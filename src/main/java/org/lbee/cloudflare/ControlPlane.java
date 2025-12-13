package org.lbee.cloudflare;

import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;
import org.lbee.network.NetworkManager;

import java.io.IOException;
import java.util.*;

/**
 * Control Plane - manages configuration generation and distribution
 * Simulates Cloudflare's control plane that coordinates edge nodes
 */
public class ControlPlane {

    public enum State {
        IDLE, DEPLOYING, ROLLBACK, BLOCKED
    }

    private final String name;
    private final NetworkManager networkManager;
    private final TLATracer tracer;
    private final Set<String> nodes;

    // State variables
    private State state;
    private ConfigVersion currentVersion;
    private Set<String> deployedNodes;
    private int rolloutCount;
    private boolean trafficBlocked;

    // Configuration history for rollback
    private Stack<ConfigVersion> configHistory;

    // Trace variables
    private final VirtualField traceCpState;
    private final VirtualField traceCpVersion;
    private final VirtualField traceDeployedNodes;
    private final VirtualField traceRolloutCount;
    private final VirtualField traceTrafficBlocked;

    private static final int RECEIVE_TIMEOUT = 200;
    private static final int MAX_ROLLOUTS = 5;

    public ControlPlane(String name, NetworkManager networkManager,
            Set<String> nodes, ConfigVersion initialConfig,
            TLATracer tracer) {
        this.name = name;
        this.networkManager = networkManager;
        this.tracer = tracer;
        this.nodes = nodes;

        this.state = State.IDLE;
        this.currentVersion = initialConfig;
        this.deployedNodes = new HashSet<>();
        this.rolloutCount = 0;
        this.trafficBlocked = false;
        this.configHistory = new Stack<>();
        this.configHistory.push(initialConfig);

        // Initialize trace variables
        this.traceCpState = tracer.getVariableTracer("cpState");
        this.traceCpVersion = tracer.getVariableTracer("cpVersion");
        this.traceDeployedNodes = tracer.getVariableTracer("deployedNodes");
        this.traceRolloutCount = tracer.getVariableTracer("rolloutCount");
        this.traceTrafficBlocked = tracer.getVariableTracer("trafficBlocked");
    }

    public void run() throws IOException {
        System.out.println("[CP] Control Plane started: " + name);

        // Simulate configuration lifecycle
        try {
            // Phase 1: Deploy new configuration
            ConfigVersion v2 = createConfigVersion("v2", ConfigRule.RuleType.WAF_RULE, false);
            deployConfiguration(v2);

            Thread.sleep(1000);

            // Phase 2: Deploy problematic configuration (simulates Cloudflare incident)
            ConfigVersion v3 = createConfigVersion("v3", ConfigRule.RuleType.ROUTING_RULE, true);
            System.out.println("\n[CP] ⚠️  Deploying potentially problematic configuration v3...");
            deployConfiguration(v3);

            Thread.sleep(1000);

            // Phase 3: Detect issues and attempt rollback
            if (trafficBlocked) {
                System.out.println("\n[CP] 🚨 Traffic blocked detected! Initiating rollback...");
                rollbackConfiguration();
            }

            Thread.sleep(500);

        } catch (InterruptedException e) {
            System.err.println("[CP] Interrupted: " + e.getMessage());
        }

        System.out.println("\n[CP] Control Plane shutting down");
        logState("shutdown");

        // Send bye to server
        networkManager.sendRaw("bye");
    }

    /**
     * Deploy a new configuration to all nodes
     */
    private void deployConfiguration(ConfigVersion newVersion) throws IOException {
        if (state != State.IDLE) {
            System.out.println("[CP] Cannot deploy: state is " + state);
            return;
        }

        if (rolloutCount >= MAX_ROLLOUTS) {
            System.out.println("[CP] Max rollout attempts reached!");
            return;
        }

        System.out.println("[CP] Starting deployment of " + newVersion);
        state = State.DEPLOYING;
        currentVersion = newVersion;
        deployedNodes.clear();
        rolloutCount++;
        configHistory.push(newVersion);

        logState("CPStartRollout");

        // Send deploy messages to all nodes
        for (String node : nodes) {
            CloudflareMessage msg = new CloudflareMessage(
                    CloudflareMessage.MessageType.DEPLOY,
                    name, node, newVersion, "rollout-" + rolloutCount);
            org.lbee.protocol.Message netMsg = new org.lbee.protocol.Message(
                    name, node, msg.serialize(), System.currentTimeMillis());
            networkManager.send(netMsg);
            System.out.println("[CP] → Sent DEPLOY to " + node);
        }

        // Wait for acknowledgments
        waitForAcknowledgments();
    }

    /**
     * Rollback to previous configuration
     */
    private void rollbackConfiguration() throws IOException {
        if (!canRollback()) {
            System.out.println("[CP] ❌ Rollback BLOCKED! Control plane or routing is compromised.");
            state = State.BLOCKED;
            logState("ControlPlaneBlocked");
            return;
        }

        System.out.println("[CP] Initiating rollback...");
        state = State.ROLLBACK;

        // Pop current (bad) version and get previous
        configHistory.pop();
        ConfigVersion rollbackVersion = configHistory.peek();
        currentVersion = rollbackVersion;
        deployedNodes.clear();

        logState("CPInitiateRollback");

        // Send rollback messages
        for (String node : nodes) {
            CloudflareMessage msg = new CloudflareMessage(
                    CloudflareMessage.MessageType.ROLLBACK,
                    name, node, rollbackVersion, "emergency-rollback");
            org.lbee.protocol.Message netMsg = new org.lbee.protocol.Message(
                    name, node, msg.serialize(), System.currentTimeMillis());
            networkManager.send(netMsg);
            System.out.println("[CP] → Sent ROLLBACK to " + node);
        }

        // Wait for rollback completion
        waitForAcknowledgments();

        if (deployedNodes.size() == nodes.size()) {
            System.out.println("[CP] ✅ Rollback completed successfully");
            trafficBlocked = false;
            state = State.IDLE;
        }

        logState("RollbackComplete");
    }

    /**
     * Wait for acknowledgments from nodes
     */
    private void waitForAcknowledgments() {
        long startTime = System.currentTimeMillis();
        long timeout = 3000; // 3 seconds

        while (deployedNodes.size() < nodes.size()) {
            if (System.currentTimeMillis() - startTime > timeout) {
                System.out.println("[CP] ⏰ Timeout waiting for acknowledgments");
                break;
            }

            try {
                org.lbee.protocol.Message netMsg = networkManager.receive(name, RECEIVE_TIMEOUT);
                CloudflareMessage msg = CloudflareMessage.deserialize(netMsg.getContent());

                handleMessage(msg);

            } catch (Exception e) {
                // Timeout or parse error, continue
            }
        }

        if (deployedNodes.size() == nodes.size()) {
            System.out.println("[CP] ✅ All nodes updated successfully");
            state = State.IDLE;
            logState("CPFinishDeployment");
        } else {
            System.out.println("[CP] ⚠️  Only " + deployedNodes.size() + "/" + nodes.size() + " nodes updated");
        }
    }

    /**
     * Handle messages from nodes
     */
    private void handleMessage(CloudflareMessage msg) {
        switch (msg.getType()) {
            case ACK:
                System.out.println("[CP] ← Received ACK from " + msg.getSourceId());
                deployedNodes.add(msg.getSourceId());
                logState("ReceivedAck");
                break;

            case FAIL:
                System.out.println("[CP] ← Received FAIL from " + msg.getSourceId() + ": " + msg.getMetadata());
                // In real system, might trigger rollback here
                break;

            case STATUS_RESPONSE:
                System.out.println("[CP] ← Status from " + msg.getSourceId() + ": " + msg.getMetadata());
                if ("TRAFFIC_BLOCKED".equals(msg.getMetadata())) {
                    trafficBlocked = true;
                    logState("GlobalConfigFailure");
                }
                break;

            default:
                System.out.println("[CP] ← Unknown message: " + msg);
        }
    }

    /**
     * Check if rollback is possible (Failure Mode C)
     */
    private boolean canRollback() {
        // Rollback blocked if control plane is blocked or traffic is completely blocked
        // In Cloudflare incident, rollback path was compromised by the bad config
        return state != State.BLOCKED && !isRollbackPathBlocked();
    }

    /**
     * Simulate rollback path being blocked by configuration
     */
    private boolean isRollbackPathBlocked() {
        // If traffic is blocked and current config blocks control messages
        return trafficBlocked && currentVersion.getRule().createsDeadZone();
    }

    /**
     * Create a configuration version
     */
    private ConfigVersion createConfigVersion(String version, ConfigRule.RuleType ruleType,
            boolean blocksTraffic) {
        ConfigRule rule = new ConfigRule(ruleType, "rule-" + version, blocksTraffic);
        return new ConfigVersion(version, rule);
    }

    /**
     * Log current state to tracer
     */
    private void logState(String action) {
        try {
            traceCpState.update(state.toString().toLowerCase());
            traceCpVersion.update(currentVersion.getVersion());
            traceDeployedNodes.update(new ArrayList<>(deployedNodes));
            traceRolloutCount.update(rolloutCount);
            traceTrafficBlocked.update(trafficBlocked);
            tracer.log(action);
        } catch (IOException e) {
            System.err.println("[CP] Failed to log state: " + e.getMessage());
        }
    }

    public State getState() {
        return state;
    }

    public boolean isTrafficBlocked() {
        return trafficBlocked;
    }
}
