package org.lbee.cloudflare;

import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.trace.VirtualField;
import org.lbee.network.NetworkManager;

import java.io.IOException;
import java.util.*;

/**
 * Data Plane Node - represents an edge node executing configuration
 * Simulates Cloudflare's edge nodes that apply WAF rules, routing, etc.
 */
public class DataPlaneNode {

    public enum NodeState {
        RUNNING, UPDATING, FAILED, BLOCKED
    }

    private final String nodeId;
    private final NetworkManager networkManager;
    private final TLATracer tracer;
    private final String controlPlaneName;

    // State variables
    private NodeState state;
    private ConfigVersion currentConfig;
    private boolean isTrafficBlocked;
    private Random random;

    // Trace variables
    private final VirtualField traceNodeState;
    private final VirtualField traceNodeConfig;

    private static final int RECEIVE_TIMEOUT = 150;
    private static final double FAILURE_PROBABILITY = 0.1; // 10% chance of update failure

    public DataPlaneNode(String nodeId, NetworkManager networkManager,
            String controlPlaneName, ConfigVersion initialConfig,
            TLATracer tracer) {
        this.nodeId = nodeId;
        this.networkManager = networkManager;
        this.tracer = tracer;
        this.controlPlaneName = controlPlaneName;

        this.state = NodeState.RUNNING;
        this.currentConfig = initialConfig;
        this.isTrafficBlocked = false;
        this.random = new Random();

        // Initialize trace variables
        this.traceNodeState = tracer.getVariableTracer("nodeState[" + nodeId + "]");
        this.traceNodeConfig = tracer.getVariableTracer("nodeConfig[" + nodeId + "]");
    }

    public void run() throws IOException {
        System.out.println("[" + nodeId + "] Data plane node started");

        long startTime = System.currentTimeMillis();
        long runDuration = 5000; // Run for 5 seconds

        while (System.currentTimeMillis() - startTime < runDuration) {
            try {
                // Receive messages from control plane
                org.lbee.protocol.Message netMsg = networkManager.receive(nodeId, RECEIVE_TIMEOUT);
                String content = netMsg.getContent();

                if ("bye".equals(content)) {
                    break;
                }

                CloudflareMessage msg = CloudflareMessage.deserialize(content);
                handleMessage(msg);

            } catch (Exception e) {
                // Timeout or parse error, continue
            }

            // Periodically report status if traffic is blocked
            if (isTrafficBlocked) {
                reportStatus();
            }
        }

        System.out.println("[" + nodeId + "] Node shutting down");
        logState("shutdown");

        // Send bye to server
        networkManager.sendRaw("bye");
    }

    /**
     * Handle messages from control plane
     */
    private void handleMessage(CloudflareMessage msg) throws IOException {
        System.out.println("[" + nodeId + "] ← Received: " + msg.getType());

        switch (msg.getType()) {
            case DEPLOY:
                handleDeploy(msg);
                break;

            case ROLLBACK:
                handleRollback(msg);
                break;

            case STATUS_REQUEST:
                reportStatus();
                break;

            default:
                System.out.println("[" + nodeId + "] Unknown message type: " + msg.getType());
        }
    }

    /**
     * Handle deployment of new configuration
     */
    private void handleDeploy(CloudflareMessage msg) throws IOException {
        if (state != NodeState.RUNNING) {
            System.out.println("[" + nodeId + "] Cannot deploy: state is " + state);
            sendFail("Node not in RUNNING state");
            return;
        }

        ConfigVersion newConfig = msg.getConfigVersion();
        System.out.println("[" + nodeId + "] Applying configuration: " + newConfig);

        // Change to updating state
        state = NodeState.UPDATING;
        logState("NodeReceiveDeploy");

        // Simulate update process
        try {
            Thread.sleep(100 + random.nextInt(200)); // Simulate work

            // Check if update fails (random failure)
            if (random.nextDouble() < FAILURE_PROBABILITY) {
                System.out.println("[" + nodeId + "] ❌ Configuration update FAILED!");
                state = NodeState.FAILED;
                logState("NodeFailUpdate");
                sendFail("Random failure during update");
                return;
            }

            // Apply configuration
            ConfigVersion oldConfig = currentConfig;
            currentConfig = newConfig;
            state = NodeState.RUNNING;

            // Check for configuration issues (Failure Mode A)
            checkConfigurationValidity(oldConfig, newConfig);

            logState("NodeCompleteUpdate");

            // Send ACK
            CloudflareMessage ack = new CloudflareMessage(
                    CloudflareMessage.MessageType.ACK,
                    nodeId, controlPlaneName, newConfig,
                    "Update successful");
            org.lbee.protocol.Message netMsg = new org.lbee.protocol.Message(
                    nodeId, controlPlaneName, ack.serialize(), System.currentTimeMillis());
            networkManager.send(netMsg);
            System.out.println("[" + nodeId + "] → Sent ACK");

        } catch (InterruptedException e) {
            System.err.println("[" + nodeId + "] Interrupted during update");
            sendFail("Interrupted");
        }
    }

    /**
     * Handle rollback to previous configuration
     */
    private void handleRollback(CloudflareMessage msg) throws IOException {
        ConfigVersion rollbackConfig = msg.getConfigVersion();
        System.out.println("[" + nodeId + "] Rolling back to: " + rollbackConfig);

        try {
            Thread.sleep(50 + random.nextInt(100)); // Simulate rollback work

            currentConfig = rollbackConfig;
            state = NodeState.RUNNING;
            isTrafficBlocked = false; // Rollback should fix traffic issues

            logState("NodeReceiveRollback");

            // Send ACK
            CloudflareMessage ack = new CloudflareMessage(
                    CloudflareMessage.MessageType.ACK,
                    nodeId, controlPlaneName, rollbackConfig,
                    "Rollback successful");
            org.lbee.protocol.Message netMsg = new org.lbee.protocol.Message(
                    nodeId, controlPlaneName, ack.serialize(), System.currentTimeMillis());
            networkManager.send(netMsg);
            System.out.println("[" + nodeId + "] → Sent ROLLBACK ACK");

        } catch (InterruptedException e) {
            System.err.println("[" + nodeId + "] Interrupted during rollback");
        }
    }

    /**
     * Check if configuration is valid (Failure Mode A)
     * Configuration may be valid locally but cause global issues
     */
    private void checkConfigurationValidity(ConfigVersion oldConfig, ConfigVersion newConfig) {
        // Check 1: Does the rule block all traffic?
        if (newConfig.getRule().createsDeadZone()) {
            System.out.println("[" + nodeId + "] ⚠️  Configuration creates DEAD ZONE - blocking all traffic!");
            isTrafficBlocked = true;
            return;
        }

        // Check 2: Is new config compatible with what other nodes might have?
        // This simulates version skew issues (Failure Mode B)
        if (!newConfig.isCompatibleWith(oldConfig)) {
            System.out.println("[" + nodeId + "] ⚠️  Configuration incompatible with previous version!");
            System.out.println("[" + nodeId + "] This may cause routing issues across the network");
            isTrafficBlocked = true;
        }
    }

    /**
     * Report node status to control plane
     */
    private void reportStatus() {
        try {
            String status = isTrafficBlocked ? "TRAFFIC_BLOCKED" : "HEALTHY";
            CloudflareMessage statusMsg = new CloudflareMessage(
                    CloudflareMessage.MessageType.STATUS_RESPONSE,
                    nodeId, controlPlaneName, currentConfig,
                    status);
            org.lbee.protocol.Message netMsg = new org.lbee.protocol.Message(
                    nodeId, controlPlaneName, statusMsg.serialize(), System.currentTimeMillis());
            networkManager.send(netMsg);
            System.out.println("[" + nodeId + "] → Sent STATUS: " + status);
        } catch (IOException e) {
            System.err.println("[" + nodeId + "] Failed to send status: " + e.getMessage());
        }
    }

    /**
     * Send failure notification to control plane
     */
    private void sendFail(String reason) {
        try {
            CloudflareMessage failMsg = new CloudflareMessage(
                    CloudflareMessage.MessageType.FAIL,
                    nodeId, controlPlaneName, currentConfig,
                    reason);
            org.lbee.protocol.Message netMsg = new org.lbee.protocol.Message(
                    nodeId, controlPlaneName, failMsg.serialize(), System.currentTimeMillis());
            networkManager.send(netMsg);
            System.out.println("[" + nodeId + "] → Sent FAIL: " + reason);
        } catch (IOException e) {
            System.err.println("[" + nodeId + "] Failed to send FAIL message: " + e.getMessage());
        }
    }

    /**
     * Log current state to tracer
     */
    private void logState(String action) {
        try {
            traceNodeState.update(state.toString().toLowerCase());
            traceNodeConfig.update(currentConfig.getVersion());
            tracer.log(action + "_" + nodeId);
        } catch (IOException e) {
            System.err.println("[" + nodeId + "] Failed to log state: " + e.getMessage());
        }
    }

    public NodeState getState() {
        return state;
    }

    public boolean isTrafficBlocked() {
        return isTrafficBlocked;
    }
}
