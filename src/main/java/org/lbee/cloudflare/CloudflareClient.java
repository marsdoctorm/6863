package org.lbee.cloudflare;

import org.lbee.instrumentation.clock.ClockException;
import org.lbee.instrumentation.clock.ClockFactory;
import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.network.NetworkManager;

import java.io.IOException;
import java.net.Socket;
import java.util.HashSet;
import java.util.Set;

/**
 * Cloudflare Configuration System Client
 * 
 * Usage:
 * java CloudflareClient <hostname> <port> <type> <name>
 * [controlplane|node1,node2,...]
 * 
 * Examples:
 * # Start control plane
 * java CloudflareClient localhost 8080 cp control-plane n1,n2,n3,n4
 * 
 * # Start data plane nodes
 * java CloudflareClient localhost 8080 node n1 control-plane
 * java CloudflareClient localhost 8080 node n2 control-plane
 * java CloudflareClient localhost 8080 node n3 control-plane
 * java CloudflareClient localhost 8080 node n4 control-plane
 */
public class CloudflareClient {

    public static void main(String[] args) throws IOException, ClockException {

        if (args.length < 5) {
            System.out.println("Usage: hostname port type={cp,node} name {cpname|node1,node2,...}");
            System.out.println("");
            System.out.println("Examples:");
            System.out.println("  Control Plane: hostname port cp control-plane n1,n2,n3,n4");
            System.out.println("  Data Node:     hostname port node n1 control-plane");
            return;
        }

        final String hostname = args[0];
        final int port = Integer.parseInt(args[1]);
        final String type = args[2];
        final String name = args[3];
        final String otherNames = args[4];

        try (Socket socket = new Socket(hostname, port)) {
            NetworkManager networkManager = new NetworkManager(socket);

            // Create initial safe configuration
            ConfigVersion initialConfig = new ConfigVersion("v1",
                    new ConfigRule(ConfigRule.RuleType.ROUTING_RULE, "initial-safe-config", false));

            // Initialize tracer
            TLATracer tracer = TLATracer.getTracer(name + ".cloudflare.ndjson",
                    ClockFactory.getClock(ClockFactory.FILE, "cloudflare.clock"));

            switch (type.toLowerCase()) {
                case "cp":
                case "controlplane":
                    // Parse node names
                    Set<String> nodes = new HashSet<>();
                    for (String nodeName : otherNames.split(",")) {
                        nodes.add(nodeName.trim());
                    }

                    System.out.println("🌐 Starting Control Plane: " + name);
                    System.out.println("   Managing nodes: " + nodes);

                    ControlPlane controlPlane = new ControlPlane(
                            name, networkManager, nodes, initialConfig, tracer);
                    controlPlane.run();

                    // Print summary
                    System.out.println("\n" + "=".repeat(60));
                    System.out.println("Control Plane Summary:");
                    System.out.println("  Final State: " + controlPlane.getState());
                    System.out.println("  Traffic Blocked: " + controlPlane.isTrafficBlocked());
                    System.out.println("=".repeat(60));
                    break;

                case "node":
                case "dataplane":
                    String cpName = otherNames.trim();

                    System.out.println("📍 Starting Data Plane Node: " + name);
                    System.out.println("   Control Plane: " + cpName);

                    DataPlaneNode node = new DataPlaneNode(
                            name, networkManager, cpName, initialConfig, tracer);
                    node.run();

                    // Print summary
                    System.out.println("\n" + "=".repeat(60));
                    System.out.println("Node Summary:");
                    System.out.println("  Final State: " + node.getState());
                    System.out.println("  Traffic Blocked: " + node.isTrafficBlocked());
                    System.out.println("=".repeat(60));
                    break;

                default:
                    System.out.println("Invalid type: " + type);
                    System.out.println("Expected: cp or node");
                    return;
            }

        } catch (Exception ex) {
            System.err.println("Error: " + ex.getMessage());
            ex.printStackTrace();
        }
    }
}
