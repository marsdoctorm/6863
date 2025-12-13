package org.lbee.cloudflare;

/**
 * Message types for Cloudflare config system
 */
public class CloudflareMessage {

    public enum MessageType {
        DEPLOY, // Deploy new configuration
        ROLLBACK, // Rollback to previous config
        ACK, // Acknowledgment of successful update
        FAIL, // Update failed
        STATUS_REQUEST, // Request node status
        STATUS_RESPONSE // Response with node status
    }

    private final MessageType type;
    private final String sourceId;
    private final String destId;
    private final ConfigVersion configVersion;
    private final String metadata;

    public CloudflareMessage(MessageType type, String sourceId, String destId,
            ConfigVersion configVersion, String metadata) {
        this.type = type;
        this.sourceId = sourceId;
        this.destId = destId;
        this.configVersion = configVersion;
        this.metadata = metadata;
    }

    public MessageType getType() {
        return type;
    }

    public String getSourceId() {
        return sourceId;
    }

    public String getDestId() {
        return destId;
    }

    public ConfigVersion getConfigVersion() {
        return configVersion;
    }

    public String getMetadata() {
        return metadata;
    }

    @Override
    public String toString() {
        return String.format("%s: %s -> %s [%s] (%s)",
                type, sourceId, destId,
                configVersion != null ? configVersion : "null",
                metadata != null ? metadata : "");
    }

    /**
     * Serialize message for network transmission
     */
    public String serialize() {
        StringBuilder sb = new StringBuilder();
        sb.append(type).append("|");
        sb.append(sourceId).append("|");
        sb.append(destId).append("|");
        sb.append(configVersion != null ? configVersion.getVersion() : "null").append("|");
        sb.append(metadata != null ? metadata : "");
        return sb.toString();
    }

    /**
     * Deserialize message from network
     */
    public static CloudflareMessage deserialize(String data) {
        String[] parts = data.split("\\|");
        if (parts.length < 4) {
            throw new IllegalArgumentException("Invalid message format");
        }

        MessageType type = MessageType.valueOf(parts[0]);
        String sourceId = parts[1];
        String destId = parts[2];
        String versionStr = parts[3];
        String metadata = parts.length > 4 ? parts[4] : null;

        ConfigVersion version = null;
        if (!"null".equals(versionStr)) {
            // For deserialization, we create a basic config
            // In real implementation, this would fetch the full config
            version = new ConfigVersion(versionStr,
                    new ConfigRule(ConfigRule.RuleType.ROUTING_RULE, "default", false));
        }

        return new CloudflareMessage(type, sourceId, destId, version, metadata);
    }
}
