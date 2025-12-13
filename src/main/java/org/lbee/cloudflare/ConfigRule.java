package org.lbee.cloudflare;

/**
 * Configuration rule types
 * Represents WAF rules, routing rules, TLS policies, etc.
 */
public class ConfigRule {

    public enum RuleType {
        WAF_RULE, // Web Application Firewall rules
        ROUTING_RULE, // Traffic routing configuration
        TLS_POLICY, // TLS/SSL configuration
        RATE_LIMIT, // Rate limiting rules
        DNS_RULE // DNS configuration
    }

    private final RuleType ruleType;
    private final String ruleContent;
    private final boolean blockAllTraffic; // Simulates misconfiguration

    public ConfigRule(RuleType ruleType, String ruleContent, boolean blockAllTraffic) {
        this.ruleType = ruleType;
        this.ruleContent = ruleContent;
        this.blockAllTraffic = blockAllTraffic;
    }

    public RuleType getRuleType() {
        return ruleType;
    }

    public String getRuleContent() {
        return ruleContent;
    }

    public boolean isBlockAllTraffic() {
        return blockAllTraffic;
    }

    /**
     * Validate rule syntax (always passes - local validation)
     */
    public boolean isValidSyntax() {
        return ruleContent != null && !ruleContent.isEmpty();
    }

    /**
     * Check if rule creates a "dead zone" or blocks all traffic
     * This simulates Failure Mode A
     */
    public boolean createsDeadZone() {
        return blockAllTraffic;
    }

    @Override
    public String toString() {
        return ruleType + ":" + (blockAllTraffic ? "BLOCKS_ALL" : "OK");
    }
}
