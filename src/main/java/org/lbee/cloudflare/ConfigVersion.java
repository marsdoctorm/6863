package org.lbee.cloudflare;

/**
 * Configuration version in the Cloudflare-style system
 */
public class ConfigVersion {
    private final String version;
    private final ConfigRule rule;

    public ConfigVersion(String version, ConfigRule rule) {
        this.version = version;
        this.rule = rule;
    }

    public String getVersion() {
        return version;
    }

    public ConfigRule getRule() {
        return rule;
    }

    /**
     * Check if this config is compatible with another config
     * Simulates Failure Mode A: local validity but global incompatibility
     */
    public boolean isCompatibleWith(ConfigVersion other) {
        if (other == null)
            return true;

        // Simulate specific incompatible combinations
        // e.g., v2 with certain rules is incompatible with v3
        if (this.version.equals("v2") && other.version.equals("v3")) {
            return this.rule.getRuleType() != other.rule.getRuleType();
        }

        return true;
    }

    @Override
    public String toString() {
        return version + "(" + rule + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (!(o instanceof ConfigVersion))
            return false;
        ConfigVersion that = (ConfigVersion) o;
        return version.equals(that.version);
    }

    @Override
    public int hashCode() {
        return version.hashCode();
    }
}
