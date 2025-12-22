# Formal Verification of Distributed Systems: Cloudflare & Amazon

## 1. Project Overview

This project serves as a comprehensive study in **Model-Based Trace Validation** for distributed systems, developed for **CSEE 6863**.

The repository delivers **two major contributions**, implementing and verifying distinct distributed protocols:

1.  **Cloudflare System (Logical Clocks):**

    - Implements a distributed system relying on logical clocks.
    - Validates the causal ordering of events against a formal TLA+ model.
    - Demonstrates the correctness of trace merging algorithms.

2.  **Amazon Two-Phase Commit (v3 Iteration):**
    - Implements the Amazon Two-Phase Commit (2PC) protocol with enhanced logic (v3).
    - Verifies safety properties (Atomicity, Consistency) under failure scenarios.
    - Validates the Java implementation against a modified, robust TLA+ specification (`v3`).

## 2. Repository Structure

```text
├── amazon/
│   └── spec/
│       └── v3/                # TLA+ Specifications for Amazon (Version 3)
├── src/main/java/             # Java Source Code (Contains both Cloudflare & Amazon logic)
├── target/                    # Compiled Java Artifacts
├── .venv/                     # Python Virtual Environment
├── run_cloudflare.py          # Execution Script: Cloudflare System
├── cloudflare_validation_pipeline.py # Execution Script: Validation Pipeline (Amazon/Generic)
├── tla_trace_validation.py    # Core Engine: Matches Traces <-> TLA+ States
├── trace_merger.py            # Utility: Merges distributed node logs into a linear trace
├── trace.schema.json          # JSON Schema for trace validation
├── pom.xml                    # Maven Project Configuration
├── _impl.log                  # [Log] Execution output from Java
└── _validate.log              # [Log] Validation results from TLA+ Model Checker
3. Environment Setup
3.1 Prerequisites
Ensure the following tools are installed and accessible in your system PATH. Note: these tools are not bundled with the repository and must be installed separately.

- Java JDK 11+ (not included)

    - Verify: `java -version`
    - Windows (Chocolatey): `choco install openjdk11 -y` or install from AdoptOpenJDK/Temurin installers.
    - Ubuntu/Debian: `sudo apt update && sudo apt install -y openjdk-11-jdk`
    - macOS (Homebrew): `brew install openjdk@11`

- Apache Maven (not included)

    - Verify: `mvn -version`
    - Windows (Chocolatey): `choco install maven -y`
    - Ubuntu/Debian: `sudo apt update && sudo apt install -y maven`
    - macOS (Homebrew): `brew install maven`

- Python 3.8+ (for the helper/validation scripts)

    - Verify: `python --version` or `python3 --version`

- TLA+ Tools (`tla2tools.jar`) — required for model checking and trace validation. This JAR is not included in the repo; download the TLA+ tools bundle from the TLA+ website and place `tla2tools.jar` somewhere on your PATH or provide its path to the Python scripts.

After installing, confirm the tools are available by running `java -version` and `mvn -version` in your shell.
```

## 3. Installation

Clone the repository:

```bash
git clone https://github.com/marsdoctorm/6863
cd 6863
```

Dependencies and Installation (recommended using a virtual environment):

Windows (PowerShell):

```powershell
python -m venv .venv
.\.venv\Scripts\Activate.ps1
pip install -r requirements.txt
```

Linux / macOS:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

you can install the minimal dependency manually:

```bash
pip install ndjson
```

Build the Java code (rebuild after modifying Java sources):

```bash
mvn clean package
```

Verification: ensure the `target/` directory is generated successfully.

## 4. Execution Guide: Cloudflare System

This module validates the Logical Clock implementation.

Command:

```bash
python cloudflare_validation_pipeline.py
```

Workflow:

Compiles/Runs the Cloudflare Java implementation.

Generates execution traces reflecting logical clock updates.

Validates that the trace respects the causal ordering defined in cloudflare.clock.

This is done by merging logs and checking against the TLA+ model.

## 5. Execution Guide: Amazon Two-Phase Commit (v3)

This module validates the Amazon 2PC implementation against the v3 TLA+ specification.

Command:

```bash
cd "/mnt/d/6863formal vertification/TwoPhase"

# Good：UseBad = FALSE
java -XX:+UseParallelGC -cp "$TLA_JAR" tlc2.TLC \
  -config amazon/spec/v3/AmazonV3Good.cfg \
  amazon/spec/v3/AmazonAZPoolV3.tla

# Bad：UseBad = TRUE
java -XX:+UseParallelGC -cp "$TLA_JAR" tlc2.TLC \
  -config amazon/spec/v3/AmazonV3Bad.cfg \
  amazon/spec/v3/AmazonAZPoolV3.tla
```




