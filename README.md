# Model-Based Trace Validation: Amazon Two-Phase Commit (v3)

## Project Overview
This project is developed for **CSEE 6863: Formal Verification of Software**. It implements a trace-based validation pipeline for a distributed system modeled after the Amazon Two-Phase Commit protocol.

The core objective is to verify the correctness of a Java implementation against a formal TLA+ specification. This repository specifically focuses on the **v3 iteration** of the Amazon specification, which includes enhanced logic and safety properties compared to previous versions.

## Key Features
- **Formal Specification (TLA+):** A rigorous model of the Amazon Two-Phase Commit protocol (v3).
- **Implementation (Java):** A concrete implementation of the system logic located in `src/main/java`.
- **Trace Validation:** A Python-based pipeline that:
  1. Executes the Java implementation to generate execution traces.
  2. Parses these traces and maps them to TLA+ states.
  3. Uses the TLA+ model checker to verify that every step in the implementation trace is allowed by the formal specification.

## Project Structure

The file structure is organized as follows:

```text
├── amazon/
│   └── spec/
│       └── v3/             # The core TLA+ specifications (Modified v3)
├── src/main/java/          # Java implementation of the protocol
├── target/                 # Maven build output
├── _impl.log               # Log file from the implementation run
├── _validate.log           # Log file from the validation process
├── cloudflare_validation_pipeline.py  # Main pipeline script (Validation Logic)
├── tla_trace_validation.py # Core logic for checking traces against TLA+ spec
├── trace_merger.py         # Utility to merge distributed traces
├── trace.schema.json       # JSON schema defining the trace format
├── pom.xml                 # Maven configuration for the Java project
└── README.md


Prerequisites
Before running the validation pipeline, ensure you have the following installed:

Java JDK 11+ (for running the implementation and Maven).

Apache Maven (for building the Java project).

Python 3.8+ (for the validation scripts).

TLA+ Tools: Ensure the TLA+ command-line tools (tla2tools.jar) are accessible or configured within the script paths.


Setup & Installation
Clone the repository:

Bash

git clone <repository-url>
cd <repository-folder>
Set up the Python environment: It is recommended to use a virtual environment.

Bash

python -m venv .venv
source .venv/bin/activate  # On Windows use: .venv\Scripts\activate
pip install -r requirements.txt  # If a requirements file exists, otherwise install dependencies manually
Build the Java Implementation:

Bash

mvn clean package
Usage
1. Configuration
Ensure that the amazon/spec/v3 folder contains the correct .tla and .cfg files for the v3 model.

2. Running the Validation Pipeline
To execute the full verification cycle (Run Implementation -> Generate Trace -> Validate against Spec), run the pipeline script:

Bash

# Note: Ensure the script points to the Amazon v3 spec path
python cloudflare_validation_pipeline.py
(Note: Although named cloudflare_... due to the base template, this script has been configured to validate the Amazon v3 specification.)

3. Interpreting Results
Success: If the implementation conforms to the spec, the script will output a success message indicating no violations were found.

Failure: Check _validate.log for details on where the trace diverged from the allowed TLA+ states.

Version Details (v3)
The v3 specification introduced the following improvements:

Refined state transitions for the commit phase.

Handling of specific edge cases in the Two-Phase protocol.



Acknowledgments
