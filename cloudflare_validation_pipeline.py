#!/usr/bin/env python3
"""
Cloudflare Configuration System - Trace Validation Pipeline

Similar to trace_validation_pipeline.py but for Cloudflare system.
Performs: build -> run -> merge traces -> validate with TLC
"""

import os
import argparse
from pathlib import Path
import subprocess
import sys
import re
import signal


def clean_traces():
    """Clean old trace files"""
    print("=== Cleaning old trace files ===")
    patterns = ["*.cloudflare.ndjson", "cloudflare.clock"]
    for pattern in patterns:
        if os.name == "nt":  # Windows
            subprocess.run(f"del /Q {pattern}", shell=True, stderr=subprocess.DEVNULL)
        else:  # Unix-like
            subprocess.run(f"rm -f {pattern}", shell=True, stderr=subprocess.DEVNULL)
    print("✓ Cleaned old traces\n")


def compile_project():
    """Compile the Java project"""
    print("=== Compiling project ===")
    result = subprocess.run(
        ["mvn", "clean", "package"],
        capture_output=True,
        text=True,
        shell=True,
    )
    print(result.stdout)
    if result.returncode != 0:
        print("✗ Compilation failed!")
        print(result.stderr)
        return False
    print("✓ Compilation successful\n")
    return True


def kill_jar_lockers(
    jar_name="target/CloudflareConfig-1.0.0-jar-with-dependencies.jar",
):
    """Kill processes that reference the built jar to avoid locking during mvn clean."""
    print("=== Killing processes locking jar ===")
    pids = []
    base = os.path.basename(jar_name)
    try:
        if os.name == "nt":
            # Use PowerShell to find processes whose command line contains the jar name
            cmd = [
                "powershell",
                "-Command",
                f"Get-CimInstance Win32_Process | Where-Object {{$_.CommandLine -match '{base}'}} | Select-Object -ExpandProperty ProcessId",
            ]
            out = subprocess.check_output(cmd, stderr=subprocess.DEVNULL, text=True)
            pids = [int(s) for s in re.findall(r"\d+", out)]
            for pid in pids:
                subprocess.run(
                    ["taskkill", "/PID", str(pid), "/F"],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
        else:
            # Try pgrep to find java processes matching the jar
            try:
                out = subprocess.check_output(
                    ["pgrep", "-f", base], stderr=subprocess.DEVNULL, text=True
                )
                pids = [int(s) for s in out.split() if s.strip()]
                for pid in pids:
                    os.kill(pid, signal.SIGKILL)
            except subprocess.CalledProcessError:
                # pgrep found nothing
                pids = []
    except Exception as e:
        print(f"Warning: could not determine/kill locking processes: {e}")

    if pids:
        print(f"Killed processes: {pids}")
    else:
        print("No locking processes found.")


def run_implementation(config_file):
    """Run the Cloudflare implementation"""
    print("=== Running Cloudflare implementation ===")
    result = subprocess.run(
        ["python", "run_cloudflare.py", "--config", config_file],
        capture_output=False,
    )
    if result.returncode != 0:
        print("✗ Execution failed!")
        return False
    print("✓ Execution complete\n")
    return True


def merge_traces(config_file, output_file="trace-cloudflare.ndjson"):
    """Merge trace files from all components"""
    print("=== Merging trace files ===")

    # Read config to get process names
    import ndjson

    with open(config_file) as f:
        config = ndjson.load(f)

    nodes = config[0]["Node"]
    cp = config[1]["CP"][0]

    # Build list of trace files
    trace_files = [f"{cp}.cloudflare.ndjson"]
    for node in nodes:
        trace_files.append(f"{node}.cloudflare.ndjson")

    # Check if files exist
    existing_files = [f for f in trace_files if os.path.exists(f)]
    if not existing_files:
        print("✗ No trace files found!")
        return False

    print(f"Found {len(existing_files)} trace files:")
    for f in existing_files:
        print(f"  - {f}")

    # Merge traces
    args = ["python", "trace_merger.py", "--sort", "True", "--out", output_file]
    args.extend(existing_files)

    result = subprocess.run(args, capture_output=True, text=True)
    if result.returncode != 0:
        print("✗ Merge failed!")
        print(result.stderr)
        return False

    print(f"✓ Traces merged into {output_file}\n")
    return True


def validate_trace(
    trace_file="trace-cloudflare.ndjson", config_file="conf-cloudflare.ndjson"
):
    """Validate trace with TLA+"""
    print("=== Validating trace with TLA+ ===")
    spec_file = Path(__file__).parent / "spec" / "CloudflareTrace.tla"
    if not os.path.exists(spec_file):
        print(f"✗ Spec file not found: {spec_file}")
        return False

    result = subprocess.run(
        [
            "python",
            "tla_trace_validation.py",
            spec_file,
            "--trace",
            trace_file,
            "--config",
            config_file,
        ],
        capture_output=False,
    )

    if result.returncode != 0:
        print("✗ Trace validation failed!")
        return False

    print("✓ Trace validation successful\n")
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Cloudflare Configuration System - Trace Validation Pipeline"
    )
    parser.add_argument(
        "-c",
        "--clean",
        action="store_true",
        help="Clean old traces before running",
    )
    parser.add_argument(
        "--config",
        type=str,
        default="conf-cloudflare.ndjson",
        help="Configuration file (default: conf-cloudflare.ndjson)",
    )
    parser.add_argument(
        "--skip-compile",
        action="store_true",
        help="Skip compilation step",
    )
    parser.add_argument(
        "--skip-run",
        action="store_true",
        help="Skip execution step (use existing traces)",
    )
    parser.add_argument(
        "--skip-validate",
        action="store_true",
        help="Skip TLA+ validation step",
    )
    parser.add_argument(
        "--trace-output",
        type=str,
        default="trace-cloudflare.ndjson",
        help="Output trace file name (default: trace-cloudflare.ndjson)",
    )

    args = parser.parse_args()

    print("=" * 60)
    print("Cloudflare Configuration System - Trace Validation Pipeline")
    print("=" * 60)
    print()

    # Step 1: Clean
    if args.clean:
        clean_traces()

    # Step 2: Compile
    if not args.skip_compile:
        # Kill any lingering processes that may lock the built jar before compiling
        kill_jar_lockers()
        if not compile_project():
            sys.exit(1)

    # Step 3: Run
    if not args.skip_run:
        if not run_implementation(args.config):
            sys.exit(1)

    # Step 4: Merge
    if not merge_traces(args.config, args.trace_output):
        sys.exit(1)

    # Step 5: Validate
    if not args.skip_validate:
        if not validate_trace(args.trace_output, args.config):
            sys.exit(1)

    print("=" * 60)
    print("✓ All steps completed successfully!")
    print("=" * 60)


if __name__ == "__main__":
    main()
