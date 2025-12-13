import contextlib
import os
import argparse
import platform
import subprocess
import ndjson
import time
import signal
from subprocess import Popen

jar_name = "CloudflareConfig-1.0.0-jar-with-dependencies.jar"


def read_json(filename):
    with open(filename) as f:
        return ndjson.load(f)


def free_ports():
    ports = [6869, 6666]
    for port in ports:
        if platform.system() == "Windows":
            with contextlib.suppress(subprocess.CalledProcessError):
                output = subprocess.check_output(
                    f"netstat -ano | findstr :{port}", shell=True
                ).decode()
                for line in output.splitlines():
                    if "LISTENING" in line:
                        pid = line.strip().split()[-1]
                        subprocess.run(
                            f"taskkill /F /PID {pid}",
                            shell=True,
                            stdout=subprocess.DEVNULL,
                            stderr=subprocess.DEVNULL,
                        )
        else:
            os.system(f"lsof -ti:{port} | xargs kill -9 >/dev/null 2>&1")


def run(nodes, cp):
    free_ports()

    print("--- Run server ---")
    server_process = Popen(
        [
            "java",
            "-cp",
            f"target/{jar_name}",
            "org.lbee.network.Server",
            "6869",
            "unordered",
        ]
    )

    print("--- Run clock server ---")
    clock_process = Popen(
        [
            "java",
            "-cp",
            f"target/{jar_name}",
            "org.lbee.instrumentation.clock.ServerClock",
            "6666",
        ]
    )

    # Wait for server to start
    time.sleep(2)

    print("--- Run Data Plane Nodes ---")
    node_processes = []
    for node in nodes:
        args = [
            "java",
            "-cp",
            f"target/{jar_name}",
            "org.lbee.cloudflare.CloudflareClient",
            "localhost",
            "6869",
            "node",
            f"{node}",
            f"{cp}",
        ]
        node_process = Popen(args)
        node_processes.append(node_process)
        time.sleep(0.5)  # Stagger node startup

    print("--- Run Control Plane ---")
    node_list = ",".join(nodes)
    cp_args = [
        "java",
        "-cp",
        f"target/{jar_name}",
        "org.lbee.cloudflare.CloudflareClient",
        "localhost",
        "6869",
        "cp",
        f"{cp}",
        node_list,
    ]
    cp_process = Popen(cp_args)

    # Wait for control plane to finish
    cp_process.wait()

    # Wait for nodes to finish
    for node_process in node_processes:
        node_process.wait()

    # Cleanup
    print("--- Cleanup ---")
    cp_process.terminate()
    for node_process in node_processes:
        node_process.terminate()

    if platform.system() == "Windows":
        server_process.terminate()
        clock_process.terminate()
    else:
        os.kill(server_process.pid, signal.SIGINT)
        os.kill(clock_process.pid, signal.SIGINT)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run Cloudflare config system")
    parser.add_argument(
        "--config",
        type=str,
        required=False,
        default="conf-cloudflare.ndjson",
        help="Config file",
    )
    args = parser.parse_args()

    # Read config and run
    config = read_json(args.config)
    nodes = config[0]["Node"]
    cp = config[1]["CP"][0]

    print(
        f"Starting Cloudflare system with {len(nodes)} nodes and control plane '{cp}'"
    )
    run(nodes, cp)
