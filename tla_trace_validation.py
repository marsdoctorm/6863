import os
import argparse
import platform
from subprocess import Popen
from config import TLA_DIR_PATH

# ===== Path to TLA+ jars =====
# tla_dir = "/opt/tla-nightly/toolbox"
tla_dir = TLA_DIR_PATH
tla_jar = os.path.join(tla_dir, "tla2tools.jar")
community_modules_jar = os.path.join(tla_dir, "CommunityModules-deps.jar")
if platform.system() == "Windows":
    tla_cp = f"{tla_jar};{community_modules_jar}"
else:
    tla_cp = f"{tla_jar}:{community_modules_jar}"


def run_tla(trace_spec, trace="trace.ndjson", config="conf.ndjson", dfs=False):
    os.environ["TRACE_PATH"] = trace
    os.environ["CONFIG_PATH"] = config

    if dfs:
        cmd = [
            "java",
            "-XX:+UseParallelGC",
            "-Dtlc2.tool.queue.IStateQueue=StateDeque",
            "-cp",
            tla_cp,
            "tlc2.TLC",
            trace_spec,
        ]
    else:
        cmd = [
            "java",
            "-XX:+UseParallelGC",
            "-Dtlc2.tool.impl.Tool.cdot=true",
            "-cp",
            tla_cp,
            "tlc2.TLC",
            "-dump",
            "dot,actionlabels,colorize,snapshot",
            "TD.dot",
            trace_spec,
        ]

    proc = Popen(cmd)
    proc.wait()
    proc.terminate()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="")
    parser.add_argument("spec", type=str, help="Specification file")
    parser.add_argument(
        "--trace",
        type=str,
        required=False,
        default="trace.ndjson",
        help="Trace file",
    )
    parser.add_argument(
        "--config",
        type=str,
        required=False,
        default="conf.ndjson",
        help="Config file",
    )
    parser.add_argument(
        "--dfs",
        action="store_true",
        help="use depth-first search (default: breadth-first search)",
    )

    args = parser.parse_args()
    run_tla(args.spec, args.trace, args.config, args.dfs)
