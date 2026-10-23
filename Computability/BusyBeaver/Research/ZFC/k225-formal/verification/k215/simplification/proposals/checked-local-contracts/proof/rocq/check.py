#!/usr/bin/env python3
"""Compile the isolated Rocq transport pilot against exact pinned source bytes."""
from __future__ import annotations
import argparse
import hashlib
import json
import shutil
import subprocess
import time
from pathlib import Path

BASE = "Computability/BusyBeaver/Research/ZFC/k225-formal/"
DEPS = [
    (BASE + "verification/k215/simplification/proposals/checked-affine-core/affine_core/source_deps/K230/RM.v",
     "deps/K230/RM.v", "214a6016420e48f4432565ce97f1a27d07ac42642f8ed170d5d0ee02c5994ee8"),
    (BASE + "rocq/rocq-extension/coq/218/Dag219.v", "deps/PilotOld/Dag219.v",
     "a12b21cb4e216049ed4bf657c9de1ee1ca467e47f05deccee32cc76a96927445"),
    (BASE + "rocq/rocq-extension/coq/215/DagPerm.v", "deps/PilotNew/DagPerm.v",
     "ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1"),
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--repo", type=Path,
                        help="Read the three pinned dependencies from a ProveIt checkout")
    inputs.add_argument("--deps-root", type=Path,
                        help="Read vendored K230/, PilotOld/ and PilotNew/ dependency directories")
    parser.add_argument("--coqc", required=True)
    parser.add_argument("--coqchk", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    root, out = Path(__file__).resolve().parent, args.out.resolve()
    if out.exists() and any(out.iterdir()):
        raise SystemExit("Output directory must be new or empty; do not reuse stale objects")
    out.mkdir(parents=True, exist_ok=True)
    result = {"status": "STARTED", "scope": "Focused finite-footprint transport pilot; not the K215 endpoint",
              "source_mode": "repository" if args.repo else "vendored",
              "sources": [], "invocations": []}
    def invoke(command: list[str], name: str) -> subprocess.CompletedProcess:
        start = time.monotonic()
        proc = subprocess.run(command, cwd=out, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / (name + ".log")).write_text(proc.stdout)
        result["invocations"].append({"name": name, "command": command,
                                      "exit_code": proc.returncode, "seconds": time.monotonic() - start,
                                      "log_sha256": sha(out / (name + ".log"))})
        if proc.returncode:
            raise RuntimeError(f"{name} failed; see log")
        return proc
    try:
        version = invoke([args.coqc, "--version"], "toolchain")
        result["toolchain"] = version.stdout.strip()
        for source, target, expected in DEPS:
            src = (args.repo.resolve() / source if args.repo else
                   args.deps_root.resolve() / Path(target).relative_to("deps"))
            if sha(src) != expected:
                raise ValueError(f"Source hash differs from reviewed baseline: {source}")
            dst = out / target
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
            result["sources"].append({"origin": source, "input_path": str(src),
                                      "compiled_path": target, "sha256": expected})
        for name in ("RunTransfer.v", "Footprint215.v"):
            shutil.copyfile(root / name, out / name)
            result["sources"].append({"origin": name, "compiled_path": name, "sha256": sha(out / name)})
        flags = ["-Q", "deps/K230", "K230", "-Q", "deps/PilotOld", "PilotOld", "-Q", "deps/PilotNew", "PilotNew"]
        for source in result["sources"]:
            name = source["compiled_path"]
            proc = invoke([args.coqc, *flags, name], name.replace("/", "_")[:-2])
            source["object_sha256"] = sha(out / Path(name).with_suffix(".vo"))
            source["closed_reports"] = proc.stdout.count("Closed under the global context")
        if result["sources"][-2]["closed_reports"] != 3 or result["sources"][-1]["closed_reports"] != 2:
            raise RuntimeError("Unexpected assumption reports: review logs before accepting")
        invoke([args.coqchk, "-silent", *flags, "Footprint215"], "coqchk")
        result["status"] = "PASS_FOCUSED_KERNEL"
    except Exception as exc:
        result["status"] = "FAIL"
        result["error"] = str(exc)
        raise
    finally:
        (out / "receipt.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "toolchain": result["toolchain"], "modules": len(result["sources"])}))


if __name__ == "__main__":
    main()
