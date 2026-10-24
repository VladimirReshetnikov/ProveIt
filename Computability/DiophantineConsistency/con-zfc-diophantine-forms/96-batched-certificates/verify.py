#!/usr/bin/env python3
"""Audit the complete delivered package and optionally rebuild its primary data."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def verify_manifest():
    data = read_json(ROOT / "MANIFEST.json")
    require(data["algorithm"] == "sha256", "manifest algorithm")
    checked = set()
    for entry in data["files"]:
        name = entry["path"]
        relative = Path(name)
        require(not relative.is_absolute() and ".." not in relative.parts,
                "unsafe manifest path")
        require(name not in checked, "duplicate manifest path")
        payload = (ROOT / relative).read_bytes()
        require(len(payload) == entry["bytes"], "byte length: " + name)
        require(hashlib.sha256(payload).hexdigest() == entry["sha256"],
                "SHA-256: " + name)
        checked.add(name)
    return {"status": "PASS", "files": len(checked)}


def run_component(script, options=()):
    command = [sys.executable]
    if not __debug__:
        command.append("-O")
    command.extend([str(ROOT / script), *options])
    completed = subprocess.run(command, cwd=ROOT, check=True,
                               capture_output=True, text=True)
    result = json.loads(completed.stdout)
    require(result["status"] == "PASS", "component failed: " + script)
    return result


def check_integration():
    natural_parent = ROOT / "direct/output/shared_frame/equation.json"
    integer_parent = ROOT / "integer/source/parent_natural.json"
    require(natural_parent.read_bytes() == integer_parent.read_bytes(),
            "integer parent differs from the delivered shared frame")
    release = read_json(ROOT / "RELEASE.json")
    checked = []
    for entry in release["quartics"]:
        packet = read_json(ROOT / entry["path"])
        metrics = packet["metrics"]
        require(packet["domain"] == entry["domain"], "domain: " + entry["path"])
        for key, expected in entry["metrics"].items():
            require(metrics[key] == expected, "release metric: " + key)
        require(len(packet["variables"]) == entry["metrics"]["variables"],
                "coordinate list dimension")
        checked.append(entry["path"])
    norm = read_json(ROOT / "guard13/equation.json")
    require(norm["variable_count"] == 13 and norm["operations"] == 195,
            "thirteen-integer release metrics")
    return {"status": "PASS", "shared_parent_byte_identity": True,
            "quartic_metric_bindings": checked}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--manifest-only", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    require(not (args.rebuild and args.manifest_only),
            "--rebuild and --manifest-only are mutually exclusive")
    result = {"status": "PASS", "python_optimized": not __debug__,
              "manifest": verify_manifest()}
    if not args.manifest_only:
        result["integration"] = check_integration()
        options = ["--rebuild"] if args.rebuild else []
        result["direct"] = run_component("direct/verify.py", options)
        result["integer"] = run_component("integer/verify_integer.py", options)
        result["guard13"] = run_component("guard13/verify_reanchored.py")
        result["scope"] = (
            "Exact finite algebra, literal reconstruction, source authentication, "
            "and integration checks. The unbounded consistency equivalences are "
            "mathematical theorems, not consequences of finite tests.")
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        args.receipt.write_text(payload)
    print(payload)


if __name__ == "__main__":
    main()
