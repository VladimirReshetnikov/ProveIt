#!/usr/bin/env python3
"""Reproduce PA194AX11QH5. Standard library; run without -O.

The default replays both universal physical executors. --quick skips those
two expensive checks and still reconstructs the table and full blank startup.
Nothing in the delivered evidence is modified; new evidence uses a temporary
directory, unless --output requests a final JSON receipt at a separate path.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
PYTHON = sys.executable
EXPECTED_SHA = "f7f52501055ff4fe47aab51acc6536adf3823afca4016a670c67b2c592ed4b02"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def integrity():
    manifest = ROOT / "SHA256SUMS"
    require(manifest.exists(), "SHA256SUMS is missing")
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split("  ", 1)
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT), "Manifest path escapes archive")
        require(path.is_file() and digest(path) == expected, "Integrity failure: " + name)
        count += 1
    return count


def table(path):
    rows = {}
    for line in path.read_text().splitlines():
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        require((q, b) not in rows, "Duplicate transition")
        require(b in (0, 1) and w in (0, 1) and d in ("L", "R"), "Invalid transition")
        rows[q, b] = (w, d, t)
    return rows


def structural(machine):
    dense = table(machine / "machine.tm")
    native = table(machine / "machine.native.tm")
    labels = json.loads((machine / "labels.json").read_text())
    require(set(dense) == {(q, b) for q in range(194) for b in (0, 1)}, "Incomplete dense table")
    require(all(0 <= t <= 194 for w, d, t in dense.values()), "Unknown successor")
    require(len(labels) == len(set(labels)) == 195, "Invalid label bijection")
    require(labels[0] == 74 and labels[194] == 254, "Start/halt labels changed")
    require({(labels[q], b): (w, d, labels[t]) for (q, b), (w, d, t) in dense.items()} == native,
            "Native/dense tables are not conjugate")
    reach = {0}
    queue = [0]
    for q in queue:
        for b in (0, 1):
            t = dense[q, b][2]
            if t != 194 and t not in reach:
                reach.add(t)
                queue.append(t)
    require(len(reach) == 194, "Unreachable control-graph component")
    old = table(ROOT / "construction/inputs/qh5/machine/machine.native.tm")
    changes = [(k, old.get(k), native.get(k)) for k in sorted(set(old) | set(native))
               if old.get(k) != native.get(k)]
    require(changes == [((2066, 1), (0, "L", 302), (1, "R", 19))], "Unexpected parent-table change")
    source_file = ROOT / "verification/reference/source_language.py"
    spec = importlib.util.spec_from_file_location("independent_source_language", source_file)
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    names = {"inc": "CI", "dec": "CD", "breakTo": "CB", "continueTo": "CC", "halt": "CH"}
    mapped = [[p, names[op], a] for p, op, a in json.loads((machine / "sites.json").read_text())]
    graph, _ = source.graph_arithmetic(mapped)
    require(graph == source.graph_intervals(mapped), "Independent source resolvers differ")
    effects = {"identity": "jump", "increment": "inc", "decrement": "dec", "halt": "halt"}
    instructions = [[effects[e[0]]] + e[1:] + targets for e, targets in graph]
    require(instructions == json.loads((machine / "instructions.json").read_text()), "Source graph mismatch")
    return {"working_states": 194, "rows": 388, "all_controls_graph_reachable": True,
            "dense_native_conjugacy": True, "source_resolvers_agree": True,
            "exact_single_parent_row_change": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true")
    parser.add_argument("--output", type=Path, help="Optional receipt; does not replace frozen evidence")
    args = parser.parse_args()
    require(__debug__ and not sys.flags.optimize, "Assertions must be enabled; do not use -O")
    require(sys.version_info >= (3, 10), "Python 3.10 or newer is required")
    start = time.monotonic()
    result = {"status": "RUNNING", "mode": "quick" if args.quick else "full",
              "proof_assistant_endpoint": False}
    print("Checking delivered-file hashes...", flush=True)
    result["manifest_files_checked"] = integrity()
    require(digest(ROOT / "machine/machine.tm") == EXPECTED_SHA, "Wrong target table")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    with tempfile.TemporaryDirectory(prefix="pa194-verify-") as temp:
        work = Path(temp)
        def run(label, command):
            print(label + "...", flush=True)
            completed = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                                       text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (work / (label.replace(" ", "_") + ".log")).write_text(completed.stdout)
            if completed.returncode:
                print(completed.stdout, file=sys.stderr)
                raise RuntimeError(label + " failed")
            return completed.stdout

        machine = work / "machine"
        command = [PYTHON, "-B", ROOT / "construction/build.py", "--output", machine]
        if args.quick:
            command.append("--quick")
        run("Reconstructing table and checking startup" if args.quick else
            "Reconstructing and replaying primary physical contracts", command)
        core = ["grammar.json", "nodes.json", "folds.json", "sites.json", "instructions.json",
                "local_folds.json", "raw.native.tm", "machine.native.tm", "machine.tm", "labels.json"]
        for name in core:
            require((machine / name).read_bytes() == (ROOT / "machine" / name).read_bytes(),
                    "Reconstruction differs: " + name)
        current = json.loads((machine / "receipt.json").read_text())
        frozen = json.loads((ROOT / "machine/receipt.json").read_text())
        for key in frozen:
            if key != "runtime" or not args.quick:
                require(current[key] == frozen[key], "Reconstruction receipt differs: " + key)
        result["construction"] = current
        result["structural"] = structural(machine)

        checks = [
            ("source_splice", ROOT / "verification/check_ax11qh5_splice.py",
             ["--old", ROOT / "construction/inputs/qh5/machine", "--new", machine]),
            ("command_identities", ROOT / "verification/ax11qh5_commands.py", []),
            ("integer_stack_audit", ROOT / "verification/adversarial_stack_audit.py", []),
            ("inherited_emitter", ROOT / "verification/check_inherited_emitter.py", []),
        ]
        for label, script, extra in checks:
            output = work / (label + ".json")
            run(label.replace("_", " "), [PYTHON, "-B", script, *extra, "--output", output])
            result[label] = json.loads(output.read_text())
            require(result[label]["status"] == "PASS", label + " did not pass")

        novelty = json.loads(run("Comparing all 82 literal reference graphs", [
            PYTHON, "-B", ROOT / "comparison/check_novelty.py", machine / "machine.tm", "--recompute"]))
        require(novelty["comparisons"] == 82 and novelty["matches"] == [], "Corpus novelty failed")
        require(novelty["raw_sha256"] == EXPECTED_SHA, "Novelty checked wrong table")
        novelty["candidate"] = "machine/machine.tm"
        result["novelty"] = novelty
        if not args.quick:
            run("Replaying independent literal-table physical checker", [
                PYTHON, "-B", ROOT / "verification/check_physical.py", machine])
            independent = json.loads((machine / "independent/receipt.json").read_text())
            require(independent == json.loads((ROOT / "machine/independent/receipt.json").read_text()),
                    "Independent physical receipt differs")
            result["independent_physical"] = independent
        else:
            result["skipped"] = ["primary universal physical replay", "independent universal physical replay"]
    result["status"] = "PASS"
    result["elapsed_seconds"] = round(time.monotonic() - start, 3)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(json.dumps({"status": "PASS", "mode": result["mode"], "states": 194,
                      "source_outcomes": 4839, "dense_sha256": EXPECTED_SHA,
                      "elapsed_seconds": result["elapsed_seconds"]}, indent=2))


if __name__ == "__main__":
    main()
