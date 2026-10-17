#!/usr/bin/env python3
"""Replay the archive's finite checks without changing the extracted files.

Usage:
    python3 verify.py
    python3 verify.py --search

The default checks need Python 3.10 or later and only its standard library.
--search additionally needs a C++17 compiler, selected by --compiler or CXX.
It replays four bounded searches on the retained local contexts; it does not
regenerate those contexts or invoke Coq/Lean. All outputs and executables are
created in a temporary copy and removed when the verification finishes.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent


class VerificationError(Exception):
    pass


def read_json(path):
    with path.open(encoding="utf-8") as stream:
        return json.load(stream)


def first_difference(expected, actual, location="$"):
    """Compare parsed data, including numeric/Boolean types and list order."""
    if type(expected) is not type(actual):
        return f"{location}: expected {type(expected).__name__}, got {type(actual).__name__}"
    if isinstance(expected, dict):
        missing = sorted(expected.keys() - actual.keys())
        extra = sorted(actual.keys() - expected.keys())
        if missing or extra:
            return f"{location}: missing keys {missing!r}; extra keys {extra!r}"
        for key in sorted(expected):
            difference = first_difference(expected[key], actual[key], f"{location}.{key}")
            if difference:
                return difference
    elif isinstance(expected, list):
        if len(expected) != len(actual):
            return f"{location}: expected length {len(expected)}, got {len(actual)}"
        for index, (left, right) in enumerate(zip(expected, actual)):
            difference = first_difference(left, right, f"{location}[{index}]")
            if difference:
                return difference
    elif expected != actual:
        return f"{location}: expected {expected!r}, got {actual!r}"
    return None


def compare(expected, actual, label):
    difference = first_difference(expected, actual)
    if difference:
        raise VerificationError(f"{label}: {difference}")


def run(command, cwd, label, timeout=900):
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["PYTHONHASHSEED"] = "0"
    # The baseline scripts contain assertions; preserve them even if the
    # caller normally sets PYTHONOPTIMIZE in their shell.
    environment["PYTHONOPTIMIZE"] = "0"
    try:
        result = subprocess.run(
            [str(part) for part in command], cwd=cwd, env=environment,
            text=True, encoding="utf-8", stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise VerificationError(f"{label}: {error}") from error
    if result.returncode:
        detail = "\n".join(part for part in (result.stdout, result.stderr) if part)
        raise VerificationError(f"{label}: exit {result.returncode}\n{detail}")
    return result.stdout


def parse_search(text, family):
    """Retain every state, edge, option, and summary counter in a C++ log."""
    result = {"header": None, "states": [], "summary": None}
    current = None
    for number, line in enumerate(text.splitlines(), 1):
        tokens = line.split()
        if not tokens:
            continue
        try:
            if tokens[0] == "radius" and len(tokens) == 4 and tokens[2] == "fuel":
                if result["header"] is not None:
                    raise ValueError("duplicate header")
                result["header"] = {"radius": int(tokens[1]), "fuel": int(tokens[3])}
            elif tokens[0] == "state" and len(tokens) == 4 and tokens[2] == "possible":
                if tokens[3] not in {"0", "1"}:
                    raise ValueError("invalid possibility flag")
                current = {"state": int(tokens[1]), "possible": int(tokens[3]), "edges": []}
                result["states"].append(current)
            elif (tokens[0] == "edge" and len(tokens) >= 7
                  and tokens[4] == "patterns" and tokens[6] == "choices"):
                if current is None or int(tokens[3]) != current["state"]:
                    raise ValueError("edge has the wrong deleted state")
                choices = []
                for token in tokens[7:]:
                    if family == "macro":
                        choices.append(int(token))
                    else:
                        match = re.fullmatch(r"([01])([LR])(\d+)", token)
                        if match is None:
                            raise ValueError(f"invalid action {token!r}")
                        choices.append([int(match[1]), match[2], int(match[3])])
                current["edges"].append({
                    "source": int(tokens[1]), "read": int(tokens[2]),
                    "target": int(tokens[3]), "patterns": int(tokens[5]),
                    "choices": choices,
                })
            elif tokens[0] == "SUMMARY" and len(tokens) % 2 == 1:
                if result["summary"] is not None:
                    raise ValueError("duplicate summary")
                result["summary"] = {
                    tokens[index]: int(tokens[index + 1])
                    for index in range(1, len(tokens), 2)
                }
            else:
                raise ValueError("unexpected log line")
        except (ValueError, IndexError) as error:
            raise VerificationError(f"{family} log line {number}: {error}: {line}") from error
    if result["header"] is None or result["summary"] is None:
        raise VerificationError(f"{family} log is missing its header or summary")
    states = result["states"]
    summary = result["summary"]
    derived = {
        "eligible": len(states),
        "edges": sum(len(state["edges"]) for state in states),
        "option_count": sum(len(edge["choices"]) for state in states for edge in state["edges"]),
        "possible": sum(state["possible"] for state in states),
    }
    for key, value in derived.items():
        if summary.get(key) != value:
            raise VerificationError(f"{family} log has inconsistent {key}")
    return result


def replay_searches(machine, temporary_root, compiler):
    compiler_command = shlex.split(compiler)
    if not compiler_command or shutil.which(compiler_command[0]) is None:
        raise VerificationError("--search needs a C++17 compiler; use --compiler or set CXX")
    build = temporary_root / "build"
    build.mkdir()
    for family in ("macro", "action"):
        run(compiler_command + ["-O3", "-std=c++17",
            str(machine / f"edge_{family}_search.cpp"),
            "-o", str(build / f"edge_{family}_search")],
            temporary_root, f"compile {family} search", timeout=180)

    summary = read_json(ROOT / "machine/search_summary.json")
    replayed = 0
    for entry in summary["results"]:
        radius = entry["radius"]
        contexts = read_json(machine / f"edge_contexts_r{radius}.json")
        compare(entry["contexts"], sum(len(edge["patterns"]) for edge in contexts["edges"]),
                f"radius {radius} retained context count")
        compare(entry["context_edges"], len(contexts["edges"]),
                f"radius {radius} retained context edge count")
        for family in ("macro", "action"):
            input_name = (f"edge_contexts_r{radius}.txt" if family == "macro"
                          else f"pre_contexts_r{radius}.txt")
            expected = parse_search((machine / f"edge_{family}_r{radius}.txt").read_text(), family)
            compare({"radius": radius, "fuel": 64}, expected["header"],
                    f"{family} radius {radius} header")
            compare(entry[family], expected["summary"],
                    f"{family} radius {radius} retained JSON summary")
            output = run([build / f"edge_{family}_search", machine / input_name, "64"],
                         temporary_root, f"{family} radius {radius}")
            actual = parse_search(output, family)
            compare(expected, actual, f"{family} radius {radius} full parsed log")
            replayed += 1
            print(f"PASS {family} radius {radius}: complete parsed log and JSON counters match", flush=True)
    return replayed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search", action="store_true", help="also compile and replay four bounded C++ searches")
    parser.add_argument("--compiler", default=os.environ.get("CXX", "c++"),
                        help="C++17 compiler command; defaults to CXX or c++")
    args = parser.parse_args()
    if sys.version_info < (3, 10):
        raise VerificationError("Python 3.10 or later is required")
    ignored = shutil.ignore_patterns("__pycache__", "*.pyc", "*.pyo", "*.o", "*.so", "*.exe")
    with tempfile.TemporaryDirectory(prefix="zfc-unary-verify-") as directory:
        temporary_root = Path(directory)
        machine = temporary_root / "machine"
        code = temporary_root / "code"
        shutil.copytree(ROOT / "machine", machine, ignore=ignored)
        shutil.copytree(ROOT / "code", code, ignore=ignored)
        results = temporary_root / "results"
        results.mkdir()
        print("Replaying finite checks in a temporary copy.", flush=True)
        for name in ("support_diagnostics", "theory_spec"):
            actual_path = results / f"{name}.json"
            expected = read_json(ROOT / "results" / f"{name}.json")
            run([sys.executable, "-B", code / f"{name}.py", "--output", actual_path],
                temporary_root, name)
            compare(expected, read_json(actual_path), name)
            print(f"PASS {name}: complete parsed JSON matches results/{name}.json", flush=True)

        expected = read_json(ROOT / "machine/baseline_audit.json")
        actual_path = machine / "baseline_audit.json"
        actual_path.unlink()
        run([sys.executable, "-B", machine / "audit_baselines.py"],
            temporary_root, "machine baseline audit")
        compare(expected, read_json(actual_path), "machine baseline audit")
        print("PASS baseline_audit: complete parsed JSON matches both tables and full blank-tape bootstraps", flush=True)
        searches = replay_searches(machine, temporary_root, args.compiler) if args.search else 0
    print(f"PASS: 3 core checks; {searches} bounded C++ searches; extracted files unchanged.", flush=True)
    print("Scope: finite diagnostics and literal machine checks; no Coq/Lean build or new consistency proof.")


if __name__ == "__main__":
    try:
        main()
    except (VerificationError, OSError, ValueError, KeyError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
