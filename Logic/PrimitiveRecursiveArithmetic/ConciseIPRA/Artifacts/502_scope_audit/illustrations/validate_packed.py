#!/usr/bin/env python3
"""Compare the fixed packed checker with its expanded source on the 38 fixtures.

Usage: validate_packed.py EXPANDED.py PACKED.py FIXTURE_DIRECTORY [REPORT.json]
The packed loader is verified as the fixed counted wrapper before execution.
"""
import ast
import base64
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import zlib


def run(job):
    name, program, raw, expected, optimized = job
    command = [sys.executable] + (["-O"] if optimized else []) + [str(program)]
    result = subprocess.run(command, input=raw, capture_output=True, timeout=10)
    accepted = result.returncode == 0 and result.stdout == b"ACCEPT\n"
    return {
        "fixture": name, "program": program.name, "optimized": optimized,
        "expected": expected, "accepted": accepted,
        "exit_code": result.returncode,
        "stdout": result.stdout.decode("utf-8", "replace"),
        "matches_expected": accepted == expected,
    }


def validate(expanded, packed, fixtures):
    expanded_raw = expanded.read_bytes()
    packed_raw = packed.read_bytes()
    tree = ast.parse(packed_raw.decode("utf-8"))
    payload = tree.body[1].value.args[0].args[0].args[0].value
    fixed_wrapper = "import zlib, base64\nexec(zlib.decompress(base64.b85decode(" + repr(payload) + ")))\n"
    fixed_wrapper = ast.unparse(ast.parse(fixed_wrapper)) + "\n"
    if fixed_wrapper.encode("utf-8") != packed_raw:
        raise RuntimeError("Packed checker differs from the fixed counted wrapper")
    if zlib.decompress(base64.b85decode(payload)) != expanded_raw:
        raise RuntimeError("Packed payload differs from the full expanded source")
    expected = json.loads((fixtures / "expected.json").read_text())["fixtures"]
    if len(expected) != 38:
        raise RuntimeError("Expected the fixed 38-file inherited fixture suite")
    jobs = []
    for row in expected:
        raw = (fixtures / row["file"]).read_bytes()
        if hashlib.sha256(raw).hexdigest() != row["sha256"]:
            raise RuntimeError("Fixture bytes changed: " + row["file"])
        for optimized in (False, True):
            for program in (expanded, packed):
                jobs.append((row["file"], program, raw,
                             row["expected"]["candidate_502"], optimized))
    with ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(run, jobs))
    failures = [row for row in results if not row["matches_expected"]]
    return {
        "python_version": sys.version.split()[0],
        "zlib_version": zlib.ZLIB_VERSION,
        "zlib_runtime_version": zlib.ZLIB_RUNTIME_VERSION,
        "fixtures": 38,
        "processes": len(results),
        "ordinary_and_optimized_modes": True,
        "expanded_sha256": hashlib.sha256(expanded_raw).hexdigest(),
        "packed_sha256": hashlib.sha256(packed_raw).hexdigest(),
        "complete_payload_identity_verified": True,
        "fixed_counted_outer_loader_verified": True,
        "accepted_processes": sum(row["accepted"] for row in results),
        "rejected_processes": sum(not row["accepted"] for row in results),
        "mismatches": failures,
        "results": results,
        "limitation": "These finite comparisons supplement exact payload identity; they do not constitute a new proof of the inherited arithmetic metatheorems.",
    }


if __name__ == "__main__":
    if len(sys.argv) not in (4, 5):
        raise SystemExit("Usage: validate_packed.py EXPANDED.py PACKED.py FIXTURE_DIRECTORY [REPORT.json]")
    result = validate(*(Path(value).resolve() for value in sys.argv[1:4]))
    if len(sys.argv) == 5:
        Path(sys.argv[4]).write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "results"}, indent=2))
    if result["mismatches"]:
        raise SystemExit(1)
