#!/usr/bin/env python3
"""Verify all direct-component literals; optionally rebuild into a temporary tree."""
from __future__ import annotations
from copy import deepcopy
from hashlib import sha256
import argparse
import json
from math import prod
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from audit_common_radix import (Trace, audit_frame, audit_offsets, audit_radix,
                               count_and_expand, digit_controls, positivity,
                               replay_affine_projection, require)
from verify_projection import verify as verify_projection

ROOT = Path(__file__).resolve().parent


def read(path):
    return json.loads(path.read_text())


def run(command):
    args = [sys.executable] + ([] if __debug__ else ["-O"]) + [str(a) for a in command]
    result = subprocess.run(args, check=True, capture_output=True, text=True, cwd=ROOT)
    return result.stdout


def check_fixtures():
    fixture = read(ROOT / "output/shared_frame/FIXTURES.json")
    full = fixture["full_shared_frame"]
    values = full["values"]
    require(all(isinstance(v, int) and v >= 0 for v in values), "fixture is not natural")
    require(len(values) == len(full["variables"]), "fixture assignment dimension")
    for row in full["rows"]:
        require(sum(c*prod(values[i] for i in mon) for c, mon in row["terms"]) == 0,
                "literal fixture residual is nonzero")
    for (n, k), output in zip(full["inputs"], full["power_outputs"]):
        require(values[output[1]] == n**k, "fixture power value mismatch")
    bad = list(values)
    bad[full["power_outputs"][0][1]] += 1
    require(any(sum(c*prod(bad[i] for i in mon) for c, mon in row["terms"])
                for row in full["rows"]), "mutated literal fixture accepted")
    d = fixture["distinct_index_frame"]
    A, B, U, V, P = [d[k] for k in ("A", "B", "U", "V", "P")]
    require(U*U-(A*A-1)*V*V == 1, "distinct-index auxiliary norm")
    require(U % (4*P*P) == 1 and V > 0 and V % (4*P*P) == 0, "pooled period")
    require(B > 1 and (B-A) % U == 0 and (B-1) % (4*P) == 0, "shared parameter CRT")
    for g in d["groups"]:
        k, X, Y, S, R = [g[j] for j in ("k", "X", "Y", "S", "R")]
        require(X*X-(A*A-1)*Y*Y == 1 and S*S-(B*B-1)*R*R == 1, "index norms")
        require((S-X) % U == 0 and (R-k) % (4*Y) == 0, "index congruences")
    return {"literal_frame_rows": len(full["rows"]), "distinct_indices": len(d["groups"]),
            "mutated_output_rejected": True}


def rebuild():
    compared = []
    with TemporaryDirectory(prefix="common-radix-rebuild-") as temporary:
        temp = Path(temporary)
        variants = [("common_radix", []), ("common_radix_offset", ["--shared-offset"]),
                    ("shared_frame", ["--shared-offset", "--shared-frame"])]
        for name, options in variants:
            run([ROOT / "build_common_radix.py", *options, "--output", temp / name])
            for file in ("equation.json", "expanded_polynomial.json", "construction_trace.json"):
                require((temp / name / file).read_bytes() == (ROOT / "output" / name / file).read_bytes(),
                        "rebuild differs: " + name + "/" + file)
                compared.append(name + "/" + file)
        for name, options in [("compact667", []), ("compact680", ["--quadratic-first"])]:
            run([ROOT / "terminal_elimination.py", temp / "shared_frame/equation.json", temp / name,
                 "--max-support", "16", "--expand", *options])
            for file in ("equation.json", "expanded_polynomial.json", "terminal_elimination_certificate.json"):
                require((temp / name / file).read_bytes() == (ROOT / "output" / name / file).read_bytes(),
                        "rebuild differs: " + name + "/" + file)
                compared.append(name + "/" + file)
        run([ROOT / "shared_frame_fixture.py", "--output", temp / "FIXTURES.json"])
        require((temp / "FIXTURES.json").read_bytes() == (ROOT / "output/shared_frame/FIXTURES.json").read_bytes(),
                "fixture rebuild differs")
        compared.append("shared_frame/FIXTURES.json")
    return {"byte_identical_files": compared, "count": len(compared)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    provenance = read(ROOT / "PROVENANCE.json")
    for name, expected in provenance["upstream_exact_copy_sha256"].items():
        actual = sha256((ROOT / "upstream/direct" / name).read_bytes()).hexdigest()
        require(actual == expected, "upstream source changed: " + name)
    result = {"status": "PASS", "immutable_source_hashes": len(provenance["upstream_exact_copy_sha256"]),
              "stages": {}, "projections": {}, "digit_controls": digit_controls()}
    for name in ("common_radix", "common_radix_offset", "shared_frame"):
        directory = ROOT / "output" / name
        equation = read(directory / "equation.json")
        trace = Trace(read(directory / "construction_trace.json"))
        result["stages"][name] = {
            "metrics": count_and_expand(equation, read(directory / "expanded_polynomial.json")),
            "affine_projection": replay_affine_projection(trace, equation),
            "radix": audit_radix(trace), "offset": audit_offsets(trace),
            "frame": audit_frame(trace), "positivity": positivity(trace)}
    parent = read(ROOT / "output/shared_frame/equation.json")
    for name in ("compact667", "compact680"):
        directory = ROOT / "output" / name
        child = read(directory / "equation.json")
        certificate = read(directory / "terminal_elimination_certificate.json")
        projection = verify_projection(parent, child, certificate)
        projection["metrics"] = count_and_expand(child, read(directory / "expanded_polynomial.json"))
        bad = deepcopy(certificate)
        bad["steps"][0]["restoration"][0][0] += 1
        rejected = False
        try:
            verify_projection(parent, child, bad)
        except ValueError:
            rejected = True
        require(rejected, "corrupted projection was accepted")
        projection["mutated_restoration_rejected"] = True
        result["projections"][name] = projection
    result["fixtures"] = check_fixtures()
    if args.rebuild:
        result["rebuild"] = rebuild()
    result["scope"] = "literal integer-polynomial data and finite controls, not a consistency proof"
    payload = json.dumps(result, indent=2, sort_keys=True)+"\n"
    if args.receipt:
        args.receipt.write_text(payload)
    print(payload)


if __name__ == "__main__":
    main()
