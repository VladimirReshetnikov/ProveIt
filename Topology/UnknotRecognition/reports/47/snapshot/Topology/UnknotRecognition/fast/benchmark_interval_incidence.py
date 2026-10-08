"""Reproduce exact port-incidence checks and paired local-kernel timings.

The large family has a known residue model that serves as an independent
answer oracle. This formula is specific to the family, not a competing
general interval algorithm. Literal graph comparisons run only at small
sizes; no timing or speedup is extrapolated to an unexecuted expanded case.
"""

import argparse
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import time

from fastunknot.integer_codec import json_safe
from fastunknot.interval_incidence import (
    analyze_port_incidence, verify_port_incidence_certificate,
)


HERE = Path(__file__).resolve().parent


def make_case(bits, port_count):
    period = 1 << bits
    size = 7 * period
    pairs = [{"start": 0, "stop": size - period, "sign": 1, "offset": period}]
    ports, residues = [], []
    denominator = 2 * port_count + 3
    for i in range(port_count):
        low = (2 * i + 1) * period // denominator
        high = min(period, low + (port_count + 1) * period // denominator)
        projected = [[low, high]]
        layer = i % 5
        marks = [[layer * period + low, layer * period + high]]
        if i % 3 == 0:
            projected.append([0, period // denominator])
            marks.append([6 * period, 6 * period + period // denominator])
        ports.append(marks)
        residues.append(projected)
    return {"bits": bits, "period": period, "size": size,
            "pairings": pairs, "ports": ports, "residue_ports": residues}


def endpoint_oracle(case):
    """Count exact signatures on residue intervals, using only endpoints."""
    ends = {0, case["period"]}
    for port in case["residue_ports"]:
        for lo, hi in port:
            ends.update((lo, hi))
    ends = sorted(ends)
    histogram = [0] * (1 << len(case["ports"]))
    for left, right in zip(ends, ends[1:]):
        mask = sum(1 << i for i, port in enumerate(case["residue_ports"])
                   if any(lo <= left < hi for lo, hi in port))
        histogram[mask] += right - left
    return histogram


def literal_oracle(case):
    """Explicit finite graph union/find; it allocates one entry per point."""
    size, pairings, ports = case["size"], case["pairings"], case["ports"]
    parent = list(range(size))

    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for p in pairings:
        for x in range(p["start"], p["stop"]):
            y = p["sign"] * x + p["offset"]
            parent[root(x)] = root(y)
    masks = {root(x): 0 for x in range(size)}
    for i, port in enumerate(ports):
        for low, high in port:
            for x in range(low, high):
                masks[root(x)] |= 1 << i
    result = [0] * (1 << len(ports))
    for mask in masks.values():
        result[mask] += 1
    return result


def measure(case, rounds, rng):
    size, pairings, ports = case["size"], case["pairings"], case["ports"]
    expected = endpoint_oracle(case)
    answer = analyze_port_incidence(size, pairings, ports, record_trace=True)
    proof = answer["certificate"]
    assert answer["histogram"] == expected
    assert verify_port_incidence_certificate(size, pairings, ports, proof)
    arms = ["count", "proof", "verify", "count_control"]
    if case["bits"] <= 12:
        assert literal_oracle(case) == expected
        arms.append("literal")
    samples, order = {arm: [] for arm in arms}, []
    for _ in range(rounds):
        shuffled = list(arms)
        rng.shuffle(shuffled)
        order.append(shuffled)
        for arm in shuffled:
            started = time.perf_counter_ns()
            if arm in ("count", "count_control"):
                result = analyze_port_incidence(size, pairings, ports)
            elif arm == "proof":
                result = analyze_port_incidence(size, pairings, ports, record_trace=True)
            elif arm == "verify":
                result = verify_port_incidence_certificate(size, pairings, ports, proof)
            else:
                result = literal_oracle(case)
            elapsed = time.perf_counter_ns() - started
            if arm == "verify":
                assert result is True
            elif arm == "literal":
                assert result == expected
            else:
                assert result["histogram"] == expected
            samples[arm].append(elapsed)
    encoded_proof = json.dumps(json_safe(proof), sort_keys=True,
                               separators=(",", ":")).encode("utf-8")
    return {"case": case, "histogram": expected, "stats": answer["stats"],
            "nonzero_signatures": sum(bool(value) for value in expected),
            "proof_json_bytes": len(encoded_proof),
            "proof_sha256": hashlib.sha256(encoded_proof).hexdigest(),
            "sample_ns": samples, "round_order": order,
            "median_ms": {arm: statistics.median(times) / 1_000_000
                          for arm, times in samples.items()}}, proof


def source_digests():
    files = [Path(__file__), HERE / "fastunknot" / "interval_incidence.py",
             HERE / "fastunknot" / "interval_orbits.py",
             HERE / "fastunknot" / "interval_orbit_verify.py",
             HERE / "fastunknot" / "integer_codec.py"]
    digests = {str(path.relative_to(HERE)): hashlib.sha256(path.read_bytes()).hexdigest()
               for path in files}
    # Only these two functions of normal_components participate in this task.
    # Hash their exact source, so unrelated ambient-geometry edits do not
    # invalidate a completed timing of the unchanged coning algorithm.
    source = (HERE / "fastunknot" / "normal_components.py").read_text()
    tree = ast.parse(source)
    helpers = [ast.get_source_segment(source, node) for node in tree.body
               if isinstance(node, ast.FunctionDef) and node.name in ("cone_pairings", "_poll")]
    if len(helpers) != 2:
        raise RuntimeError("Coning helper source could not be identified")
    digests["fastunknot/normal_components.py::cone_pairings+_poll"] = hashlib.sha256(
        "\n\n".join(helpers).encode("utf-8")).hexdigest()
    return digests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=HERE / "results" / "interval_incidence_20261008.json")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--bits", type=int, nargs="+", default=[8, 12, 64, 1024, 4096])
    parser.add_argument("--ports", type=int, nargs="+", default=[2, 4, 6, 8])
    args = parser.parse_args()
    if args.rounds < 1 or any(bits < 4 for bits in args.bits):
        parser.error("Use positive rounds and bit parameters at least four")
    if any(not 1 <= count <= 12 for count in args.ports):
        parser.error("Use one through twelve ports")
    before = source_digests()
    rng = random.Random(202610083)
    records = []
    retained = None
    for bits in args.bits:
        for port_count in args.ports:
            record, proof = measure(make_case(bits, port_count), args.rounds, rng)
            records.append(record)
            if bits == 1024 and port_count == 4:
                retained = {"size": record["case"]["size"],
                            "pairings": record["case"]["pairings"],
                            "ports": record["case"]["ports"], "certificate": proof}
            print(f"bits={bits} ports={port_count} count_ms="
                  f"{record['median_ms']['count']:.3f} proof_bytes="
                  f"{record['proof_json_bytes']}", flush=True)
    after = source_digests()
    if before != after:
        raise RuntimeError("Measured dependencies changed during the benchmark")
    result = {
        "schema": "interval-port-incidence-benchmark-v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(), "platform": platform.platform(),
        "rounds": args.rounds, "seed": 202610083,
        "scope": "Local incidence counts; no whole-recognizer timing or extrapolation",
        "family": "Seven sheets of a residue interval under one partial translation",
        "oracle": "Independent residue endpoint partition; literal DSU for bits<=12",
        "source_sha256": before, "records": records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(result), indent=2) + "\n")
    if retained is not None:
        proof_path = args.output.with_name("interval_incidence_cert_1024_4.json")
        proof_path.write_text(json.dumps(json_safe(retained), indent=2) + "\n")
    print(f"Saved {len(records)} exact comparisons to {args.output}", flush=True)


if __name__ == "__main__":
    main()
