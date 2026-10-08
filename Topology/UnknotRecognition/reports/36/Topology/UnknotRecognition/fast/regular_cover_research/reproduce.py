#!/usr/bin/env python3
"""Reproduce finite-sheet audits and compressed regular-cover measurements.

Run from fast/:
  python regular_cover_research/reproduce.py --output results/regular_cover_gluing_20261008.json

No external dependencies, sheet-expanding large benchmark, or knot verdicts.
All generated comparison inputs are isomorphic by known block gauges. The
independent small audit also generates inequivalent and impossible marked
comparisons and uses literal sheet permutations and exhaustive gauge tuples.
"""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.regular_cover_gluing import (  # noqa: E402
    RegularCoverAssembly, compare_assemblies, verify_certificate,
    transport_witness, verify_transport, canonicalize_assembly, phase_orbit_count,
)
from regular_cover_research.oracle import (  # noqa: E402
    ExpandedGroup, element, make_assembly, brute_phase_orbits,
)


def hex_tree(value):
    if type(value) is int:
        return hex(value)
    if isinstance(value, (tuple, list)):
        return [hex_tree(x) for x in value]
    if isinstance(value, dict):
        return {key: hex_tree(item) for key, item in value.items()}
    return value


def digest(value):
    payload = json.dumps(hex_tree(value), sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def audit_small_cases():
    counters = Counter()

    def check(source, target, marks):
        group = ExpandedGroup(source["group"]["kind"], source["group"]["modulus"])
        actual = group.all_gauges(source, target, marks)
        certificate = compare_assemblies(source, target, marks)
        assert verify_certificate(source, target, marks, certificate)
        assert certificate["isomorphism_count"] == len(actual)
        assert certificate["equivalent"] == bool(actual)
        if actual:
            witness = transport_witness(source, target, certificate)
            assert verify_transport(source, target, marks, witness)
            assert tuple(group.encode(x) for x in witness) in actual
        counters["comparisons"] += 1
        counters["equivalent"] += bool(actual)
        counters["inequivalent"] += not bool(actual)
        counters["accepted_literal_gauge_tuples"] += len(actual)

    for kind in ("cyclic", "dihedral"):
        for modulus in range(1, 8):
            group = ExpandedGroup(kind, modulus)
            source = make_assembly(kind, modulus, 1, [], extras=(2, 3))
            for boundary in range(source["blocks"][0]["surface"]["boundary_components"]):
                for x, y in product(range(group.size), repeat=2):
                    marks = [{"kind": "boundary", "block": 0, "boundary": boundary,
                              "source": group.decode(x), "target": group.decode(y)}]
                    check(source, source, marks)
                    counters["boundary_lift_pair_queries"] += 1

    rng = random.Random(20261008)
    graphs = [(2, [(0, 1), (1, 0)]), (2, [(0, 0), (0, 1), (1, 1)]),
              (3, [(0, 1), (1, 2), (2, 0)]), (3, [(1, 0)])]
    for kind in ("cyclic", "dihedral"):
        for modulus in range(1, 7):
            group = ExpandedGroup(kind, modulus)
            for _ in range(10):
                vertices, graph = rng.choice(graphs)
                source = make_assembly(kind, modulus, vertices, graph,
                                       [group.decode(rng.randrange(group.size)) for _ in graph],
                                       extras=(2, 3))
                target = deepcopy(source)
                for edge in target["edges"]:
                    edge["phase"] = group.decode(rng.randrange(group.size))
                marks = []
                for _ in range(rng.randrange(4)):
                    vertex = rng.randrange(vertices)
                    mark = {"kind": rng.choice(("point", "boundary")), "block": vertex,
                            "source": group.decode(rng.randrange(group.size)),
                            "target": group.decode(rng.randrange(group.size))}
                    if mark["kind"] == "boundary":
                        mark["boundary"] = rng.randrange(
                            source["blocks"][vertex]["surface"]["boundary_components"])
                    marks.append(mark)
                check(source, target, marks)
                counters["random_marked_graph_queries"] += 1

    orbit_records = []
    for kind in ("cyclic", "dihedral"):
        for modulus in range(1, 7):
            group = ExpandedGroup(kind, modulus)
            graph = [(0, 0), (0, 0)]
            expected = brute_phase_orbits(kind, modulus, 1, graph)
            keys = set()
            for phases in product(range(group.size), repeat=2):
                source = make_assembly(kind, modulus, 1, graph,
                                       [group.decode(x) for x in phases])
                canonical = canonicalize_assembly(source)
                keys.add(canonical["key"])
                target = deepcopy(source)
                for edge, phase in zip(target["edges"], canonical["phases"]):
                    edge["phase"] = phase
                assert verify_transport(source, target, [], canonical["gauges"])
            assert len(keys) == expected == phase_orbit_count(kind, modulus, 2)
            orbit_records.append({"kind": kind, "modulus": modulus,
                                  "cycle_rank": 2, "phase_assignments": group.size ** 2,
                                  "literal_orbits": expected, "canonical_keys": len(keys)})
    return {"counts": dict(counters), "phase_orbits": orbit_records}


def build_benchmark_case(bits, scenario, vertices=64):
    modulus = 105 * (1 << bits)
    graph = [(i, (i - 1) // 2) if i % 2 else ((i - 1) // 2, i)
             for i in range(1, vertices)]
    if scenario == "cycle_constraints":
        graph.extend((i, vertices - 1 - i) for i in range(17))
    rng = random.Random(1000003 * bits + (scenario == "cycle_constraints"))
    phases = [element() for _ in graph]
    if scenario == "cycle_constraints":
        for index in range(vertices - 1, len(graph)):
            phases[index] = element(rng.randrange(2), rng.getrandbits(bits + 7) % modulus)
        phases[-1] = element(1, 23)  # at least one reflection chord
    else:
        phases = [element(rng.randrange(2), rng.getrandbits(bits + 7) % modulus)
                  for _ in graph]
    source = make_assembly("dihedral", modulus, vertices, graph, phases, extras=(6, 10, 14))
    prepared = RegularCoverAssembly(source)
    group = prepared.group
    gauges = [(rng.randrange(2), rng.getrandbits(bits + 7) % modulus) for _ in range(vertices)]
    target = deepcopy(source)
    for edge in target["edges"]:
        u, v = edge["source"]["block"], edge["target"]["block"]
        old = group.parse(edge["phase"])
        new = group.multiply(group.inverse(gauges[u]), group.multiply(old, gauges[v]))
        edge["phase"] = element(*new)
    degree = [0] * vertices
    for u, v in graph:
        degree[u] += 1
        degree[v] += 1
    marks = []
    for index in range(32):
        vertex = (index * 37) % vertices
        point = (rng.randrange(2), rng.getrandbits(bits + 7) % modulus)
        marks.append({"kind": "boundary", "block": vertex,
                      "boundary": degree[vertex] + index % 3,
                      "source": element(*point),
                      "target": element(*group.multiply(point, gauges[vertex]))})
    expected_count = 2 if scenario == "cycle_constraints" else modulus // 210
    return {"source": source, "target": target, "marks": marks, "bits": modulus.bit_length(),
            "scenario": scenario, "vertices": vertices, "edges": len(graph),
            "expected_count": expected_count}


def benchmark(rounds):
    cases = [build_benchmark_case(bits, scenario)
             for bits in (32, 128, 512, 2048, 8192, 24000)
             for scenario in ("tree_boundary_constraints", "cycle_constraints")]
    measurements = []
    for case in cases:
        case["prepared_source"] = RegularCoverAssembly(case["source"])
        case["prepared_target"] = RegularCoverAssembly(case["target"])
        case["samples"] = {name: [] for name in (
            "validated_compare_seconds", "prepared_compare_seconds",
            "certificate_verify_seconds", "direct_transport_verify_seconds",
            "canonicalize_seconds")}
        case["poll_calls"] = 0

        def poll():
            case["poll_calls"] += 1

        certificate = compare_assemblies(case["source"], case["target"], case["marks"], check=poll)
        assert certificate["isomorphism_count"] == case["expected_count"]
        assert verify_certificate(case["source"], case["target"], case["marks"], certificate)
        case["certificate_hash"] = digest(certificate)
        case["families"] = sum("obstruction" not in b
                               for record in certificate["components"] for b in record["branches"])
        case["isomorphism_count_bits"] = certificate["isomorphism_count"].bit_length()
        canonical_source = canonicalize_assembly(case["prepared_source"])
        canonical_target = canonicalize_assembly(case["prepared_target"])
        assert canonical_source["key"] == canonical_target["key"]

    rng = random.Random(618033988)
    for _ in range(rounds):
        rng.shuffle(cases)
        for case in cases:
            raw_source, raw_target, marks = case["source"], case["target"], case["marks"]
            source, target = case["prepared_source"], case["prepared_target"]
            start = time.perf_counter()
            certificate = compare_assemblies(raw_source, raw_target, marks)
            case["samples"]["validated_compare_seconds"].append(time.perf_counter() - start)
            start = time.perf_counter()
            prepared_certificate = compare_assemblies(source, target, marks)
            case["samples"]["prepared_compare_seconds"].append(time.perf_counter() - start)
            assert certificate == prepared_certificate
            start = time.perf_counter()
            assert verify_certificate(source, target, marks, certificate)
            case["samples"]["certificate_verify_seconds"].append(time.perf_counter() - start)
            witness = transport_witness(source, target, certificate)
            start = time.perf_counter()
            assert verify_transport(source, target, marks, witness)
            case["samples"]["direct_transport_verify_seconds"].append(time.perf_counter() - start)
            start = time.perf_counter()
            canonicalize_assembly(source)
            case["samples"]["canonicalize_seconds"].append(time.perf_counter() - start)

    for case in sorted(cases, key=lambda item: (item["scenario"], item["bits"])):
        measurements.append({key: case[key] for key in (
            "scenario", "bits", "vertices", "edges", "poll_calls", "families",
            "isomorphism_count_bits", "certificate_hash")} | {
                "marks": len(case["marks"]),
                "samples": case["samples"],
                "medians": {key: statistics.median(value)
                            for key, value in case["samples"].items()},
            })
    control = next(case for case in cases
                   if case["scenario"] == "tree_boundary_constraints" and case["bits"] == 2055)
    ratios = []
    for _ in range(rounds):
        a = time.perf_counter()
        compare_assemblies(control["prepared_source"], control["prepared_target"], control["marks"])
        first = time.perf_counter() - a
        a = time.perf_counter()
        compare_assemblies(control["prepared_source"], control["prepared_target"], control["marks"])
        second = time.perf_counter() - a
        ratios.append(first / second)
    return {"rounds": rounds, "cases": measurements,
            "prepared_compare_AA_ratio_samples": ratios}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--rounds", type=int, default=7)
    parser.add_argument("--skip-audit", action="store_true")
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    started = time.perf_counter()
    root = Path(__file__).resolve().parents[1]
    result = {
        "schema": "regular-cover-gluing-research-v1",
        "status": "restricted geometric kernel; no knot verdict or global complexity claim",
        "python": sys.version,
        "platform": platform.platform(),
        "code_sha256": hashlib.sha256(
            (root / "fastunknot" / "regular_cover_gluing.py").read_bytes()).hexdigest(),
        "audit": None if args.skip_audit else audit_small_cases(),
        "benchmark": benchmark(args.rounds),
        "timing_scope": {
            "validated_compare": "raw inputs, full schema and peripheral validation, solve",
            "prepared_compare": "prepared models, validate marks, solve",
            "verification": "prepared models; separate arithmetic certificate and direct transport",
            "canonicalization": "prepared unmarked model; input generation and digest excluded",
            "expanded_comparison": "none; exhaustive expanded oracle is for correctness only",
        },
    }
    result["elapsed_seconds"] = time.perf_counter() - started
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "elapsed_seconds": result["elapsed_seconds"],
                      "audit": None if result["audit"] is None else result["audit"]["counts"],
                      "benchmark_cases": len(result["benchmark"]["cases"])}))


if __name__ == "__main__":
    main()
