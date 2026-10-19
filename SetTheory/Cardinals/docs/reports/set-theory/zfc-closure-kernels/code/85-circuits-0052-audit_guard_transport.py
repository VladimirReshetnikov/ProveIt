#!/usr/bin/env python3
"""Independently check product-invariant transport and its exact case ordering.

The checker uses leaf_cfg.py rather than the prior invariant checker or the
layout emitter.  Its abstract transfer and finite fixture construction are
implemented here.  Default paths refer to the delivered research archive.
Finite instruction fixtures remain finite rejection evidence.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import re

from leaf_cfg import Program, check_map, increment, strip
from verify_blank import read_table, verify

PIN = "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746"
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
INITIAL = (7, 1, 1, 7, 7, 1, 7, 7, 7)
EXCLUDED = (8202, 8203, 8204, 8358, 8359, 8360)
ROTATIONS = (0, 233, 235, 236, 237)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def file_hash(path):
    return sha256(path.read_bytes()).hexdigest()


def parse_source(path):
    raw = path.read_bytes()
    require(sha256(raw).hexdigest() == PIN, "Wrong source program bytes")
    body = raw.decode("ascii").split("Definition p254_tab", 1)[1]
    body = body.split("[", 1)[1].split("].", 1)[0]
    tokens = re.findall(r"CN|CI|CD|CB|CC|CH|\d+|[(),;]", body)
    require(re.sub(r"CN|CI|CD|CB|CC|CH|\d+|[(),;]|\s+", "", body) == "",
            "Unparsed source text")
    cursor, nodes = 0, []
    while cursor < len(tokens):
        require(tokens[cursor] == "(", "Expected node opening")
        cursor += 1
        pair = []
        for branch in range(2):
            op = tokens[cursor]
            cursor += 1
            require(op in {"CN", "CI", "CD", "CB", "CC", "CH"}, "Invalid source opcode")
            arg = None if op == "CH" else int(tokens[cursor])
            cursor += op != "CH"
            pair.append((op, arg))
            require(tokens[cursor] == ("," if branch == 0 else ")"), "Malformed source node")
            cursor += 1
        nodes.append(pair)
        if cursor < len(tokens):
            require(tokens[cursor] == ";", "Expected source separator")
            cursor += 1
    require(len(nodes) == 6459, "Unexpected source node count")
    sites, visited = [], set()

    def descend(node, address):
        require(0 <= node < len(nodes) and node not in visited, "Source is not a tree")
        visited.add(node)
        for bit, (op, arg) in enumerate(nodes[node]):
            word = address + str(bit)
            if op == "CN":
                descend(arg, word)
            else:
                sites.append((word, op, arg))

    descend(0, "")
    require(len(visited) == 6459 and len(sites) == 6460, "Incomplete source traversal")
    return Program(sites)


def cases(program):
    addresses = [row[0] for row in program.sites]
    require(addresses == sorted(addresses), "Site indices must be zero-based lexicographic leaf order")
    index = {address: i for i, address in enumerate(addresses)}
    require(index[program.initial] == 0, "Initial leaf differs")
    result = []
    for i, (pc, op, arg) in enumerate(program.sites):
        require(op not in {"CI", "CD"} or 0 <= arg < 9, "Invalid logical register")
        for zero in ((True, False) if op == "CD" else (None,)):
            successors = program.successors(pc)
            guard = "zero" if zero is True else "positive" if zero is False else "always"
            target = None if op == "CH" else index[successors[guard]]
            result.append((i, pc, op, arg, zero, target))
    require(len(result) == 8391, "Unexpected guarded-case count")
    return result


def label(case):
    i, pc, op, arg, zero, target = case
    return i, op, arg if op in {"CI", "CD"} else None, zero, target


def represented(mask):
    return {category for category in range(3) if mask & (1 << category)}


def image(categories, op, zero):
    if op == "CI":
        return {1 if category == 0 else 2 for category in categories}
    if zero:
        return categories & {0}
    result = set()
    if 1 in categories:
        result.add(0)
    if 2 in categories:
        result.update((1, 2))
    return result


def check_product(certificate, edges):
    require(certificate["program_sha256"] == PIN, "Certificate source binding failed")
    require(certificate["logical_register_order"] == ["N", "T", "W", "A", "D", "H", "X", "Y", "L"],
            "Wrong logical register order")
    require(certificate["categories"] == ["0", "1", "at least2"], "Wrong category semantics")
    require(tuple(certificate["initial_masks"]) == INITIAL, "Wrong root invariant")
    masks = certificate["masks"]
    require(len(masks) == 6460, "Wrong number of site invariants")
    for row in masks:
        require(row is None or (len(row) == 9 and all(type(mask) is int and 0 < mask < 8 for mask in row)),
                "Malformed product mask")
    require(masks[0] is not None, "Initial site declared unreachable")
    require(all(represented(a) <= represented(b) for a, b in zip(INITIAL, masks[0])),
            "Initial product not included")
    excluded, nonhalting_edges = [], 0
    for number, (source, pc, op, arg, zero, target) in enumerate(edges):
        row = masks[source]
        after = None if row is None else list(map(represented, row))
        if after is not None and op in {"CI", "CD"}:
            after[arg] = image(after[arg], op, zero)
            if not after[arg]:
                after = None
        if after is None:
            excluded.append(number)
        elif target is not None:
            require(masks[target] is not None, f"Edge {number} enters empty invariant")
            require(all(a <= represented(b) for a, b in zip(after, masks[target])),
                    f"Product closure failed on guarded case {number}")
            nonhalting_edges += 1
    require(tuple(excluded) == EXCLUDED == tuple(certificate["excluded_case_indices"]),
            "Unexpected excluded guards")
    return {
        "status": "PASS", "initial_logical_masks": list(INITIAL),
        "sites_with_nonempty_invariant": sum(row is not None for row in masks),
        "guarded_cases": len(edges), "feasible_guarded_cases": len(edges) - len(excluded),
        "feasible_nonhalting_edges": nonhalting_edges,
        "excluded": [{"case_index": number, "leaf_index": edges[number][0],
                      "address": edges[number][1], "opcode": edges[number][2],
                      "argument": edges[number][3], "zero_guard": edges[number][4],
                      "source_masks": masks[edges[number][0]]} for number in excluded],
    }


def paint(pc, head, distance, values):
    require(distance >= len(pc), "Header precedes program counter")
    ones = {head - 1, head + distance}
    ones.update(head + i for i, bit in enumerate(pc) if bit == "1")
    offset = head + distance + 1
    for value in values:
        ones.update(offset + j for j in range(1, value + 2))
        offset += value + 2
    return sorted(ones)


def fixture(edge):
    site, pc, op, arg, zero, target = edge
    registers = [(3 * i + 1) % 5 for i in range(9)]
    if op == "CD":
        registers[PHYSICAL[arg]] = 0 if zero else 2
    source = paint(pc, 0, 40, registers + [0, 2])
    if op == "CH":
        return [1, 0, len(source), *source, 0]
    spare, extra = [0, 2], 0
    if op == "CI":
        registers[PHYSICAL[arg]] += 1
        spare.append(1)
        raw = pc
    elif op == "CD" and not zero:
        registers[PHYSICAL[arg]] -= 1
        extra, raw = 1, pc
    elif op == "CD":
        raw = strip(pc, "0", 1)
    elif op == "CB":
        raw = strip(pc, "0", arg)
    else:
        raw = strip(pc, "1", arg)
    if op == "CC":
        nextpc, overflow = raw, False
    else:
        overflow = not raw or set(raw) == {"1"}
        nextpc = "" if overflow else increment(raw)
    head = -int(overflow)
    expected = paint(nextpc, head, 40 + extra + int(overflow), registers + spare)
    return [0, head, len(source), *source, len(expected), *expected]


def read_fixtures(path):
    lines = path.read_text().splitlines()
    nrows = int(lines[0])
    table = {}
    for row in lines[1:nrows + 1]:
        state, bit, write, move, target = map(int, row.split())
        require((state, bit) not in table, "Duplicate fixture transition")
        table[state, bit] = write, move, target
    count = int(lines[nrows + 1])
    tests = [list(map(int, row.split())) for row in lines[nrows + 2:]]
    require(count == len(tests), "Fixture count differs from contents")
    return table, tests


def check_fixtures(path, table, expected):
    actual_table, actual = read_fixtures(path)
    require(actual_table == table, f"Fixture table differs: {path.name}")
    require(len(actual) == len(expected), "Wrong fixture count")
    for index, (a, b) in enumerate(zip(actual, expected)):
        require(a == b, f"Fixture {index} does not match its labeled source guard")
    return {"status": "PASS", "cases": len(actual), "sha256": file_hash(path),
            "table_rows": len(table), "scope": "Exact finite source/expected-frame fixtures and case order"}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--package", type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument("--fixtures-root", type=Path,
                    help="Optional directory holding rotationN_merges and rotationN_admissible fixture directories")
    ap.add_argument("--baseline-fixtures", type=Path, help="Optional original unfiltered baseline fixture file")
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    package = args.package
    source_path = package / "reference/context246/sources/Prog254.v"
    certificate_path = package / "reference/guard-invariant/product-invariant.json"
    base = parse_source(source_path)
    original = cases(base)
    certificate = json.loads(certificate_path.read_text())
    report = {"status": "PASS", "source_sha256": file_hash(source_path),
              "certificate_sha256": file_hash(certificate_path),
              "scope": "All natural N,A,D,X,Y,L; T=W=H=0 at the empty-PC root",
              "baseline": check_product(certificate, original), "layouts": []}
    if args.baseline_fixtures:
        table = read_table(package / "reference/context246/machine/zfc_prefix246_old.tm")
        expected = list(map(fixture, original))
        report["baseline"]["unfiltered_fixtures"] = check_fixtures(args.baseline_fixtures, table, expected)
        if args.fixtures_root:
            report["baseline"]["restricted_fixtures"] = check_fixtures(
                args.fixtures_root / "baseline_admissible/merge-cases.txt", table,
                [row for i, row in enumerate(expected) if i not in EXCLUDED])
    for rotation in ROTATIONS:
        directory = package / f"candidates/layout{rotation}"
        program_path = directory / "program.json"
        data = json.loads(program_path.read_text())
        program = Program(data["sites"] if isinstance(data, dict) else data)
        edges = cases(program)
        mapping = dict(zip(sorted(base.by_address), sorted(program.by_address)))
        equivalence = check_map(base, program, mapping)
        require(equivalence["status"] == "PASS", "Independent leaf-graph check failed")
        require(list(map(label, original)) == list(map(label, edges)), "Guard-index labels differ")
        entry = {"layout": rotation, "program_sha256": file_hash(program_path),
                 "leaf_graph": equivalence, "product": check_product(certificate, edges)}
        table = read_table(directory / "machine_old.tm")
        if args.fixtures_root:
            expected = list(map(fixture, edges))
            entry["unfiltered_fixtures"] = check_fixtures(
                args.fixtures_root / f"rotation{rotation}_merges/merge-cases.txt", table, expected)
            entry["restricted_fixtures"] = check_fixtures(
                args.fixtures_root / f"rotation{rotation}_admissible/merge-cases.txt", table,
                [row for i, row in enumerate(expected) if i not in EXCLUDED])
        bootpath = package / f"verification/proof/lowcost/rotation{rotation}-start95-bootstrap.json"
        if bootpath.exists():
            boot = json.loads(bootpath.read_text())
            require(boot["old_table_sha256"] == file_hash(directory / "machine_old.tm"),
                    "Bootstrap table byte hash differs")
            hit = {"start": boot["start"], "steps": boot["steps"], "head": boot["head"],
                   "state": boot["dispatcher"], "header": boot["header"],
                   "values": boot["physical_primaries"] + boot["spare_values"],
                   "logical": boot["logical_primaries"]}
            fresh = verify(table, hit)
            require(fresh["one_cells"] == boot["one_cells"], "Stored bootstrap support differs")
            logical = fresh["logical_primaries"]
            require(logical[1] == logical[2] == logical[5] == 0, "Bootstrap lacks stronger zero-root condition")
            entry["exact_blank_bootstrap"] = {"status": "PASS", "steps": boot["steps"],
                "start": boot["start"], "empty_pc": True, "logical_primaries": logical,
                "T_W_H_zero": True, "complete_support_cells": len(fresh["one_cells"])}
        report["layouts"].append(entry)
    output = args.output or package / "verification/proof/guard-transport-independent.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "layouts": len(report["layouts"]),
                      "excluded_case_indices": list(EXCLUDED), "output": str(output)}, indent=2))


if __name__ == "__main__":
    main()
