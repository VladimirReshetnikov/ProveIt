#!/usr/bin/env python3
"""Offline finite checks for the 271-state three-congruence fusion experiment.

Python 3.10+; standard library only. See README.md and PROVENANCE.md.
Checks the NEW fused reference against its compressed candidate, regenerates
the binary table, and independently extracts decision edges from that table.
These checks do not prove the binary compiler or the ZFC consistency endpoint.
"""
from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REGISTERS = ["nextproof", "topwff", "wffstack", "axiomcode", "param1",
             "param2", "scratch1", "scratch2", "prooflist"]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(items):
    result = {}
    for key, value in items:
        require(key not in result, f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(), object_pairs_hook=unique_object)


def load_dag(path):
    data = read_json(path)
    require(type(data["root"]) is int and data["root"] == 0, "DAG root is not zero")
    nodes = {int(q): tuple(es) for q, es in data["nodes"].items()}
    names = {int(q): name for q, name in data["names"].items()}
    require(set(data["nodes"]) == {str(q) for q in nodes}, "noncanonical node IDs")
    require(set(nodes) == set(range(len(nodes))) == set(names), "nondense DAG IDs")
    require(len(set(names.values())) == len(names), "duplicate DAG state name")
    for edges in nodes.values():
        require(len(edges) == 2, "DAG node has other than two edges")
        for edge in edges:
            require(isinstance(edge, str), "edge is not a string")
            match = re.fullmatch(r"(ENode|EInc|EDecnz|EBreak|EContinue) (\d+)|EHalt", edge)
            require(match is not None, f"unknown DAG edge {edge}")
            if edge.startswith("ENode "):
                require(int(edge[6:]) in nodes, "DAG edge names absent node")
            elif edge.startswith(("EInc ", "EDecnz ")):
                require(int(edge.split()[1]) < len(REGISTERS), "absent register")
    done, active = set(), set()

    def visit(q):
        require(q not in active, "cyclic decision DAG")
        if q in done:
            return
        active.add(q)
        for edge in nodes[q]:
            if edge.startswith("ENode "):
                visit(int(edge[6:]))
        active.remove(q)
        done.add(q)

    visit(0)
    require(done == set(nodes), "unreachable decision node")
    return nodes, names


def load_engine():
    path = HERE / "vendor/source08_rm_verifier.py"
    spec = importlib.util.spec_from_file_location("fusion_source08_rm", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_certificate(engine, reference, candidate, cert):
    """All-record operation equality and both-exit closure, with reachability.

    Adapted from ProveIt's layout_grammar_experiment.independent_check, using
    the independently written source-08 path interpreter, not the generator.
    """
    old, new = engine.Machine(reference), engine.Machine(candidate)
    records = cert["pairs"]
    require(records and type(cert["initial"]) is int and cert["initial"] == 0,
            "bad initial record")
    require(cert["branch_order"] == "EDecnz: zero, positive", "bad branch order")
    require(old.contract("") == (records[0]["old"], records[0]["instruction"]),
            "reference initial operation mismatch")
    require(new.contract("") == (records[0]["new"], records[0]["instruction"]),
            "candidate initial operation mismatch")
    distinct = set()
    for row in records:
        left, right, op = row["old"], row["new"], row["instruction"]
        require(re.fullmatch("[01]+", left) is not None and
                re.fullmatch("[01]+", right) is not None, "invalid path")
        require((left, right) not in distinct, "duplicate record")
        distinct.add((left, right))
        require(old.lookup(left) == (left, op), "reference instruction mismatch")
        require(new.lookup(right) == (right, op), "candidate instruction mismatch")
        a_targets, b_targets = old.targets(left, op), new.targets(right, op)
        successors = row["successors"]
        require(len(a_targets) == len(b_targets) == len(successors), "wrong arity")
        for index, a, b in zip(successors, a_targets, b_targets, strict=True):
            require(type(index) is int and 0 <= index < len(records),
                    "invalid successor index")
            target = records[index]
            require(a == (target["old"], target["instruction"]),
                    "reference successor mismatch")
            require(b == (target["new"], target["instruction"]),
                    "candidate successor mismatch")
    reached, pending = set(), [0]
    while pending:
        index = pending.pop()
        if index not in reached:
            reached.add(index)
            pending.extend(records[index]["successors"])
    require(len(reached) == len(records), "unreachable certificate records")
    return {"verified": True, "pairs": len(records),
            "reference_nodes": len(reference), "candidate_nodes": len(candidate),
            "instructions": dict(Counter(r["instruction"].split()[0] for r in records))}


def compile_dag(nodes, names):
    """Thin adapter for the verbatim MIT-0 Wade generator in vendor/."""
    sys.path.insert(0, str(HERE / "vendor"))
    import TMBuilder as backend
    builder = backend.TMBuilder()
    registers = [builder.reg(name) for name in REGISTERS]

    def leaf(edge):
        if edge == "EHalt":
            return "halt"
        kind, value = edge.split()
        n = int(value)
        if kind == "ENode":
            return n
        if kind == "EInc":
            return registers[n].inc
        if kind == "EDecnz":
            return registers[n].decnz
        return f"_{'break' if kind == 'EBreak' else 'continue'}.{n}"

    for q in range(len(nodes)):
        seq = backend.Sequence(tuple(leaf(edge) for edge in nodes[q]))
        seq.name = names[q]
        builder.sequences.append(seq)
    builder.generate()
    builder.tm.gc()
    return builder.tm


def normalize(machine):
    """Same documented totalization and label order as the source-19 helper."""
    working = {q for q, bit in machine.states}
    missing = [(q, bit) for q in sorted(working) for bit in ("0", "1")
               if (q, bit) not in machine.states]
    require(missing == [("1.inc", "1")], "unexpected undefined-row convention")
    order = [machine.start] + sorted(working - {machine.start})
    labels = {q: i for i, q in enumerate(order)}
    labels["halt"] = len(order)
    lines = ["#! start 0"]
    for q in order:
        for bit in ("0", "1"):
            action = machine.states.get((q, bit))
            write, move, target = ((bit, "R", "halt") if action is None else action)
            lines.append(f"{labels[q]} {bit} {write} {move} {labels[target]}")
    return ("\n".join(lines) + "\n").encode(), labels, missing


def parse_table(raw, labels):
    """Parse the delivered numeric table without using Wade's parser."""
    require(all(type(v) is int for v in labels.values()), "noninteger state label")
    require(set(labels.values()) == set(range(len(labels))), "nonbijective labels")
    halt = labels["halt"]
    require(halt == len(labels) - 1, "halt label is not last")
    inverse = {number: name for name, number in labels.items()}
    lines = raw.decode().splitlines()
    require(lines and lines[0] == "#! start 0", "unexpected start directive")
    rows = {}
    for line in lines[1:]:
        match = re.fullmatch(r"(\d+) ([01]) ([01]) ([LR]) (\d+)", line)
        require(match is not None, f"invalid TM row {line!r}")
        q, bit, write, move, target = match.groups()
        q, target = int(q), int(target)
        require(0 <= q < halt and 0 <= target <= halt, "TM state outside label set")
        key = (inverse[q], bit)
        require(key not in rows, "duplicate TM transition")
        rows[key] = (write, move, inverse[target])
    require(len(rows) == 2 * halt, "binary TM table is not total")
    return rows


def extract_edges(table, nodes, names):
    """Invert all 418 candidate edges from the delivered table's actual rows.

    The arithmetic for break/continue depends on both the read bit and write
    symbol. It is adapted from source-08 reextract, separate from the generator.
    """
    byname = {name: q for q, name in names.items()}
    registers = {name: i for i, name in enumerate(REGISTERS)}
    checked = 0
    for q, edges in nodes.items():
        for bit, expected in enumerate(edges):
            write, move, target = table[names[q], str(bit)]
            if target in byname:
                actual = f"ENode {byname[target]}"
            elif target == "halt":
                actual = "EHalt"
            elif match := re.fullmatch(r"3\.(.*)\.(inc|decnz)", target):
                actual = f"{'EInc' if match[2] == 'inc' else 'EDecnz'} {registers[match[1]]}"
            elif target.startswith("6.break."):
                actual = f"EBreak {int(target.rsplit('.', 1)[1]) + (bit == 0)}"
            elif target.startswith("6.continue."):
                actual = ("EBreak 0" if bit == 0 and write == "1" else
                          f"EContinue {int(target.rsplit('.', 1)[1]) + bit}")
            else:
                raise ValueError(f"unexpected decision target {target}")
            require(actual == expected, f"decision edge mismatch at {q}/{bit}")
            direct = expected.split()[0] in ("ENode", "EInc", "EDecnz", "EHalt")
            wanted_write = str(bit) if direct else (
                "1" if expected == "EBreak 0" and bit == 0 else "0")
            require(write == wanted_write and move == ("R" if direct else "L"),
                    f"decision write/direction mismatch at {q}/{bit}")
            checked += 1
    return checked


def expect_rejection(action, label):
    try:
        action()
    except (AssertionError, ValueError, IndexError, KeyError, TypeError):
        return {"mutation": label, "rejected": True}
    raise ValueError(f"corrupted input accepted: {label}")


def negative_checks(engine, reference, candidate, cert, table, names):
    result = []
    for kind in ("wrong_operation", "wrong_successor", "wrong_initial",
                 "missing_pair", "duplicate_pair"):
        changed = copy.deepcopy(cert)
        if kind == "wrong_operation":
            changed["pairs"][0]["instruction"] = "EHalt"
        elif kind == "wrong_successor":
            changed["pairs"][0]["successors"][0] = len(changed["pairs"])
        elif kind == "wrong_initial":
            changed["initial"] = 1
        elif kind == "missing_pair":
            changed["pairs"].pop()
        else:
            changed["pairs"].append(copy.deepcopy(changed["pairs"][0]))
        result.append(expect_rejection(
            lambda: check_certificate(engine, reference, candidate, changed), kind))
    key = names[0], "0"
    write, move, target = table[key]
    for kind, replacement in (
            ("TM_wrong_write", (str(1 - int(write)), move, target)),
            ("TM_wrong_direction", (write, "L" if move == "R" else "R", target)),
            ("TM_wrong_target", (write, move, "halt"))):
        changed = dict(table)
        changed[key] = replacement
        result.append(expect_rejection(
            lambda: extract_edges(changed, candidate, names), kind))
    return result


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: the verbatim source-08 helper uses assertions")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT,
                        help="artifact package root (normally inferred)")
    args = parser.parse_args()
    root = args.root.resolve()
    data = root / "data/fusion"
    manifest = read_json(data / "sha256.json")
    for relative, expected in manifest.items():
        actual = hashlib.sha256((root / relative).read_bytes()).hexdigest()
        require(actual == expected, f"SHA-256 mismatch: {relative}")
    reference, _ = load_dag(data / "reference_dag.json")
    candidate, names = load_dag(data / "candidate_dag.json")
    cert = read_json(data / "rm_certificate.json")
    engine = load_engine()
    rm_result = check_certificate(engine, reference, candidate, cert)
    raw = (root / "machines/fusion/fused271.tm").read_bytes()
    labels = read_json(data / "labels.json")
    actual_table = parse_table(raw, labels)
    extracted = extract_edges(actual_table, candidate, names)
    generated, generated_labels, missing = normalize(compile_dag(candidate, names))
    require(generated == raw, "regenerated TM differs from delivered table")
    require(generated_labels == labels, "regenerated numeric labels differ")
    require((len(reference), len(candidate), len(actual_table), labels["halt"])
            == (284, 209, 542, 271), "unexpected artifact dimensions")
    mutations = negative_checks(engine, reference, candidate, cert, actual_table, names)
    print(json.dumps({
        "verified": True,
        "scope": "new fused reference versus compressed candidate; finite structural checks",
        "sha256_files_checked": len(manifest),
        "rm_certificate": rm_result,
        "TM": {"working_states": labels["halt"], "alphabet": [0, 1],
               "rows": len(actual_table), "start_state": 0, "halt_state": labels["halt"],
               "decision_edges_reextracted_from_delivered_table": extracted,
               "full_table_regeneration_identical": True,
               "totalized_upstream_missing_rows": missing,
               "sha256": hashlib.sha256(raw).hexdigest()},
        "negative_checks": mutations,
        "binary_compiler_correctness_proved": False,
        "ZFC_consistency_endpoint_proved": False,
        "new_state_record": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
