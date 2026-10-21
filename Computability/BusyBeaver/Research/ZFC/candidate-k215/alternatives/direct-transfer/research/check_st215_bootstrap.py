#!/usr/bin/env python3
"""Independent ST215 blank-prefix and synthetic-AX bridge certificate.

Uses only the Python standard library and does not import a supplied checker.
Usage:
    python check_st215_bootstrap.py MACHINE SOURCE [CONTEXT_ROOT_SOURCE]

With no arguments, use ../machine/st215.native.tm and
../source/st215.sites.json relative to this script.
MACHINE is the append-0, start-0 literal native table.  SOURCE is the rotated
source.sites.json.  The optional third argument checks its complete control
graph against the unrotated short-transfer source.  Outputs a JSON receipt
beside this script.  The receipt contains the full sparse tape and the full
finite source trace, rather than a checksum-only claim.

The theorem-valued AX suffix, infinite scheduler credit and theorem compiler
are ordinary mathematical arguments, not consequences of this finite test.
"""

import hashlib
import json
import sys
from pathlib import Path


def interval_cfg(sites):
    first, end = {}, {}
    for i, (path, _, _) in enumerate(sites):
        for j in range(len(path) + 1):
            first.setdefault(path[:j], i)
            end[path[:j]] = i + 1
    size, graph = len(sites), []
    for i, (path, op, arg) in enumerate(sites):
        bit = "0" if op in ("CD", "CB") else "1"
        choices = [j for j, b in enumerate(path) if b == bit]
        depth = arg if op in ("CB", "CC") else 1
        if len(choices) < depth:
            target = 0
        else:
            prefix = path[:choices[-depth]]
            target = end[prefix] % size if bit == "0" else first[prefix]
        if op == "CH": edges = []
        elif op in ("CB", "CC"): edges = [target]
        elif op == "CD": edges = [target, (i + 1) % size]
        else: edges = [(i + 1) % size]
        graph.append((op, arg, edges))
    return graph


def binary_cut_cfg(sites):
    """Independent arithmetic-on-paths resolver; no interval endpoints used."""
    leaves = {p: i for i, (p, _, _) in enumerate(sites)}
    max_depth = max(map(len, leaves))

    def locate(prefix):
        word = prefix + "0" * max_depth
        for length in range(1, max_depth + 1):
            if word[:length] in leaves:
                assert "1" not in prefix[length:]
                return leaves[word[:length]]
        raise AssertionError(prefix)

    def successor(path):
        if not path: return ""
        return format((int(path, 2) + 1) % (1 << len(path)),
                      "0" + str(len(path)) + "b")

    def cut(path, bit, count):
        positions = [i for i, v in enumerate(path) if v == bit]
        return path[:positions[-count]] if len(positions) >= count else ""

    graph = []
    for path, op, arg in sites:
        if op == "CH": edges = []
        elif op == "CI": edges = [locate(successor(path))]
        elif op == "CD":
            edges = [locate(successor(cut(path, "0", 1))),
                     locate(successor(path))]
        elif op == "CB": edges = [locate(successor(cut(path, "0", arg)))]
        elif op == "CC": edges = [locate(cut(path, "1", arg))]
        else: raise AssertionError(op)
        graph.append((op, arg, edges))
    return graph


def count_dag(sites):
    leaves = {path: (op, arg) for path, op, arg in sites}
    unique = set()

    def build(path):
        value = leaves[path] if path in leaves else (build(path + "0"),
                                                    build(path + "1"))
        unique.add(value)
        return value

    build("")
    return len(unique)


def source_trace(graph):
    registers = [1, 0, 2, 0, 0, 0, 0, 0, 0]
    ordinal, trace = 25, []
    for step in range(178):
        trace.append({"step": step, "ordinal": ordinal,
                      "registers": registers.copy()})
        if step == 177: break
        op, arg, edges = graph[ordinal]
        if op == "CI":
            registers[arg] += 1
            ordinal = edges[0]
        elif op == "CD":
            positive = int(registers[arg] > 0)
            registers[arg] -= positive
            ordinal = edges[positive]
        elif op in ("CB", "CC"):
            ordinal = edges[0]
        else:
            raise AssertionError("Unexpected CH in the AX prefix")
    assert ordinal == 58
    assert registers == [1, 0, 0, 0, 0, 0, 0, 18, 0]
    return trace


def literal_blank_prefix(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"): continue
        q, read, write, direction, next_q = line.split()
        key = (int(q), int(read))
        assert key not in table
        assert direction in ("L", "R")
        assert int(read) in (0, 1) and int(write) in (0, 1)
        table[key] = (int(write), -1 if direction == "L" else 1, int(next_q))
    states = {q for q, _ in table}
    assert len(table) == 430 and len(states) == 215
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {nq for _, _, nq in table.values()} - states == {254}
    assert 254 not in states
    ones, head, state = set(), 0, 0
    for _ in range(70506):
        write, direction, next_q = table[state, int(head in ones)]
        if write: ones.add(head)
        else: ones.discard(head)
        head += direction
        state = next_q
    assert (state, head) == (84, -2)
    return states, ones


def expected_frame():
    logical = [1, 0, 0, 0, 0, 0, 0, 18, 0]
    physical_order = (6, 2, 0, 4, 3, 7, 8, 5, 1)
    physical = [None] * 9
    for i, j in enumerate(physical_order): physical[j] = logical[i]
    path = "00110010010110010"
    # Relative to the dispatcher head: guard at -1; program zone [0,63];
    # zero-gap header at 64; blocks use one zero then value+1 one-cells.
    ones = {-1, 64} | {i for i, bit in enumerate(path) if bit == "1"}
    position = 65
    for value in physical + [0] * 63:
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    return {cell - 2 for cell in ones}


def main():
    if len(sys.argv) == 1:
        packet = Path(__file__).resolve().parent.parent
        sys.argv.extend([str(packet / "machine/st215.native.tm"),
                         str(packet / "source/st215.sites.json")])
    if len(sys.argv) < 3:
        raise SystemExit(__doc__)
    machine, source = map(Path, sys.argv[1:3])
    sites = json.loads(source.read_text())
    graph = interval_cfg(sites)
    assert len(sites) == 4732
    assert graph == binary_cut_cfg(sites)
    assert sites[25] == ["0011001000000", "CD", 1]
    assert sites[58] == ["00110010010110010", "CI", 7]
    assert graph[4696] == ("CC", 3, [0])
    assert count_dag(sites) == 201
    source_hashes = {str(source): hashlib.sha256(source.read_bytes()).hexdigest()}
    old_agreement = None
    if len(sys.argv) > 3:
        old = Path(sys.argv[3])
        old_sites = json.loads(old.read_text())
        assert graph == interval_cfg(old_sites) == binary_cut_cfg(old_sites)
        old_agreement = len(graph)
        source_hashes[str(old)] = hashlib.sha256(old.read_bytes()).hexdigest()
    trace = source_trace(graph)
    states, ones = literal_blank_prefix(machine)
    assert ones == expected_frame()
    assert len(ones) == 100 and min(ones) == -3 and max(ones) == 225
    result = {
        "status": "PASS",
        "machine_sha256": hashlib.sha256(machine.read_bytes()).hexdigest(),
        "source_hashes": source_hashes,
        "nonhalting_states": len(states),
        "complete_native_table_rows": 2 * len(states),
        "independent_complete_cfg_agreement": len(graph),
        "unrotated_complete_cfg_agreement": old_agreement,
        "source_reduced_dag_nodes": count_dag(sites),
        "blank_prefix": {
            "binary_steps": 70506, "native_state": 84, "head": -2,
            "gap": 0, "header_cell": 62,
            "source_ordinal": 58, "source_path": sites[58][0],
            "logical_registers": trace[-1]["registers"],
            "spare_blocks": [0] * 63,
            "complete_one_cells": sorted(ones),
            "reconstructed_frame_matches_literal_tape": True,
        },
        "synthetic_ax_bridge": {
            "entry_ordinal": 25,
            "entry_registers": trace[0]["registers"],
            "source_steps": 177,
            "complete_trace": trace,
        },
        "scope": (
            "Exact finite literal blank run, whole sparse-tape frame, two "
            "independent complete source CFG reconstructions and finite AX "
            "prefix. Infinite whole-tape primitive simulation, all-natural "
            "AX semantics, protected credit, compiler and calculus "
            "calibration are separate mathematical premises."
        ),
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    output = Path(__file__).with_name("st215_bootstrap_independent.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "output": str(output),
                      "binary_steps": 70506, "source_bridge_steps": 177,
                      "cfg_leaves": len(graph), "dag_nodes": 201}, indent=2))


if __name__ == "__main__": main()
