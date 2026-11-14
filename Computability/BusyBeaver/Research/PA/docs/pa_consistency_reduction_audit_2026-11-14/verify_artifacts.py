#!/usr/bin/env python3
"""Independently verify the packaged physical machine artifacts.

Uses only Python's standard library. It does not import the inherited compiler
or symbolic executor, rerun the symbolic proof procedures, or assert a PA
consistency equivalence. All finite startup tapes are checked cell for cell.
"""
from __future__ import annotations

from collections import deque
import hashlib
import json
from pathlib import Path
import sys
from typing import Any


ROOT = Path(__file__).resolve().parent
COMBINATIONS = ROOT / "reduction_agent" / "combination_study"
RESULTS = COMBINATIONS / "results"
OUTPUT = ROOT / "evidence" / "artifact_verification.json"
EXPECTED_NAMES = (
    "diagonal_mp_h",
    "diagonal_mp_h_short_neg",
    "separate_mp_h",
    "separate_mp_h_short_neg",
)
EXPECTED_COUNTS = {
    "diagonal_mp_h": (196, 3677, 4785),
    "diagonal_mp_h_short_neg": (197, 3461, 4497),
    "separate_mp_h": (196, 3650, 4750),
    "separate_mp_h_short_neg": (197, 3434, 4462),
}
STARTUP_STEPS = 58154
ROOT_NATIVE_STATE = 84
EXPECTED_HEAD = -2
HEADER_DISTANCE = 48
PHYSICAL_SEED = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def parse_table(path: Path, expected_start: int) -> dict[tuple[int, int], tuple[int, int, int]]:
    """Parse the literal five-column format without a compiler dependency."""
    rows: dict[tuple[int, int], tuple[int, int, int]] = {}
    declared_starts: list[int] = []
    for number, raw in enumerate(path.read_text(encoding="ascii").splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#! start "):
            fields = line.split()
            require(len(fields) == 3, f"{relative(path)}:{number}: invalid start directive")
            declared_starts.append(int(fields[2]))
            continue
        if line.startswith("#"):
            continue
        fields = line.split()
        require(len(fields) == 5, f"{relative(path)}:{number}: expected five fields")
        q, read, write, direction, target = fields
        q, read, write, target = map(int, (q, read, write, target))
        require(q >= 0 and target >= 0, f"{relative(path)}:{number}: negative state")
        require(read in (0, 1) and write in (0, 1), f"{relative(path)}:{number}: nonbinary symbol")
        require(direction in ("L", "R"), f"{relative(path)}:{number}: invalid direction")
        key = q, read
        require(key not in rows, f"{relative(path)}:{number}: duplicate row {key}")
        rows[key] = write, (-1 if direction == "L" else 1), target
    require(bool(rows), f"{relative(path)}: empty table")
    require(declared_starts in ([], [expected_start]), f"{relative(path)}: inconsistent start")
    if path.name == "machine.native.tm":
        require(declared_starts == [expected_start], f"{relative(path)}: missing native start")
    states = {q for q, _ in rows}
    require(expected_start in states, f"{relative(path)}: undefined initial state")
    require(set(rows) == {(q, b) for q in states for b in (0, 1)},
            f"{relative(path)}: partial binary transition function")
    return rows


def check_domain(rows: dict, start: int, halt: int, expected_states: set[int], name: str) -> dict:
    states = {q for q, _ in rows}
    require(states == expected_states, f"{name}: wrong working-state domain")
    require(halt not in states, f"{name}: halt is also a working state")
    destinations = {transition[2] for transition in rows.values()}
    require(destinations - states == {halt}, f"{name}: undefined destination or missing halt")
    reached = {start}
    pending = deque([start])
    while pending:
        q = pending.popleft()
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target != halt and target not in reached:
                reached.add(target)
                pending.append(target)
    require(reached == states, f"{name}: graph-unreachable working states")
    halting_rows = sorted([q, b] for (q, b), (_, _, target) in rows.items() if target == halt)
    require(len(halting_rows) == 1, f"{name}: expected one transition to the distinct halt")
    return {"working_states": len(states), "rows": len(rows),
            "graph_reachable_working_states": len(reached), "start": start,
            "halt": halt, "halting_rows": halting_rows}


def verify_source(sites: list[dict], name: str) -> dict:
    """Reconstruct the complete binary source tree and its ordinal CFG."""
    require(isinstance(sites, list) and len(sites) > 25, f"{name}: invalid source list")
    trie: dict = {}
    paths: list[str] = []
    for ordinal, site in enumerate(sites):
        require(site.get("ordinal") == ordinal, f"{name}: noncanonical source ordinal")
        path = site.get("path")
        require(isinstance(path, str) and bool(path) and set(path) <= {"0", "1"},
                f"{name}: invalid binary source path")
        current = trie
        for bit in path:
            require("leaf" not in current, f"{name}: overlapping source paths")
            current = current.setdefault(bit, {})
        require(not current, f"{name}: duplicate or overlapping source path")
        current["leaf"] = ordinal
        paths.append(path)
    require(paths == sorted(paths), f"{name}: source is not in binary-tree ordinal order")
    stack = [trie]
    while stack:
        node = stack.pop()
        if "leaf" in node:
            require(set(node) == {"leaf"}, f"{name}: malformed source leaf")
        else:
            require(set(node) == {"0", "1"}, f"{name}: nonfull binary source tree")
            stack.extend((node["0"], node["1"]))

    def locate(prefix: str) -> int:
        current = trie
        for position, bit in enumerate(prefix):
            if "leaf" in current:
                require("1" not in prefix[position:], f"{name}: stray successor suffix")
                return current["leaf"]
            current = current[bit]
        while "leaf" not in current:
            current = current["0"]
        return current["leaf"]

    def after(prefix: str) -> int:
        position = prefix.rfind("0")
        require(position >= 0, f"{name}: source control exits the tree")
        return locate(prefix[:position] + "1")

    def cut(prefix: str, bit: str, count: int) -> str:
        positions = [i for i, value in enumerate(prefix) if value == bit]
        require(len(positions) >= count, f"{name}: insufficient control depth")
        return prefix[:positions[-count]]

    contracts = 0
    for site in sites:
        path, op, arg = site["path"], site["op"], site["arg"]
        if op in ("inc", "dec"):
            require(type(arg) is int and 0 <= arg < 9, f"{name}: invalid register index")
            if op == "inc":
                expected = [op, arg, after(path)]
                contracts += 1
            else:
                expected = [op, arg, after(cut(path, "0", 1)), after(path)]
                contracts += 2
        elif op in ("breakTo", "continueTo"):
            require(type(arg) is int and arg > 0, f"{name}: invalid jump depth")
            destination = after(cut(path, "0", arg)) if op == "breakTo" else locate(cut(path, "1", arg))
            expected = ["jump", destination]
            contracts += 1
        else:
            require(op == "halt" and arg is None, f"{name}: invalid source instruction")
            expected = ["halt"]
            contracts += 1
        require(site.get("instruction") == expected, f"{name}: CFG mismatch at site {site['ordinal']}")
    require(sites[25]["instruction"] == ["dec", 8, 27, 26], f"{name}: changed clean-seed source site")
    return {"source_sites": len(sites), "branch_contracts_from_source": contracts,
            "full_binary_tree": True, "independently_reconstructed_CFG": True,
            "seed_ordinal": 25, "seed_path": paths[25], "maximum_path_length": max(map(len, paths))}


def simulate_blank(rows: dict, root_state: int, halt: int, path: str, name: str) -> dict:
    q, head, ones = 0, 0, set()
    for step in range(STARTUP_STEPS):
        require(q != halt, f"{name}: halted before startup endpoint at step {step}")
        write, direction, q = rows[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    expected = {EXPECTED_HEAD - 1, EXPECTED_HEAD + HEADER_DISTANCE}
    expected.update(EXPECTED_HEAD + i for i, bit in enumerate(path) if bit == "1")
    position = EXPECTED_HEAD + HEADER_DISTANCE + 1
    for value in PHYSICAL_SEED:
        expected.update(range(position + 1, position + value + 2))
        position += value + 2
    require(q == root_state, f"{name}: wrong startup endpoint state")
    require(head == EXPECTED_HEAD, f"{name}: wrong startup endpoint head")
    require(ones == expected, f"{name}: complete startup tape differs in {len(ones ^ expected)} cells")
    return {"steps": STARTUP_STEPS, "dense_state": q, "native_state": ROOT_NATIVE_STATE,
            "head": head, "header_distance": HEADER_DISTANCE, "physical_register_file": PHYSICAL_SEED,
            "one_cells": len(ones), "entire_tape_equal": True, "source_seed_ordinal": 25,
            "source_seed_path": path}


def verify_combination(name: str, aggregate: dict[str, dict]) -> dict:
    folder = RESULTS / name
    receipt = read_json(folder / "receipt.json")
    require(receipt == aggregate[name], f"{name}: aggregate and individual receipts disagree")
    require(receipt.get("name") == name, f"{name}: receipt identity mismatch")
    labels = read_json(folder / "labels.json")
    require(isinstance(labels, list) and all(type(q) is int and q >= 0 for q in labels),
            f"{name}: invalid native-label list")
    n = len(labels) - 1
    require(n >= 196, f"{name}: an unexpected sub-196 construction needs separate review")
    require(len(set(labels)) == len(labels) and labels[0] == 74 and labels[-1] == 254,
            f"{name}: invalid start/halt label conjugacy")
    require(ROOT_NATIVE_STATE in labels[:-1], f"{name}: missing root control")
    dense = parse_table(folder / "machine.tm", 0)
    native = parse_table(folder / "machine.native.tm", 74)
    dense_domain = check_domain(dense, 0, n, set(range(n)), name + " dense")
    native_domain = check_domain(native, 74, 254, set(labels[:-1]), name + " native")
    for (q, bit), (write, direction, target) in dense.items():
        require(native[labels[q], bit] == (write, direction, labels[target]),
                f"{name}: row-by-row label conjugacy failed at {(q, bit)}")
    require(receipt.get("states") == n and receipt.get("rows") == 2 * n,
            f"{name}: receipt state/row count mismatch")
    for filename, key in (("machine.tm", "dense_sha256"), ("machine.native.tm", "native_sha256")):
        require(sha256(folder / filename) == receipt.get(key), f"{name}: {key} mismatch")
    sites = read_json(folder / "sites.json")
    source = verify_source(sites, name)
    require(receipt.get("source_sites") == source["source_sites"], f"{name}: source count mismatch")
    symbolic = receipt.get("symbolic", {})
    require(symbolic.get("ok") is True, f"{name}: supplied symbolic receipt is not a pass")
    require(symbolic.get("contracts") == source["branch_contracts_from_source"],
            f"{name}: supplied symbolic case count differs from source")
    actual_counts = n, len(sites), source["branch_contracts_from_source"]
    require(actual_counts == EXPECTED_COUNTS[name], f"{name}: unexpected packaged construction census")
    startup = simulate_blank(dense, labels.index(ROOT_NATIVE_STATE), n, sites[25]["path"], name)
    old_startup = receipt.get("startup", {})
    require(old_startup.get("steps") == STARTUP_STEPS and old_startup.get("state") == ROOT_NATIVE_STATE
            and old_startup.get("head") == EXPECTED_HEAD and old_startup.get("source_ordinal") == 25
            and old_startup.get("path") == list(map(int, sites[25]["path"]))
            and old_startup.get("all_cells_equal") is True, f"{name}: startup receipt mismatch")
    return {"name": name, "status": "PASS", "dense_domain": dense_domain,
            "native_domain": native_domain, "all_rows_conjugate": True, "source": source,
            "independent_blank_startup": startup,
            "input_sha256": {filename: sha256(folder / filename) for filename in
                             ("machine.tm", "machine.native.tm", "labels.json", "sites.json", "receipt.json")},
            "symbolic_verification_replayed": False}


def verify_inventory_summary() -> dict:
    folder = ROOT / "comparison_agent"
    inventory = read_json(folder / "inventory.json")
    summary = read_json(folder / "summary.json")
    tables, archives = inventory["tables"], inventory["archives"]
    selected195 = [table for table in tables if table["states"] == 195]
    calculated = {
        "top_level_archives": len(archives),
        "table_occurrences": len(tables),
        "raw_table_byte_strings": len({table["sha256"] for table in tables}),
        "distinct_labeled_transition_functions": len({table["table_sha256"] for table in tables}),
        "literal195_occurrences": len(selected195),
        "literal195_byte_strings": len({table["sha256"] for table in selected195}),
    }
    for key, value in calculated.items():
        require(summary.get(key) == value, f"corpus summary count differs from inventory: {key}")
    require(inventory.get("snapshot") == summary.get("snapshot"), "corpus snapshot mismatch")
    require(inventory.get("skipped_archives") == [], "inventory records skipped archives")
    require(len({archive["archive"] for archive in archives}) == len(archives), "duplicate archive census entry")
    require(summary.get("all_manuscripts_sub196_result") is False, "unexpected claimed sub-196 result")
    grouped = [index for group in inventory["graph_groups"].values() for index in group]
    require(sorted(grouped) == list(range(len(tables))), "graph-group inventory is not a partition")
    return {"status": "PASS", "calculated_counts": calculated, "snapshot": summary["snapshot"],
            "scope": "Independent arithmetic cross-check of saved inventory metadata; the original archive bytes are not re-extracted by this verifier.",
            "input_sha256": {name: sha256(folder / name) for name in ("inventory.json", "summary.json")}}


def main() -> int:
    report: dict[str, Any] = {
        "status": "FAIL",
        "verifier": "verify_artifacts.py",
        "verifier_sha256": sha256(Path(__file__)),
        "scope": "Independent table/domain/reachability/conjugacy checks, reconstructed source CFGs, exact full-tape finite startups, receipt counts, and corpus-metadata arithmetic. No symbolic-proof replay, nonhalting conclusion, new PA theorem, or sub-196 construction is asserted.",
    }
    try:
        aggregate_list = read_json(RESULTS / "receipt.json")
        aggregate = {receipt["name"]: receipt for receipt in aggregate_list}
        require(len(aggregate) == len(aggregate_list) == len(EXPECTED_NAMES), "wrong aggregate receipt census")
        require(set(aggregate) == set(EXPECTED_NAMES), "unexpected aggregate construction identities")
        report["machines"] = [verify_combination(name, aggregate) for name in EXPECTED_NAMES]
        report["corpus_summary"] = verify_inventory_summary()
        report["status"] = "PASS"
    except Exception as error:
        report["error"] = f"{type(error).__name__}: {error}"
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if report["status"] != "PASS":
        print(report["error"], file=sys.stderr)
        return 1
    print(json.dumps({"status": "PASS", "machines": len(report["machines"]),
                      "independent_blank_startup_steps_per_machine": STARTUP_STEPS,
                      "corpus_summary": report["corpus_summary"]["calculated_counts"],
                      "evidence": relative(OUTPUT)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
