#!/usr/bin/env python3
"""Portable verification of the retained alternate 240-state layout.

The default check uses only the Python standard library and the explicitly
supplied tables/source files.  It recomputes the complete source segment
bisimulation and the exact blank initialization of both tables.  Optional
--runtime additionally uses the packaged symbolic engine; it never disables
input validation or modifies that engine's transition/proof rules.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
import time

PINS = {
    "baseline_table": "547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f",
    "baseline_sites": "74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d",
    "alternate_table": "9353a5a0baa1ea352579fbf09f8f2c789c7595bdb55854b1012f947f97666d2a",
    "alternate_sites": "2423356d29b08e03e71d39b665986f4794c19ad897f9493b707a7df7b33478f2",
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pinned(path, name):
    actual = digest(path)
    assert actual == PINS[name], ("Exact input pin mismatch", name, actual)
    return actual


def table(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith("#! start "):
            assert start is None
            start = int(line.split()[-1])
        elif line and not line.startswith("#"):
            q, b, w, d, target = line.split()
            q, b, w, target = map(int, (q, b, w, target))
            assert q >= 0 and target >= 0 and b in (0, 1) and w in (0, 1)
            assert d in ("L", "R") and (q, b) not in rows
            rows[q, b] = w, (1 if d == "R" else -1), target
    states = {q for q, _ in rows}
    assert start == 95 and 96 in states and 254 not in states
    assert len(states) == 240 and len(rows) == 480
    assert all((q, b) in rows for q in states for b in (0, 1))
    assert {t for _, _, t in rows.values()} - states == {254}
    return rows


class Source:
    def __init__(self, path):
        self.sites = json.loads(path.read_text())
        assert isinstance(self.sites, list) and len(self.sites) == 6455
        self.leaf = {}
        self.prefixes = set()
        for row in self.sites:
            assert isinstance(row, list) and len(row) == 3
            pc, op, arg = row
            assert isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {"0", "1"}
            assert pc not in self.leaf and op in ("CI", "CD", "CB", "CC", "CH")
            if op == "CH":
                assert arg is None
            elif op in ("CI", "CD"):
                assert type(arg) is int and 0 <= arg < 9
            else:
                assert type(arg) is int and arg >= 1
            self.leaf[pc] = op, arg
            self.prefixes.update(pc[:i] for i in range(len(pc)))
        assert not (self.prefixes & self.leaf.keys())
        assert len(self.prefixes) + 1 == len(self.leaf)
        assert all(p + b in self.prefixes or p + b in self.leaf for p in self.prefixes for b in "01")
        # Require the same serialization whose hash is pinned above.
        assert path.read_bytes() == (json.dumps(self.sites, indent=2) + "\n").encode()
        self.segment_cache = {}

    def contract(self, pc):
        while pc not in self.leaf:
            assert pc in self.prefixes
            pc += "0"
        return pc

    @staticmethod
    def increment(pc):
        return pc[:pc.rindex("0")] + "1" if "0" in pc else ""

    @staticmethod
    def strip(pc, bit, count):
        while count and pc:
            count -= pc[-1] == bit
            pc = pc[:-1]
        return pc

    def successor(self, pc, positive=False):
        op, arg = self.leaf[pc]
        if op == "CH":
            return None
        if op == "CI" or (op == "CD" and positive):
            return self.contract(self.increment(pc))
        if op in ("CD", "CB"):
            return self.contract(self.increment(self.strip(pc, "0", arg if op == "CB" else 1)))
        assert op == "CC"
        return self.contract(self.strip(pc, "1", arg))

    def segment(self, pc):
        if pc in self.segment_cache:
            return self.segment_cache[pc]
        initial = pc
        pc = self.contract(pc)
        seen = set()
        counts = [0] * 9
        while True:
            assert pc not in seen, ("Control-only cycle", pc)
            seen.add(pc)
            op, arg = self.leaf[pc]
            if op in ("CD", "CH"):
                result = tuple(counts), pc
                self.segment_cache[initial] = result
                return result
            if op == "CI":
                counts[arg] += 1
            pc = self.successor(pc)


def source_bisimulation(old, new):
    a, b = old.segment(""), new.segment("")
    assert a[0] == b[0]
    pairs = [(a[1], b[1])]
    index = {pairs[0]: 0}
    certificate = []
    for x, y in pairs:
        assert old.leaf[x] == new.leaf[y], ("Different decrement or halt", x, y)
        edges = []
        if old.leaf[x][0] != "CH":
            for positive in (False, True):
                aa = old.segment(old.successor(x, positive))
                bb = new.segment(new.successor(y, positive))
                assert aa[0] == bb[0], ("Different increment effects", x, y, positive)
                pair = aa[1], bb[1]
                if pair not in index:
                    index[pair] = len(pairs)
                    pairs.append(pair)
                edges.append(index[pair])
        certificate.append([x, y, *edges])
    assert len(certificate) == 1932
    return {"status": "ALL_EDGES_CHECKED", "initial_increment_counts": list(a[0]), "pairs": certificate}


def boot(rows):
    ones = set()
    q, head = 95, 0
    for _ in range(409691):
        assert q != 254
        write, direction, q = rows[q, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    expected = {-6, 176}
    p = 177
    for value in [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167:
        p += 1
        expected.update(range(p, p + value + 1))
        p += value + 1
    assert q == 96 and head == -5 and ones == expected and len(ones) == 351
    return {"steps": 409691, "state": q, "head": head, "one_positions": sorted(ones), "complete_zero_exterior": True}


def runtime_check(engine_path, old_table, old_source, new_table, new_source):
    sys.path.insert(0, str(engine_path.resolve().parent))
    spec = importlib.util.spec_from_file_location("alternate_layout_runtime", engine_path)
    assert spec and spec.loader
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    # Retain the engine's original baseline validation, including its exact
    # baseline source pin.  The alternate source has already passed the
    # corresponding structural/type checks and its own exact pin above.
    original_validation = engine.validate_inputs(old_table, old_source.sites)
    assert tuple(engine.r.PHY) == (6, 2, 0, 4, 3, 7, 8, 5, 1)
    started = time.monotonic()
    lemmas, blocks = engine.prove_blocks(new_table)
    count = symbolic_steps = 0
    for site in new_source.sites:
        for positive in ((False, True) if site[1] == "CD" else (False,)):
            answer = engine.case(new_table, lemmas, site, positive)
            count += 1
            symbolic_steps += answer["symbolic_steps"]
            if count % 1000 == 0:
                print("alternate runtime proved", count, "cases", flush=True)
    assert count == 8386
    return {
        "status": "UNIVERSAL_MATHEMATICAL_PASS",
        "cases": count,
        "symbolic_steps": symbolic_steps,
        "seconds": time.monotonic() - started,
        "checker_sha256": digest(engine_path),
        "helper_sha256": digest(Path(engine.r.__file__)),
        "baseline_engine_validation": original_validation,
        "alternate_input_validation": "Exact alternate source/table pins, full binary-tree and opcode validation, complete 240-state binary transition domain.",
        "scope": "All natural primary values, all natural additional gaps, arbitrary first spare value and arbitrary finite remaining spare list; whole tape. Mathematical checker, not a proof-assistant kernel theorem.",
        "blocks": blocks,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-table", type=Path, required=True)
    parser.add_argument("--baseline-sites", type=Path, required=True)
    parser.add_argument("--alternate-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, metavar="SYMBOLIC_RUNTIME_PY")
    args = parser.parse_args()
    assert __debug__ and not sys.flags.optimize, "Run without -O or PYTHONOPTIMIZE."
    alternate_table_path = args.alternate_dir / "machine_old.tm"
    alternate_sites_path = args.alternate_dir / "sites_logical.json"
    hashes = {
        "baseline_table": pinned(args.baseline_table, "baseline_table"),
        "baseline_sites": pinned(args.baseline_sites, "baseline_sites"),
        "alternate_table": pinned(alternate_table_path, "alternate_table"),
        "alternate_sites": pinned(alternate_sites_path, "alternate_sites"),
    }
    old_table, new_table = table(args.baseline_table), table(alternate_table_path)
    old_source, new_source = Source(args.baseline_sites), Source(alternate_sites_path)
    certificate = source_bisimulation(old_source, new_source)
    provided = args.alternate_dir / "source_bisimulation.json"
    assert json.loads(provided.read_text()) == certificate
    old_boot, new_boot = boot(old_table), boot(new_table)
    assert old_boot == new_boot
    report = {
        "status": "ALTERNATE_SOURCE_AND_EXACT_BOOT_PASS",
        "input_sha256": hashes,
        "verifier_sha256": digest(Path(__file__)),
        "working_states": 240,
        "source_leaves": len(new_source.sites),
        "maximum_depth": max(len(p) for p in new_source.leaf),
        "maximum_zero_run": max(max(map(len, p.split("1"))) for p in new_source.leaf),
        "source_bisimulation_pairs": len(certificate["pairs"]),
        "all_source_segment_edges_recomputed": True,
        "provided_source_certificate_matches": True,
        "blank_boot": new_boot,
        "runtime": "NOT_REQUESTED",
        "scope": "The default check proves source segment equivalence and exact blank initialization. The separate all-values symbolic runtime receipt supplies the table-to-source simulation; this default check does not infer it from finite tests.",
    }
    print("source bisimulation and both complete blank boots passed", flush=True)
    if args.runtime:
        report["runtime"] = runtime_check(args.runtime, old_table, old_source, new_table, new_source)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k not in ("blank_boot", "runtime")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
