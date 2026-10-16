#!/usr/bin/env python3
"""Rebracket the pinned axiom-emission word and check a finite RM bisimulation.

This is a compiler experiment, not a new sub-254-state ZFC machine.
It needs the pinned ProveIt snapshot and the public MIT-0 Wade backend.
The Python checker and binary TM compiler are not formalized in Lean.
Only files in the selected output directory are written.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from functools import cache
import hashlib
import importlib
import json
from pathlib import Path
import random
import re
import sys

UPSTREAM_COMMIT = "297ab8df7e5de329605c3875b4934643b371a5e3"
SOURCE_SHA256 = "538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3"
JSON_SHA256 = "bb884eacd778c79f4cc672ea4136db91e7d4ad7eb70ead7cc2892aba56566db5"
REGISTERS = ["nextproof", "topwff", "wffstack", "axiomcode", "param1", "param2",
             "scratch1", "scratch2", "prooflist"]
BACKEND_SHA256 = {
    "TMBuilder.py": "03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517",
    "tm.py": "2d00bf8c8324d8e9bc5639ba14e508091d854a7c93ecb96ab598f41c15ae9787",
    "tmdb.py": "4ccf4dab37438109a350d77259b5eb52e33ce110a954cd2d56a218e84e653526",
    "LICENSE.wade": "c1dffee77db98625debe39b47538e1d2f3b7956cbc7bcd6ed9363701b2177cfa",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def compile_dag(backend, nodes, names):
    """Public interface adapted from ProveIt's MIT-0 recover_wade_dag.py."""
    builder = backend.TMBuilder()
    registers = [builder.reg(name) for name in REGISTERS]
    def leaf(e):
        if e == "EHalt":
            return "halt"
        kind, value = e.split()
        n = int(value)
        if kind == "ENode":
            return n
        if kind == "EInc":
            return registers[n].inc
        if kind == "EDecnz":
            return registers[n].decnz
        return f"_{'break' if kind == 'EBreak' else 'continue'}.{n}"
    for q in range(len(nodes)):
        sequence = backend.Sequence(tuple(leaf(e) for e in nodes[q]))
        sequence.name = names[q]
        builder.sequences.append(sequence)
    builder.generate()
    builder.tm.gc()
    return builder.tm


def reextract(machine, nodes, names):
    """Invert all emitted decision edges, including read-sensitive controls."""
    byname = {name: q for q, name in names.items()}
    register_ids = {name: i for i, name in enumerate(REGISTERS)}
    for q, edges in nodes.items():
        for bit, expected in enumerate(edges):
            action = machine.states[names[q], str(bit)]
            target = action.nextstate
            if target in byname:
                actual = f"ENode {byname[target]}"
            elif target == "halt":
                actual = "EHalt"
            elif match := re.fullmatch(r"3\.(.*)\.(inc|decnz)", target):
                actual = f"{'EInc' if match[2] == 'inc' else 'EDecnz'} {register_ids[match[1]]}"
            elif target.startswith("6.break."):
                actual = f"EBreak {int(target.rsplit('.', 1)[1]) + (bit == 0)}"
            elif target.startswith("6.continue."):
                actual = ("EBreak 0" if bit == 0 and action.write == "1" else
                          f"EContinue {int(target.rsplit('.', 1)[1]) + bit}")
            else:
                raise ValueError(f"unexpected target {target}")
            assert actual == expected, (q, bit, actual, expected)
            direct = expected.split()[0] in ("ENode", "EInc", "EDecnz", "EHalt")
            expected_write = str(bit) if direct else ("1" if expected == "EBreak 0" and bit == 0 else "0")
            assert action.write == expected_write and action.direction == ("R" if direct else "L")


def bounder(nodes):
    @cache
    def bc(edge):
        kind, *rest = edge.split()
        n = int(rest[0]) if rest else 0
        if kind == "ENode":
            a, b = map(bc, nodes[n])
            return max(a[0] - 1, b[0], 0), max(a[1], b[1] - 1, 0)
        if kind == "EDecnz":
            return 1, 0
        if kind == "EBreak":
            return n, 0
        if kind == "EContinue":
            return 0, n
        return 0, 0
    return bc


def axiom_word(nodes):
    @cache
    def expand(q):
        if not 1 <= q <= 114:
            return (q,)
        assert all(e.startswith("ENode ") for e in nodes[q])
        return sum((expand(int(e.split()[1])) for e in nodes[q]), ())
    return expand(1)


def repair(word, seed, alpha):
    """Weighted Re-Pair; every committed replacement has >=2 occurrences."""
    rng = random.Random(seed)
    seq, grammar = list(word), []
    while True:
        counts = Counter(zip(seq, seq[1:]))
        choices = [(p, n) for p, n in counts.items() if n >= 2]
        if not choices:
            break
        pair = rng.choices([p for p, n in choices], [n ** alpha for p, n in choices])[0]
        new, i = [], 0
        while i < len(seq):
            if i + 1 < len(seq) and tuple(seq[i:i + 2]) == pair:
                new.append(300 + len(grammar))
                i += 2
            else:
                new.append(seq[i])
                i += 1
        if len(seq) - len(new) < 2:
            break
        grammar.append(pair)
        seq = new
    return seq, grammar


def transform(nodes, names, seq, grammar):
    """Intern binary productions; retain all non-axiom source nodes verbatim."""
    out = {q: es for q, es in nodes.items() if not 1 <= q <= 114}
    outnames = {q: s for q, s in names.items() if q in out}
    interner = {es: q for q, es in out.items()}
    next_id = max(nodes) + 1
    remap = {}
    def edge(v):
        return f"ENode {remap.get(v, v)}"
    def pair(a, b):
        nonlocal next_id
        es = (a, b)
        if es not in interner:
            interner[es] = next_id
            out[next_id] = es
            outnames[next_id] = f"axiom_grammar_{next_id}"
            next_id += 1
        return interner[es]
    for j, (a, b) in enumerate(grammar):
        remap[300 + j] = pair(edge(a), edge(b))
    root = remap.get(seq[-1], seq[-1])
    for v in reversed(seq[:-1]):
        root = pair(edge(v), f"ENode {root}")
    # Only node 149 enters the old axioms graph; this is checked below.
    for q, es in tuple(out.items()):
        out[q] = tuple(f"ENode {root}" if e == "ENode 1" else e for e in es)
    # Preserve root zero; eliminate unused helper nodes; renumber for Wade.
    seen, pending = set(), [0]
    while pending:
        q = pending.pop()
        if q in seen:
            continue
        seen.add(q)
        for e in out[q]:
            if e.startswith("ENode "):
                pending.append(int(e.split()[1]))
    ordered = [0] + sorted(seen - {0})
    ids = {q: j for j, q in enumerate(ordered)}
    converted = {ids[q]: tuple(f"ENode {ids[int(e.split()[1])]}" if e.startswith("ENode ") else e
                              for e in out[q]) for q in ordered}
    cnames = {ids[q]: outnames[q] for q in ordered}
    return converted, cnames, ids[root]


def expand_to_boundary(nodes, q, boundary):
    if q in boundary:
        return (q,)
    return sum((expand_to_boundary(nodes, int(e.split()[1]), boundary)
                for e in nodes[q]), ())


class PathMachine:
    """Exact finite instruction-site graph from RM.v path semantics.

    Paths are tuples of bits, MSB first, implicitly padded with zeros.
    Break/continue edges change no register and are contracted exactly.
    Every maximal contracted control path must terminate in an operation.
    """
    def __init__(self, nodes):
        self.nodes = nodes
        self.lookup = {}
        self.control_max = 0
        self.site_count = 0
        self.max_depth = 0
        def leaves(q, path):
            for bit, e in enumerate(nodes[q]):
                childpath = path + (bit,)
                if e.startswith("ENode "):
                    leaves(int(e.split()[1]), childpath)
                else:
                    self.lookup[childpath] = e
        leaves(0, ())
        self.site_count = len(self.lookup)
        self.max_depth = max(map(len, self.lookup))

    @staticmethod
    def inc(path):
        out = list(path)
        for j in reversed(range(len(out))):
            if out[j] == 0:
                out[j] = 1
                break
            out[j] = 0
        return tuple(out)

    @staticmethod
    def strip(path, bit, count):
        k = len(path)
        while count and k:
            k -= 1
            if path[k] == bit:
                count -= 1
        return path[:k]

    @cache
    def walk(self, path):
        q, used = 0, ()
        for depth in range(len(self.nodes) + 1):
            bit = path[depth] if depth < len(path) else 0
            used += (bit,)
            e = self.nodes[q][bit]
            if not e.startswith("ENode "):
                return used, e
            q = int(e.split()[1])
        raise ValueError("cyclic decoder or insufficient fuel")

    @cache
    def normalize(self, path):
        visited, steps = set(), 0
        while True:
            site, e = self.walk(path)
            if not (e.startswith("EBreak ") or e.startswith("EContinue ")):
                self.control_max = max(self.control_max, steps)
                return site, e
            if site in visited:
                raise ValueError("control-only loop; no finite contraction certificate")
            visited.add(site)
            kind, k = e.split()
            path = self.strip(site, int(kind == "EContinue"), int(k))
            if kind == "EBreak":
                path = self.inc(path)
            steps += 1

    def successors(self, site, e):
        if e == "EHalt":
            return []
        if e.startswith("EInc "):
            return [self.normalize(self.inc(site))]
        if e.startswith("EDecnz "):
            return [self.normalize(self.inc(self.strip(site, 0, 1))),
                    self.normalize(self.inc(site))]
        raise ValueError("unexpected instruction after normalization")


def bisimulation(oldnodes, newnodes):
    old, new = PathMachine(oldnodes), PathMachine(newnodes)
    initial = old.normalize(()), new.normalize(())
    states, todo, records = {initial: 0}, deque([initial]), []
    while todo:
        left, right = todo.popleft()
        sid = states[left, right]
        q1, e1 = left
        q2, e2 = right
        assert e1 == e2, (sid, e1, e2)
        succ = []
        for a, b in zip(old.successors(q1, e1), new.successors(q2, e2), strict=True):
            pair = a, b
            if pair not in states:
                states[pair] = len(states)
                todo.append(pair)
            succ.append(states[pair])
        assert sid == len(records)
        records.append({"old": "".join(map(str, q1)), "new": "".join(map(str, q2)),
                        "instruction": e1, "successors": succ})
    return {"initial": 0, "branch_order": "EDecnz: zero, positive", "pairs": records}, {
        "related_site_pairs": len(records),
        "instruction_counts": dict(Counter(r["instruction"].split()[0] for r in records)),
        "old_unfolded_sites": old.site_count, "new_unfolded_sites": new.site_count,
        "old_max_path_length": old.max_depth, "new_max_path_length": new.max_depth,
        "old_max_contracted_control_steps": old.control_max,
        "new_max_contracted_control_steps": new.control_max,
        "all_reachable_operation_labels_match": True,
        "both_decrement_branches_checked": True,
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    inputs = p.add_mutually_exclusive_group(required=True)
    inputs.add_argument("--repo", type=Path)
    inputs.add_argument("--inputs", type=Path,
                        help="portable input directory: source_dag.json and backend/")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--seed", type=int, default=341)
    p.add_argument("--alpha", type=int, default=4)
    args = p.parse_args()
    origin, output = (args.repo or args.inputs).resolve(), args.output.resolve()
    if output == origin or origin in output.parents:
        p.error("output must be outside the source input directory")
    output.mkdir(parents=True, exist_ok=True)
    if args.repo:
        source = (origin / "lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v").read_bytes()
        assert sha(source) == SOURCE_SHA256
        matches = re.findall(r"\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)\s+\(\* (.*?) \*\)",
                             source.decode())
        nodes = {int(n): (a, b) for n, a, b, name in matches}
        names = {int(n): name for n, a, b, name in matches}
        backend_source = origin / "lib/jeff-busy-beaver-zfc254/ZF/generator"
    else:
        raw = (origin / "source_dag.json").read_bytes()
        assert sha(raw) == JSON_SHA256
        data = json.loads(raw)
        assert data["source_sha256"] == SOURCE_SHA256 and data["root"] == 0
        nodes = {int(n): tuple(es) for n, es in data["nodes"].items()}
        names = {int(n): s for n, s in data["names"].items()}
        backend_source = origin / "backend"
    assert set(nodes) == set(names) == set(range(219)) and names[0] == "main().0"
    assert [(q, e) for q, es in nodes.items() if not 1 <= q <= 114 for e in es
            if e.startswith("ENode ") and 1 <= int(e.split()[1]) <= 114] == [(149, "ENode 1")]
    word = axiom_word(nodes)
    bc = bounder(nodes)
    assert all(bc(f"ENode {q}") == (0, 0) for q in set(word))
    seq, grammar = repair(word, args.seed, args.alpha)
    newnodes, newnames, newroot = transform(nodes, names, seq, grammar)
    assert bounder(newnodes)("ENode 0") == (0, 0)
    cert, stats = bisimulation(nodes, newnodes)
    write_json(output / "rm_bisimulation.json", cert)
    write_json(output / "rebracketed_dag.json", {"root": 0, "axioms_root": newroot,
                                               "nodes": newnodes, "names": newnames})
    backend_dir = output / "backend"
    backend_dir.mkdir(exist_ok=True)
    for filename in ("TMBuilder.py", "tm.py", "tmdb.py", "LICENSE.wade"):
        data = (backend_source / filename).read_bytes()
        assert sha(data) == BACKEND_SHA256[filename]
        (backend_dir / filename).write_bytes(data)
    sys.path.insert(0, str(backend_dir))
    backend = importlib.import_module("TMBuilder")
    machine = compile_dag(backend, newnodes, newnames)
    reextract(machine, newnodes, newnames)
    table = output / "rebracketed_wade.tm"
    machine.save(str(table))
    working = {q for q, _ in machine.states}
    framework = {q for q in working if q[0].isdigit()}
    ordered = [machine.start] + sorted(working - {machine.start})
    numeric = {q: i for i, q in enumerate(ordered)}
    halt = len(ordered)
    total_rows = ["#! start 0"]
    for q in ordered:
        for b in ("0", "1"):
            a = machine.states.get((q, b))
            if a is None:
                w, d, target = b, "R", halt
            else:
                w, d, target = a.write, a.direction, numeric.get(a.nextstate, halt)
            total_rows.append(f"{numeric[q]} {b} {w} {d} {target}")
    numeric_table = output / "rebracketed_wade_total.tm"
    numeric_table.write_text("\n".join(total_rows) + "\n")
    write_json(output / "state_names.json", {"halt": halt, "names": ordered})
    evidence = {
        "source_commit": "6594795e9db81637c30959e42b3bcfc9eb77722f",
        "upstream_commit": UPSTREAM_COMMIT,
        "source_Dag254_sha256": SOURCE_SHA256,
        "portable_source_dag_json_sha256": JSON_SHA256,
        "backend_sha256": BACKEND_SHA256,
        "experiment": "axiom word Re-Pair with exact finite RM operation bisimulation",
        "seed": args.seed, "weight_exponent": args.alpha,
        "original_axiom_nodes": 114, "axiom_word_length": len(word),
        "distinct_axiom_helpers": len(set(word)),
        "all_helpers_break_continue_closed": True,
        "new_grammar_productions": len(grammar), "new_residual_word_length": len(seq),
        "original_decision_states": len(nodes), "decision_states": len(newnodes),
        "framework_states": len(framework), "working_states": len(working),
        "transition_rows": len(machine.states),
        "missing_transition_rows": [[q, b] for q in sorted(working) for b in ("0", "1")
                                    if (q, b) not in machine.states],
        "terminal_targets": sorted({a.nextstate for a in machine.states.values()} - working),
        "emitted_DAG_reextracted_exactly": True,
        "rm_bisimulation": stats,
        "rm_bisimulation_sha256": sha((output / "rm_bisimulation.json").read_bytes()),
        "machine_sha256": sha(table.read_bytes()),
        "totalized_numeric_machine_sha256": sha(numeric_table.read_bytes()),
        "totalized_transition_rows": 2 * len(working),
        "missing_row_normalization": "write read symbol, move right, halt; adds no working state",
        "Lean_bisimulation_checked": False, "binary_TM_compiler_proved": False,
        "sub_254_record_claimed": False,
    }
    write_json(output / "rebracketing_evidence.json", evidence)
    print(json.dumps(evidence, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
