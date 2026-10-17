#!/usr/bin/env python3
"""Independent finite audit of a supplied register-program DAG and binary TM.

The emitter/search driver is never imported. This reconstructs every leaf,
guard, and carry/strip successor, checks the entire affine suite using the
attributed original executor, and performs literal whole-tape executions.
Affine claims remain conditional on the four original Box contracts. Literal
samples are finite facts, not an unbounded compiler-correctness proof. The
semantic equivalence of the supplied source transformation is outside scope.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

BASELINE_SHA = '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
STRICT_SHA = 'da3cc5f3f5f4d5ebde71c9f353c9ddead010d9c8529d8ae97b6e9ccfe1ba21ce'
LOGICAL_TO_PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
BOX_STATES = {0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56,
              59, 60, 63, 64, 69, 73, 75, 83, 85, 95, 97, 109, 112, 131}
BOX_ROWS = {(q, b) for q in BOX_STATES for b in (0, 1)} - {(3, 0)}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def parse_table(raw):
    result = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, target = line.split()
        key = int(q), int(b)
        assert key not in result
        result[key] = int(w), direction, int(target)
    states = {q for q, _ in result}
    assert 64 in states and 96 in states and 254 not in states
    assert set(result) == {(q, b) for q in states for b in (0, 1)}
    assert all(w in (0, 1) and d in ('L', 'R') and t in states | {254}
               for w, d, t in result.values())
    return result, states


def reconstruct(raw):
    data = json.loads(raw)
    nodes = {int(q): tuple(tuple(edge) for edge in pair)
             for q, pair in data['nodes'].items()}
    root = data['root']
    assert all(len(pair) == 2 for pair in nodes.values())
    used_nodes = set()
    leaves = []

    def visit(q, prefix, active):
        assert q not in active and q in nodes
        used_nodes.add(q)
        for b, edge in enumerate(nodes[q]):
            path = prefix + str(b)
            op = edge[0]
            assert op in ('N', 'I', 'D', 'B', 'C', 'H')
            if op == 'N':
                assert len(edge) == 2
                visit(edge[1], path, active | {q})
            else:
                assert len(edge) == (1 if op == 'H' else 2)
                argument = edge[1] if len(edge) == 2 else None
                if op in ('I', 'D'):
                    assert 0 <= argument < 9
                if op in ('B', 'C'):
                    assert argument >= 0
                leaves.append((path, op, argument))

    visit(root, '', set())
    assert used_nodes == set(nodes)
    lookup = {p: i for i, (p, _, _) in enumerate(leaves)}
    assert len(lookup) == len(leaves)

    def decode(pc):
        q, position, path = root, 0, ''
        while True:
            bit = int(pc[position]) if position < len(pc) else 0
            position += 1
            path += str(bit)
            edge = nodes[q][bit]
            if edge[0] != 'N':
                assert '1' not in pc[position:]
                return lookup[path]
            q = edge[1]

    cases = []
    for site, (pc, op, argument) in enumerate(leaves):
        for zero in ((True, False) if op == 'D' else (None,)):
            nxt, overflow = successor(pc, op, argument, zero)
            target = None if op == 'H' else decode(nxt)
            cases.append((site, pc, op, argument, zero, nxt, overflow, target))
    return nodes, root, leaves, cases, decode('')


def successor(pc, op, argument, zero):
    """Explicit list carry and suffix consumption, without emitter helpers."""
    if op == 'H':
        return '', False
    bits = [int(c) for c in pc]
    if op == 'B' or op == 'D' and zero or op == 'C':
        wanted = 1 if op == 'C' else 0
        remaining = argument if op in ('B', 'C') else 1
        while bits and remaining:
            remaining -= bits.pop() == wanted
    if op == 'C':
        return ''.join(map(str, bits)).rstrip('0'), False
    index = len(bits) - 1
    while index >= 0 and bits[index] == 1:
        bits[index] = 0
        index -= 1
    if index < 0:
        return '', True
    bits[index] = 1
    return ''.join(map(str, bits)).rstrip('0'), False


def frame(pc, gap, primary, spares, head):
    assert len(pc) <= gap and len(primary) == 9
    ones = {head - 1, head + gap}
    ones.update(head + i for i, b in enumerate(pc) if b == '1')
    position = head + gap + 1
    for value in primary + spares:
        assert value >= 0
        position += 1
        for _ in range(value + 1):
            ones.add(position)
            position += 1
    return ones


def literal(table, q, head, ones, limit, goal=None, halting=False):
    """Execute literal binary rows; compare the entire finite support."""
    used = set()
    intermediate = 0
    for steps in range(1, limit + 1):
        row = q, int(head in ones)
        used.add(row)
        write, direction, q = table[row]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += 1 if direction == 'R' else -1
        if q == 254:
            assert halting, ('unexpected halt', steps)
            return steps, q, head, ones, used, intermediate
        if goal is not None and q == 96:
            if (head, ones) == goal:
                return steps, q, head, ones, used, intermediate
            intermediate += 1
    if goal is not None or halting:
        raise AssertionError(('literal fuel exhausted', limit))
    return limit, q, head, ones, used, intermediate


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--source', type=Path, required=True)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--literal-variants', type=int, default=3, choices=(0, 1, 2, 3))
    ap.add_argument('--literal-fuel', type=int, default=200000)
    args = ap.parse_args()
    assert __debug__
    begun = time.monotonic()
    source_raw, table_raw = args.source.read_bytes(), args.table.read_bytes()
    table, states = parse_table(table_raw)
    baseline_path = args.repo / 'Computability/BusyBeaver/Research/ZFC/candidate-permutation252/zfc_permutation252_old.tm'
    baseline_raw = baseline_path.read_bytes()
    assert sha(baseline_raw) == BASELINE_SHA
    baseline, _ = parse_table(baseline_raw)
    assert len(BOX_ROWS) == 55
    assert all(table[row] == baseline[row] for row in BOX_ROWS)
    nodes, root, leaves, cases, initial = reconstruct(source_raw)
    strict_path = args.repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    strict_raw = strict_path.read_bytes()
    assert sha(strict_raw) == STRICT_SHA
    sys.modules['cost_search'] = SimpleNamespace()
    spec = importlib.util.spec_from_file_location('modified_independent_strict', strict_path)
    strict = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(strict)
    string_table = {(str(q), b): (w, d, str(t)) for (q, b), (w, d, t) in table.items()}
    symbolic_rows = set()

    class Tracking(dict):
        def __getitem__(self, key):
            symbolic_rows.add((int(key[0]), key[1]))
            return super().__getitem__(key)

    string_table = Tracking(string_table)
    min_literal, max_rule_count, rule_totals = 10**9, 0, Counter()
    kind_counts = Counter()
    for site, pc, op, argument, zero, nxt, overflow, target_site in cases:
        physical = LOGICAL_TO_PHYSICAL[argument] if op in ('I', 'D') else argument
        effect = ('inc', physical) if op == 'I' else ('dec', physical) if op == 'D' and not zero else None
        expected = [('b', int(b)) for b in nxt] + [('r', 0, 1, 40 + overflow - len(nxt)), ('b', 1), ('box', ('plain', effect))]
        counts, literal_count = strict.run(string_table, pc, (physical, zero) if op == 'D' else None,
                                           strict.canon([('b', 1)], expected), halt=op == 'H', fuel=1000)
        assert literal_count > 0
        min_literal = min(min_literal, literal_count)
        max_rule_count = max(max_rule_count, sum(counts.values()))
        rule_totals.update(counts)
        kind_counts[op] += 1
    print('AFFINE PASS', len(cases), 'cases', flush=True)
    boot = literal(table, 64, 0, set(), 82552)
    spares = [0] * 65
    spares[8] = 1
    expected_boot = frame('', 40, [0] * 9, spares, 2)
    assert (boot[1], boot[2], boot[3]) == (96, 2, expected_boot)
    assert len(expected_boot) == 77
    first9 = literal(table, 64, 0, set(), 9)
    assert (first9[1], first9[2], first9[3]) == (1, 7, {8})
    variants = [(40, [0] * 9, []),
                (57, [0, 1, 2, 0, 3, 1, 2, 4, 0], [0, 2, 0]),
                (97, [5, 0, 2, 4, 1, 3, 0, 2, 1], [2, 1, 3])][:args.literal_variants]
    literal_counts = Counter()
    literal_rows = set(boot[4])
    max_steps, total_steps, max_intermediate, examples = 0, 0, 0, []
    for variant, (gap, values, tail) in enumerate(variants):
        for index, (site, pc, op, argument, zero, nxt, overflow, target_site) in enumerate(cases):
            primary = values.copy()
            physical = LOGICAL_TO_PHYSICAL[argument] if op in ('I', 'D') else argument
            if op == 'D':
                primary[physical] = 0 if zero else max(1, primary[physical])
            after, spare_after = primary.copy(), tail.copy()
            if op == 'I':
                after[physical] += 1
            elif op == 'D' and not zero:
                after[physical] -= 1
                spare_after.append(0)
            output_head = -int(overflow)
            goal = (output_head, frame(nxt, gap + overflow, after, spare_after, output_head))
            sample = literal(table, 96, 0, frame(pc, gap, primary, tail, 0),
                             args.literal_fuel, goal=goal if op != 'H' else None, halting=op == 'H')
            steps, q, head, ones, used, intermediate = sample
            literal_rows.update(used)
            literal_counts[op] += 1
            max_steps = max(max_steps, steps)
            total_steps += steps
            max_intermediate = max(max_intermediate, intermediate)
            if index in (0, len(cases) - 1):
                examples.append(dict(variant=variant, case=index, pc=pc, operation=op,
                                     steps=steps, intermediate_dispatch_visits=intermediate))
        print('LITERAL PASS variant', variant, len(cases), 'cases', flush=True)
    reachable = set()
    todo = deque([64])
    while todo:
        q = todo.popleft()
        if q in reachable or q == 254:
            continue
        reachable.add(q)
        todo.extend(table[q, b][2] for b in (0, 1))
    result = dict(status='PASS', scope=__doc__, source_sha256=sha(source_raw), table_sha256=sha(table_raw),
                  checker_sha256=sha(Path(__file__).read_bytes()), baseline_sha256=BASELINE_SHA, strict_sha256=STRICT_SHA,
                  working_states=len(states), rows=len(table), start_state=64, halt_state=254,
                  unchanged_protected_box_rows=55, source_dag_nodes=len(nodes), source_root=root,
                  source_leaves=len(leaves), source_guarded_cases=len(cases), source_max_leaf_depth=max(map(lambda x: len(x[0]), leaves)),
                  source_initial_leaf=leaves[initial], all_nonhalt_successors_closed=sum(c[-1] is not None for c in cases),
                  affine=dict(passed_cases=len(cases), case_kinds=dict(kind_counts), fuel=1000,
                              minimum_literal_rules=min_literal, maximum_rules_per_case=max_rule_count,
                              total_rules=dict(rule_totals), used_rows=len(symbolic_rows)),
                  boot=dict(literal_steps=82552, state=96, head=2, header_distance=40,
                            primary=[0] * 9, spare_count=65, nonzero_spares={8: 1},
                            whole_one_positions=sorted(expected_boot), all_other_cells_zero=True,
                            used_rows=len(boot[4])),
                  literal_controls=dict(variants=len(variants), passed_cases=sum(literal_counts.values()),
                                        case_kinds=dict(literal_counts), full_tape_comparison_on_nonhalt=True,
                                        total_microsteps=total_steps, maximum_microsteps=max_steps,
                                        maximum_intermediate_dispatch_visits=max_intermediate,
                                        used_rows_including_boot=len(literal_rows), examples=examples),
                  graph_reachable_working_states=len(reachable), graph_unreachable_states=sorted(states - reachable),
                  changed_common_rows=sum(table[k] != v for k, v in baseline.items() if k in table),
                  deleted_old_states=sorted({q for q, _ in baseline} - states),
                  added_working_states=sorted(states - {q for q, _ in baseline}),
                  elapsed_seconds=time.monotonic() - begun)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ('status', 'working_states', 'source_guarded_cases', 'elapsed_seconds')}), flush=True)


if __name__ == '__main__':
    main()
