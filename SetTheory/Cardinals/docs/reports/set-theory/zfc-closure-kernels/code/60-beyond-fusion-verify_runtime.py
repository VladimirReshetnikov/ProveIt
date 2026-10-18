#!/usr/bin/env python3
"""Check the changed runtime against every guard of its frozen source DAG.

Instruction verification is conditional on the four unchanged Box contracts
used by strict_affine.py. The literal blank prefix is checked separately.
Source-level arithmetic equivalence and Con(ZFC) calibration are separate
mathematical obligations. This is a Python sufficient checker, not a proof
kernel or a machine-minimality certificate.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib.util
import json
import sys
import time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'inputs'))
sys.dont_write_bytecode = True
import audit_helper as audit


def load_strict():
    path = HERE/'inputs/strict_affine.py'
    sys.modules['cost_search'] = SimpleNamespace()
    spec = importlib.util.spec_from_file_location('portable_strict', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sites_and_walk(data):
    nodes = {int(q): tuple(map(tuple, edges)) for q, edges in data['nodes'].items()}
    root = int(data['root'])
    assert root in nodes
    for q, edges in nodes.items():
        assert len(edges) == 2
        for edge in edges:
            assert edge[0] in {'N', 'I', 'D', 'B', 'C', 'H'}
            assert len(edge) == (1 if edge[0] == 'H' else 2)
            if edge[0] == 'N':
                assert edge[1] in nodes and edge[1] < q, 'acyclic bottom-up DAG numbering'
    sites = []
    reached = set()
    def visit(q, path):
        reached.add(q)
        for bit, edge in enumerate(nodes[q]):
            p = path + str(bit)
            if edge[0] == 'N':
                visit(edge[1], p)
            else:
                sites.append((p, 'C' + edge[0], edge[1] if len(edge) == 2 else None))
    visit(root, '')
    assert reached == set(nodes)
    def walk(pc):
        q, consumed = root, ''
        while True:
            bit = pc[len(consumed)] if len(consumed) < len(pc) else '0'
            consumed += bit
            edge = nodes[q][int(bit)]
            if edge[0] != 'N':
                assert not any(c == '1' for c in pc[len(consumed):]), ('stray successor bits', pc)
                return consumed, 'C'+edge[0], edge[1] if len(edge) == 2 else None
            q = edge[1]
    return nodes, sites, walk


def cases_from_dag(data, strict):
    nodes, sites, walk = sites_and_walk(data)
    cases = []
    for pc, op, logical in sites:
        for zero in ((True, False) if op == 'CD' else (None,)):
            physical = audit.NEWPHYS[logical] if op in ('CI', 'CD') else logical
            guard = (physical, zero) if op == 'CD' else None
            nxt = audit.successor(pc, op, logical, zero)
            if op != 'CH':
                walk(nxt or '')
            effect = ('inc', physical) if op == 'CI' else ('dec', physical) if op == 'CD' and not zero else None
            right = [('b', int(c)) for c in (nxt or '')]
            right += [('r', 0, 1, (41 if nxt is None else 40)-len(nxt or '')), ('b', 1), ('box', ('plain', effect))]
            target = strict.canon([('b', 1)], right)
            cases.append((pc, op, logical, guard, nxt, target))
    return nodes, sites, cases


def verify(table_path, dag_path, expected_states, expected_cases):
    began = time.monotonic()
    strict = load_strict()
    raw = table_path.read_bytes()
    numeric = audit.read_table(raw)
    states = {q for q, _ in numeric}
    assert len(states) == expected_states
    assert set(numeric) == {(q, bit) for q in states for bit in (0, 1)}
    assert {64, 96} <= states and 254 not in states
    assert all(w in (0, 1) and d in ('L', 'R') and t in states | {254} for w, d, t in numeric.values())
    baseline_raw = (HERE/'inputs/permutation252.tm').read_bytes()
    assert hashlib.sha256(baseline_raw).hexdigest() == audit.EXPECTED_SHA
    baseline = audit.read_table(baseline_raw)
    assert len(audit.BOX_PAIRS) == 55
    assert all(numeric[k] == baseline[k] for k in audit.BOX_PAIRS)
    table = {(str(q), bit): (w, d, str(t)) for (q, bit), (w, d, t) in numeric.items()}
    nodes, sites, cases = cases_from_dag(json.loads(dag_path.read_text()), strict)
    assert len(cases) == expected_cases
    totals = Counter()
    case_records = []
    minimum = 10**9
    for index, (pc, op, logical, guard, nxt, target) in enumerate(cases):
        counts, literal = strict.run(table, pc, guard, target, halt=(op == 'CH'), fuel=1500)
        assert literal > 0, ('no positive literal progress', index)
        totals.update(counts)
        minimum = min(minimum, literal)
        case_records.append({'index': index, 'pc': pc, 'operation': op, 'logical_argument': logical,
                             'guard': guard, 'successor': nxt, 'literal_steps': literal,
                             'symbolic_rule_steps': sum(counts.values()), 'pass': True})
    # Exact finite binary execution with a sparse tape, from the blank tape.
    q, head, ones, _, prefix9 = audit.run_prefix(numeric, 82552)
    spare = [0]*65
    spare[8] = 1
    expected = audit.paint('', 40, [0]*9, spare, 2)
    assert (q, head, ones) == (96, 2, expected)
    assert len(ones) == 77
    return {'scope': __doc__, 'status': 'PASS', 'working_states': len(states), 'rows': len(numeric),
            'start_state': 64, 'dispatch_state': 96, 'halt_label': 254,
            'decoder_nodes': len(nodes), 'leaf_occurrences': len(sites), 'guard_cases': len(cases),
            'minimum_literal_steps': minimum, 'unchanged_box_rows': 55, 'affine_fuel': 1500,
            'rule_counts': dict(totals), 'cases': case_records,
            'blank_prefix': {'steps': 82552, 'state': q, 'head': head, 'ones': sorted(ones),
                             'all_other_cells_zero': True, 'prefix9': prefix9,
                             'equals_permutation252_clean_root': True},
            'input_sha256': {str(path.relative_to(HERE)) if path.is_relative_to(HERE) else path.name:
                              hashlib.sha256(path.read_bytes()).hexdigest()
                              for path in (table_path, dag_path, HERE/'inputs/strict_affine.py', HERE/'inputs/audit_helper.py')},
            'elapsed_seconds': time.monotonic()-began}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, default=HERE/'inputs/direct255.tm')
    parser.add_argument('--dag', type=Path, default=HERE/'inputs/direct_fused_dag.json')
    parser.add_argument('--expected-states', type=int, default=255)
    parser.add_argument('--expected-cases', type=int, default=7311)
    parser.add_argument('--output', type=Path, default=HERE/'evidence/direct255-verification.json')
    args = parser.parse_args()
    assert __debug__, 'Run without -O: assertions are verification conditions.'
    result = verify(args.table.resolve(), args.dag.resolve(), args.expected_states, args.expected_cases)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print({k: v for k, v in result.items() if k not in {'cases', 'rule_counts', 'scope'}})


if __name__ == '__main__':
    main()
