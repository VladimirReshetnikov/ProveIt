#!/usr/bin/env python3
"""Independent exact audit of the recompiled 215-state rotation12 companion.

Source graph equality is an all-natural step-equivalence certificate. Blank
startup replay is finite. The separate symbolic runtime receipt supplies the
unbounded source-to-TM simulation theorem; this script only checks its binding.
"""
from collections import deque
from pathlib import Path
import hashlib
import importlib.util
import json
import gzip

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'upstream'
NEW = ROOT / 'machine'
RUNTIME = ROOT / 'evidence/shallow'
OUT = RUNTIME
spec = importlib.util.spec_from_file_location('source', ROOT / 'code/source_language.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def table(p):
    answer = {}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, r, w, direction, z = line.split()
        q, r, w, z = map(int, (q, r, w, z))
        assert r in (0, 1) and w in (0, 1) and direction in ('L', 'R')
        assert (q, r) not in answer
        answer[q, r] = (w, -1 if direction == 'L' else 1, z)
    states = {q for q, r in answer}
    assert len(states) == 215 and len(answer) == 430
    assert all((q, r) in answer for q in states for r in (0, 1))
    assert {z for w, d, z in answer.values()} - states == {254}
    return answer


def graph_distinguishing_word(old, new):
    """Shortest labeled graph word with unequal write/move or halt behavior."""
    todo = deque([(0, 0, '')])
    seen = {(0, 0)}
    while todo:
        q, z, prefix = todo.popleft()
        if (q == 254) != (z == 254):
            return {'word': prefix, 'reason': 'halt status differs'}
        if q == 254:
            continue
        for bit in (0, 1):
            a, b = old[q, bit], new[z, bit]
            word = prefix + str(bit)
            if a[:2] != b[:2]:
                return {'word': word, 'reason': 'write/move pair differs', 'old_state': q, 'new_state': z, 'old_action': list(a), 'new_action': list(b)}
            pair = (a[2], b[2])
            if pair not in seen:
                seen.add(pair)
                todo.append((*pair, word))
    return None


baseline_rows = json.loads((BASE / 'sites215.json').read_text())
new_rows = json.loads((NEW / 'sites-shallow.json').read_text())
baseline = s.tree(baseline_rows)
changed = s.tree(new_rows)
path = '11010010011101010110011100'
old_node = s.subtree(baseline, path)
(A, B), C = old_node
assert all(s.boundary(factor) == (0, 0, False) for factor in (A, B, C))
rebuilt = s.replace(baseline, path, (A, (B, C)))
assert rebuilt == changed
assert s.compact(s.sites(rebuilt)) == (NEW / 'sites-shallow.json').read_bytes()
assert [r[1:] for r in baseline_rows] == [r[1:] for r in new_rows]
old_graph, old_no_stray = s.graph_arithmetic(baseline_rows)
new_graph, new_no_stray = s.graph_arithmetic(new_rows)
assert old_graph == new_graph == s.graph_intervals(baseline_rows) == s.graph_intervals(new_rows)
assert s.boundary(baseline) == s.boundary(changed) == (0, 0, True)

old_table = table(BASE / 'k215.native.tm')
new_table = table(NEW / 'k215-shallow.native.tm')
distinguishing_word = graph_distinguishing_word(old_table, new_table)
assert distinguishing_word is not None
startup = json.loads(gzip.decompress((RUNTIME / 'startup.json.gz').read_bytes()))
state, head, ones = 0, 0, set()
assert len(startup['trace']) == startup['steps'] == 95740
for recorded in startup['trace']:
    bit = int(head in ones)
    write, direction, target = new_table[state, bit]
    assert recorded == [state, head, bit, write, direction, target]
    if write:
        ones.add(head)
    else:
        ones.discard(head)
    state, head = target, head + direction
assert state == startup['state'] == 84
assert head == startup['head'] == -8
assert sorted(ones) == startup['one_cells']

# Reconstruct the advertised complete root frame without using the runtime
# checker's parser. Physical order is the legacy register layout.
logical = [4, 0, 0, 0, 0, 0, 0, 0, 0]
logical_to_physical = (6, 2, 0, 4, 3, 7, 8, 5, 1)
physical = [0] * 9
for i, j in enumerate(logical_to_physical):
    physical[j] = logical[i]
header = head + 64 + 1
expected_ones = {head - 1, header}
cursor = header + 1
for value in physical + [1] * 40:
    cursor += 1
    expected_ones.update(range(cursor, cursor + value + 1))
    cursor += value + 1
assert ones == expected_ones and len(ones) == 95
assert startup['registers'] == logical and startup['gap'] == 1 and startup['spares'] == [1] * 40

receipt = json.loads((RUNTIME / 'runtime.json').read_text())
cases = json.loads(gzip.decompress((RUNTIME / 'runtime_cases.json.gz').read_bytes()))
expected_guards = {(i, positive) for i, row in enumerate(new_rows) for positive in ((False, True) if row[1] == 'CD' else (False,))}
actual_guards = {(case['site_index'], case['positive']) for case in cases}
assert expected_guards == actual_guards and len(cases) == len(expected_guards) == 6176
assert receipt['table_sha256'] == sha(NEW / 'k215-shallow.native.tm')
assert receipt['sites_sha256'] == sha(NEW / 'sites-shallow.json')
assert receipt['status'] == 'UNIVERSAL_MATHEMATICAL_PASS' and receipt['failures'] == []
assert receipt['proved_cases'] == receipt['expected_cases'] == 6176
assert receipt['checker_sha256'] == sha(ROOT / 'code/runtime-inputs/runtime/symbolic_runtime.py')
assert receipt['helper_sha256'] == sha(ROOT / 'code/runtime-inputs/runtime/independent_runtime.py')

result = {
    'status': 'PASS',
    'scope': 'Exact finite source reconstruction with all-natural identity step equivalence, whole blank-prefix replay, complete frame reconstruction, and symbolic-runtime receipt binding/coverage. The separately executed symbolic runtime is not rerun here. No formal proof-assistant kernel claim.',
    'source_sha256': sha(NEW / 'sites-shallow.json'),
    'table_sha256': sha(NEW / 'k215-shallow.native.tm'),
    'baseline_source_sha256': sha(BASE / 'sites215.json'),
    'baseline_table_sha256': sha(BASE / 'k215.native.tm'),
    'recipe': {'path': path, 'rewrite': '((A,B),C) -> (A,(B,C))', 'closed_factors': True, 'factor_leaf_counts': [len(s.sites(x)) for x in (A, B, C)]},
    'old_metrics': s.metrics(baseline),
    'new_metrics': s.metrics(changed),
    'changed_leaf_paths': sum(a[0] != b[0] for a, b in zip(baseline_rows, new_rows)),
    'total_leaf_path_length_change': sum(len(b[0]) - len(a[0]) for a, b in zip(baseline_rows, new_rows)),
    'primitive_word_identical': True,
    'all_instruction_effects_and_guarded_successors_identical': True,
    'independent_CFG_resolvers_agree': True,
    'arithmetic_no_stray_successor_checks': [old_no_stray, new_no_stray],
    'changed_binary_rows': sum(old_table[k] != v for k, v in new_table.items()),
    'rooted_transition_graphs_not_isomorphic': distinguishing_word,
    'blank_startup_steps': startup['steps'],
    'blank_seed': {'state': state, 'head': head, 'header': header, 'gap': 1, 'logical_registers': logical, 'unit_spares': 40, 'one_cells': len(ones)},
    'symbolic_runtime_receipt_bound': True,
    'symbolic_runtime_guard_cases': len(cases),
}
(OUT / 'independent-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
