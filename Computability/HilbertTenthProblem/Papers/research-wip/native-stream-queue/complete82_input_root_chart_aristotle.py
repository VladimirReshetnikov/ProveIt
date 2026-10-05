#!/usr/bin/env python3
"""Fresh static author binding. Never evaluates saved or newly emitted arrays.

Only pre-freeze execution is authorized; dependencies remain inert bytes/JSON.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
STEM = Path('/tmp/complete82_input_root_chart_aristotle')
PINS = {
    'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
    'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
    'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
    'complete83_shared_projection_scout.md': 'e36f465f257836c972b0edf10b865580e14427360d37799433fa7f301a85a4b8',
    'complete83_shared_projection_math.md': '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c',
    'complete84_main_quotient_gap_aristotle.md': '73e1dbef9b5767405d11d8f992f3927b7bf8c5f992206c9590bc22c6516201db',
}


def ck(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source_meta(rows, free, output):
    available = set(free)
    for row in rows:
        name, op, left, right = row
        ck(name not in available and op in ('*', '+', '-'), 'definition')
        for operand in (left, right):
            ck(type(operand) is int or operand in available, 'topology')
        available.add(name)
    defs = {r[0]: r for r in rows}
    live = set()
    pending = [output]
    while pending:
        name = pending.pop()
        if type(name) is int or name in live:
            continue
        live.add(name)
        if name in defs:
            pending.extend(defs[name][2:])
    ck(live == set(free) | set(defs), 'all rows and free ports live')
    counts = Counter(r[1] for r in rows)
    return {'M': counts['*'], 'A': counts['+'] + counts['-'], 'total': len(rows),
            'live_rows': len(defs), 'live_free_ports': len(free)}


def topo(rows, free):
    remaining = [r[:] for r in rows]
    available = set(free)
    ordered = []
    while remaining:
        ready = next((r for r in remaining if all(type(x) is int or x in available for x in r[2:])), None)
        ck(ready is not None, 'cycle or absent port')
        ordered.append(ready)
        available.add(ready[0])
        remaining.remove(ready)
    return ordered


def add(p, q, scale=1):
    result = dict(p)
    for mon, coef in q.items():
        result[mon] = result.get(mon, 0) + scale * coef
        if result[mon] == 0:
            del result[mon]
    return result


def mul(p, q):
    result = {}
    for x, a in p.items():
        for y, b in q.items():
            mon = tuple(s + t for s, t in zip(x, y))
            result[mon] = result.get(mon, 0) + a * b
    return {m: c for m, c in result.items() if c}


def cut_check():
    names = ['a', 'c', 'kappa', 'X', 'W', 'M', 'sigma', 'H']
    variables = {}
    for i, name in enumerate(names):
        mon = tuple(int(j == i) for j in range(len(names)))
        variables[name] = {mon: 1}
    a, c, k, x, w, m, s, h = [variables[n] for n in names]
    u = add(add(m, mul(a, k), -1), w, -1)
    old_d = add(add(add(mul(a, c), x), u), mul(s, h))
    new_d = add(add(add(mul(a, add(c, k, -1)), add(x, w, -1)), m), mul(s, h))
    old_mu = add(add(mul(a, k), w), u)
    ck(old_d == new_d, 'main-root formal cut')
    ck(old_mu == m, 'input-root formal cut')
    return {'variables': names, 'restored_main_root_terms': len(new_d),
            'restored_input_root_terms': len(old_mu), 'both_exact': True,
            'scope': 'Handwritten two-root coefficient identity only; no source-array interpreter.'}


def build():
    dependencies = []
    raw = {}
    reads = {
        'complete84_scaled_strong_output.json': 'Full JSON, static definitions and inherited interface only.',
        'complete84_scaled_strong_output.md': 'Full proof read; scaled-strong factorization used.',
        'complete83_shared_projection_scout.json': 'Full source and declared interfaces; no evaluations imported.',
        'complete83_shared_projection_scout.md': 'Full proof read; historical status explicitly superseded.',
        'complete83_shared_projection_math.md': 'Lines1-110: all-zero pretyping, native roots and exact offset; diagnostic section not reaudited.',
        'complete84_main_quotient_gap_aristotle.md': 'Full note read; compare canonical gap proof with offset-blind extension.',
    }
    for name, expected in PINS.items():
        data = (BASE / name).read_bytes()
        ck(sha(data) == expected, 'dependency ' + name)
        raw[name] = data
        dependencies.append({'path': str(BASE / name), 'sha256': expected, 'bytes': len(data), 'read_scope': reads[name]})
    for name, scope in [
        ('complete83_rejecting_compiler.md', 'Full proof read; quantified same-recipe unbounded-input refutation inherited.'),
        ('complete82_auxiliary_square_product_chart.md', 'Lines1-80; distinct source and lost auxiliary condition only.'),
        ('complete82_all_input_outer_collapse.md', 'Lines1-85; distinguish its all-input conclusion.'),
        ('complete80_main_root_gap_collapse.md', 'Lines1-130; distinguish its free main-gap transformation.'),
    ]:
        data = (BASE / name).read_bytes()
        dependencies.append({'path': str(BASE / name), 'sha256': sha(data), 'bytes': len(data), 'read_scope': scope})
    packet = json.loads(raw['complete83_shared_projection_scout.json'])['packet']
    original_serialized = json.dumps(packet, sort_keys=True)
    rows = packet['source']
    old_meta = source_meta(rows, packet['free'], packet['output'])
    ck(old_meta['M'] == 46 and old_meta['A'] == 37 and old_meta['total'] == 83, 'parent count')
    defs = {r[0]: r for r in rows}
    guards = [
        ['cam2', '*', 'R10a', 'R12'], ['D1', '+', 'wn2', 'cam2'],
        ['gam', '*', 'sigma', 'a4m5'],
        ['shared_main_partial', '+', 'D1', 'shared_projection'],
        ['R14', '+', 'shared_main_partial', 'gam'],
        ['difference_multiple', '*', 'index_rhs', 'R12'],
        ['exponent_partial', '+', 'W', 'difference_multiple'],
        ['exponent_rhs', '+', 'exponent_partial', 'shared_projection'],
        ['mu2', '*', 'exponent_rhs', 'exponent_rhs'],
        ['index_product', '*', 'delta', 'A'], ['index_rhs', '+', 'odd_index', 'index_product'],
        ['scaled_t', '*', 'twice_cell_bits', 'x'], ['odd_index', '+', 'scaled_t', 'inner_bits'],
        ['W', '-', 'marked_rhs', 'Z'], ['marked_rhs', '-', 'C_after_alpha', 'scaled_t'],
        ['C_after_alpha', '-', 'q_minus_FZ', 'alpha'], ['q_minus_FZ', '-', 'q_minus_F', 'Z'],
        ['q_minus_F', '-', 'q', 'F'],
        ['A', '+', 'a_square', 'a4m5'], ['a_square', '*', 'R12', 'R12'],
        ['a4m5', '+', 'a4', 3], ['a4', '*', 4, 'R12'],
        ['aux_coefficient_root', '*', 'i', 'Ac2'], ['R16', '*', 'aux_coefficient_root', 'aux_coefficient_root'],
        ['scaled_f_square', '*', 'A', 'L16'], ['norm_strong', '-', 'scaled_f_square', 'R16'],
        ['Ac2', '*', 'A', 'c2'], ['c2', '*', 'R10a', 'R10a'], ['L16', '*', 'f', 'f'],
        ['polynomial', '-', 'seven_units', 'A'],
    ]
    for row in guards:
        ck(defs[row[0]] == row, 'literal bound row ' + row[0])
    removed = {'cam2', 'D1', 'shared_main_partial', 'R14', 'difference_multiple', 'exponent_partial', 'exponent_rhs'}
    inserted = [
        ['root_coefficient_gap', '-', 'R10a', 'index_rhs'],
        ['root_scaled_gap', '*', 'R12', 'root_coefficient_gap'],
        ['root_projection_gap', '-', 'wn2', 'W'],
        ['root_partial', '+', 'root_scaled_gap', 'root_projection_gap'],
        ['root_with_input', '+', 'root_partial', 'input_root'],
        ['R14', '+', 'root_with_input', 'gam'],
    ]
    modified = ['mu2', '*', 'input_root', 'input_root']
    new_rows = [modified[:] if r[0] == 'mu2' else r[:] for r in rows if r[0] not in removed] + inserted
    free = ['input_root' if n == 'shared_projection' else n for n in packet['free']]
    witnesses = ['input_root' if n == 'shared_projection' else n for n in packet['witnesses']]
    new_rows = topo(new_rows, free)
    ledger = source_meta(new_rows, free, packet['output'])
    ck(ledger == {'M':45, 'A':37, 'total':82, 'live_rows':82, 'live_free_ports':25}, 'child ledger')
    literal = [r[0] for r in new_rows if defs.get(r[0]) == r]
    ck(len(literal) == 75, 'literal unchanged count')
    ck(len(witnesses) == 18 and len(set(witnesses)) == 18, 'witnesses')
    finalizer = ['norm_pair', 'norm_triple', 'norm_four', 'norm_product', 'all_units', 'seven_units', 'polynomial']
    newdefs = {r[0]:r for r in new_rows}
    ck(all(newdefs[n] == defs[n] for n in finalizer), 'full literal finalizer')
    ck(json.dumps(packet, sort_keys=True) == original_serialized, 'parent immutability')
    # Only residue classes of the handwritten norm, not source evaluations.
    ck(all((m*m - ((a+1)*(a+3))*k*k) % 4 != 3 for a in range(4) for m in range(4) for k in range(4)), 'mod4 sign')
    return {
        'author': 'Aristotle, new scoped input-root chart',
        'proof': {'path': str(STEM.with_suffix('.md')), 'sha256': sha(STEM.with_suffix('.md').read_bytes())},
        'helper_sha256': sha(Path(__file__).read_bytes()),
        'dependencies': dependencies,
        'parent_immutable': True,
        'literal_guards': guards,
        'removed_rows': [r for r in rows if r[0] in removed],
        'inserted_rows': inserted,
        'changed_retained_row': {'old':defs['mu2'], 'new':modified},
        'literal_retained_names': literal,
        'finalizer': [defs[n] for n in finalizer],
        'packet': {'source':new_rows, 'free':free, 'witnesses':witnesses,
                   'ordinary_input':packet['ordinary_input'], 'fixed_numerals':packet['fixed_numerals'],
                   'output':packet['output'], 'ledger':ledger, 'factors':packet['factors'],
                   'positive_zero_language':'Exactly shared-projection83 on inherited valid compiler slices; refuted.',
                   'exact_degree_claimed':False},
        'cut_identity':cut_check(),
        'mod4_handwritten_norm_cases':64,
        'execution_limits': {'source_arrays_evaluated':False, 'predecessor_code_executed_or_imported':False,
                             'native_fixtures_materialized':False, 'repository_mutation':False,
                             'future_replay_authorized':False},
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = build()
    target = STEM.with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    else:
        ck(result == json.loads(target.read_text()), 'exact receipt')
    print('PASS: static82=45M37A,18w,75 literal rows, all25 ports live; no source evaluations.')


if __name__ == '__main__':
    main()
