#!/usr/bin/env python3
"""Original static243 source writer and independently handwritten linear cuts.
Never execute saved source arrays or import predecessor scientific programs.
"""
import argparse
import hashlib
import json
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs')
ARCHIVE = BASE / 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
BINDINGS = {
    'neary_woods_positive_groups244_tesla.md': '8f4bcdb21a1202c618de0e2b6cd9cb3f5d83372cf9ab83f59ee8f32d3701ff07',
    'neary_woods_positive_groups244_tesla.py': '21bfe676106749fefe71bd0f5b32e3cd8689f3e68c24f4798782fb717750d203',
    'neary_woods_positive_groups244_tesla.json': '59fb18b0cda52249afab70bf7e2952e80378ab41961e299d809dfa20e322003b',
}

def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoding(rows):
    return json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()


def operands(row):
    return {value for value in row[2:] if isinstance(value, str)}


def uses(rows, name):
    return sorted(row[0] for row in rows if name in operands(row))


def inspect(rows, supplied, output, recipes):
    available = set(supplied)
    names = set()
    counts = {'M': 0, 'A': 0}
    roles = set()
    for row in rows:
        check(isinstance(row, list) and len(row) == 4, 'binary row shape')
        name, operation = row[:2]
        check(isinstance(name, str) and name not in available, 'unique producer')
        check(operation in ('+', '-', '*'), 'allowed operation')
        check(operands(row) <= available, 'topological ordering')
        for value in row[2:]:
            if isinstance(value, str) or type(value) is int:
                continue
            check(type(value) is dict and set(value) == {'fixed_numeral'}, 'numeral role form')
            roles.add(value['fixed_numeral'])
        counts['M' if operation == '*' else 'A'] += 1
        available.add(name)
        names.add(name)
    check(roles == set(recipes), 'all numeral roles used')
    producers = {row[0]: row for row in rows}
    pending = [output]
    live = set()
    while pending:
        value = pending.pop()
        if value in live:
            continue
        live.add(value)
        if value in producers:
            pending.extend(operands(producers[value]))
    check(names | set(supplied) <= live, 'all gates and supplied ports live')
    return dict(counts, total=len(rows), all_rows_and_ports_live=True,
                fixed_numeral_roles=len(roles), canonical_source_sha256=digest(encoding(rows)))


def order(records, supplied):
    pending = records[:]
    known = set(supplied)
    arranged = []
    while pending:
        found = next((i for i, row in enumerate(pending) if operands(row) <= known), None)
        check(found is not None, 'acyclic replacement graph')
        row = pending.pop(found)
        check(row[0] not in known, 'unique replacement name')
        known.add(row[0])
        arranged.append(row)
    return arranged


def replace_size_cone(form):
    rows = form['source']
    supplied = form['parameters'] + form['auxiliaries']
    old_audit = inspect(rows, supplied, form['output'], form['fixed_numeral_recipes'])
    check((old_audit['total'], old_audit['M'], old_audit['A']) == (244, 129, 115), 'complete244 parent')
    check(old_audit == form['ledger'], 'parent ledger binding')
    by_name = {row[0]: row for row in rows}
    literals = [
        ['group_global_slack', '+', 'hist__global_bound', 'hist__Shat1'],
        ['groups_size_slack', '+', 'group_global_slack', 'hist__S0'],
        ['hist__global_sum__14', '+', 'hist__ZVhat1', 'hist__global_sum__13'],
        ['hist__linear_group__169', '+', 'hist__Shat1', 'hist__ZVhat1'],
        ['hist__P__10', '+', 'groups_size_slack', 'hist__global_sum__14'],
        ['hist__global_sum__13', '+', 'hist__ZV0', 'hist__global_sum__12'],
        ['hist__global_sum__12', '+', 'hist__ZU0', 'hist__global_sum__11'],
        ['hist__global_sum__11', '+', 'hist__H_U', 'hist__H_V'],
    ]
    for literal in literals:
        check(by_name[literal[0]] == literal, 'literal cut binding ' + literal[0])
    guards = {
        'group_global_slack': ['groups_size_slack'],
        'groups_size_slack': ['hist__P__10'],
        'hist__global_sum__14': ['hist__P__10'],
        'hist__linear_group__169': ['hist__linear_coefficient__170'],
    }
    for name, targets in guards.items():
        check(uses(rows, name) == targets, 'complete parent consumer guard ' + name)
    changes = {
        'groups_size_slack': ['groups_size_slack', '+', 'hist__global_bound', 'hist__S0'],
        'hist__global_sum__14': ['hist__global_sum__14', '+', 'hist__linear_group__169', 'hist__global_sum__13'],
    }
    records = [changes.get(row[0], row) for row in rows if row[0] != 'group_global_slack']
    replacement = order(records, supplied)
    audit = inspect(replacement, supplied, form['output'], form['fixed_numeral_recipes'])
    check((audit['total'], audit['M'], audit['A']) == (243, 129, 114), 'complete243 count')
    check(len(form['auxiliaries']) == 43, 'unchanged43 witnesses')
    kept = sum(row == by_name.get(row[0]) for row in replacement)
    check(kept == 241, '241 literal retained records')
    check(uses(replacement, 'hist__linear_group__169') == ['hist__global_sum__14', 'hist__linear_coefficient__170'], 'shared addition consumers')
    check(uses(replacement, 'groups_size_slack') == ['hist__P__10'], 'child slack private')
    check(uses(replacement, 'hist__global_sum__14') == ['hist__P__10'], 'child sum private')
    check(replacement[-1] == ['lower_unit_output', '-', 'lower_history_product', 'geo__A'], 'charged final subtraction')
    inherited = ['parameters', 'auxiliaries', 'domains', 'merged', 'fixed_numeral_recipes',
                 'fixed_u9_recipe', 'output', 'comparisons', 'multiplier_port', 'scaled_factor_semantics']
    result = {key: form[key] for key in inherited}
    result.update(
        source=replacement, ledger=audit,
        certificate={'total': 242, 'M': 129, 'A': 113, 'comparisons': 1, 'positive_witnesses': 43},
        manual_degree_upper_bound=936, exact_degree_claimed=False,
        parent_source_sha256=old_audit['canonical_source_sha256'],
        inverse_to_parent={'all_supplied_coordinates': 'identity'},
        delta={'deleted': [by_name['group_global_slack']], 'added': [],
               'edited': [{'before': by_name[name], 'after': row} for name, row in changes.items()],
               'literal_retained_row_records': kept, 'consumer_guards': guards,
               'fixed_numeral_recipes_changed': False,
               'topological_reorder': replacement != records},
        scope='Exact same polynomial on identical supplied coordinates over every commutative ring; complete inherited U9 interfaces.')
    return result


def handwritten_linear_identity():
    # These eight abstract variables are unrelated to all saved source arrays.
    labels = ['g', 'S0', 'Shat1', 'ZVhat1', 'HU', 'HV', 'ZU', 'ZV0']
    basis = [tuple(int(i == j) for j in range(8)) for i in range(8)]
    g, s0, sh1, zv1, hu, hv, zu, zv0 = basis
    def plus(left, right):
        return tuple(a + b for a, b in zip(left, right))
    rest = plus(zv0, plus(zu, plus(hu, hv)))
    original = plus(plus(plus(g, sh1), s0), plus(zv1, rest))
    shared = plus(plus(g, s0), plus(plus(sh1, zv1), rest))
    check(original == shared == (1,) * 8, 'independent whole-size linear identity')
    return {'variables': labels, 'parent_coefficients': list(original),
            'child_coefficients': list(shared), 'exact_cut_identities': 1,
            'scope': 'Handwritten eight-variable linear P cut, not symbolic evaluation of source arrays.'}


def receipt():
    dependencies = []
    parent_data = None
    for name, expected in BINDINGS.items():
        path = ARCHIVE / name
        if not path.exists():
            path = Path('/tmp') / name
        raw = path.read_bytes()
        check(digest(raw) == expected, 'frozen dependency ' + name)
        dependencies.append({'path': str((ARCHIVE / name).relative_to(BASE)), 'sha256': expected, 'bytes': len(raw)})
        if name.endswith('.json'):
            parent_data = json.loads(raw)
    check(parent_data is not None and len(parent_data['forms']) == 2, 'both parent interfaces present')
    forms = [replace_size_cone(form) for form in parent_data['forms']]
    check([form['merged'] for form in forms] == [False, True], 'both ordinary-input interfaces')
    return {'status': 'PASS', 'helper_sha256': digest(Path(__file__).read_bytes()),
            'dependencies': dependencies,
            'dependency_locator_policy': 'Pinned repository bytes or identical same-name /tmp bytes before installation.',
            'forms': forms, 'handwritten_linear_cut': handwritten_linear_identity(),
            'source_arrays_evaluated': False, 'source_degree_propagation': False,
            'predecessor_or_frozen_code_executed_or_imported': False}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    options = parser.parse_args()
    serialized = json.dumps(receipt(), indent=2, sort_keys=True) + '\n'
    path = Path(__file__).with_suffix('.json')
    if options.write:
        path.write_text(serialized)
    else:
        check(path.read_text() == serialized, 'saved receipt exact match')
    print('PASS: two complete243 sources; static count/topology/liveness and one independent linear cut.')


if __name__ == '__main__':
    main()
