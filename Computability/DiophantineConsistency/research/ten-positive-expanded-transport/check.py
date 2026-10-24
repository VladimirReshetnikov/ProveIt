#!/usr/bin/env python3
"""Independent exact parent maps and free-ring equality; no producer imports."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
ANCHORS = {
    'ten-positive-zero-offset': {
        'equation.json': '047ea8145ef52ab939322f2147c75272e7a182016be78a453fbdf2d3c2a6a493',
        'PROOF.md': '8555e4f3cb78aba44e091e35d61b08a26f63f638b60d3d1795d3395680eff6f9',
        'MANIFEST.json': 'd5b79085e328ee3ce5a067d1c37f29c5d209957af1624e68f24068eb87a674cf',
    },
    'ten-positive-direct-zero-offset': {
        'equation.json': 'bea07edb73ff6cdf8f0f7c45dec63fa96b42848066cdb82661fd1e9fd4cd282f',
        'PROOF.md': '852b579bc75497f1be33ff1d02e45d94b59bc1b2acecc1609cefcec006ff99e8',
        'MANIFEST.json': '81181c10352dfbfa23c4c71044ce3c266b30458b0d605cfcf4e2f5b99b2494d7',
    },
}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def load(path):
    return json.loads(path.read_bytes())


def digest(data):
    return sha256(data).hexdigest()


def local_bindings():
    build = load(HERE / 'BUILD.json')
    need(build['status'] == 'PASS', 'complete local build receipt')
    expected = {'build.py', 'check.py', 'PROOF.md', 'README.md', 'PARENT_PINS.json',
                'zero98.json', 'zero98_CUTS.json', 'direct103.json', 'direct103_CUTS.json'}
    expected |= {str(p.relative_to(HERE)) for d in ['parents', 'coefficients']
                 for p in (HERE / d).rglob('*') if p.is_file()}
    need(set(build['sha256']) == expected, 'closed local build source and generated-artifact bindings')
    for rel, expected_hash in build['sha256'].items():
        need(digest((HERE / rel).read_bytes()) == expected_hash, 'actual complete local build binding ' + rel)
    manifest = HERE / 'MANIFEST.json'
    if manifest.is_file():
        records = load(manifest)['files']
        members = {str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p != manifest}
        need(set(records) == members, 'closed own research manifest inventory')
        for rel, expected_hash in records.items():
            need(digest((HERE / rel).read_bytes()) == expected_hash, 'complete own research manifest member ' + rel)


def parents_bound():
    pins = load(HERE / 'PARENT_PINS.json')
    for name, anchors in ANCHORS.items():
        folder = ROOT / 'candidates' / name
        for rel, expected in anchors.items():
            need(digest((folder / rel).read_bytes()) == expected, 'fixed accepted parent anchor ' + name + '/' + rel)
        manifest = load(folder / 'MANIFEST.json')['files']
        members = {str(p.relative_to(folder)) for p in folder.rglob('*')
                   if p.is_file() and p != folder / 'MANIFEST.json'}
        need(members == set(manifest), 'whole accepted closed parent member set')
        for rel, expected in manifest.items():
            need(digest((folder / rel).read_bytes()) == expected, 'whole accepted parent member ' + rel)
        for rel in ['equation.json', 'PROOF.md', 'CHECK.json', 'MANIFEST.json']:
            need(digest((folder / rel).read_bytes()) == pins[name + '/' + rel], 'entire recorded parent pin')
            if rel != 'MANIFEST.json':
                need((HERE / 'parents' / name / rel).read_bytes() == (folder / rel).read_bytes(),
                     'verbatim copied parent dependency ' + rel)
        need(load(folder / 'CHECK.json')['status'] == 'PASS', 'accepted complete parent receipt')


def topology(data, expected_count, breakdown, degree):
    rows = data['source']
    inputs = data['witnesses'] + data['fixed_numerals']
    known = set(inputs)
    degrees = {v: 1 for v in data['witnesses']} | {v: 0 for v in data['fixed_numerals']}
    deps = {}
    for row in rows:
        need(type(row) is list and len(row) == 4, 'binary gate shape')
        n, op, a, b = row
        need(n not in known and op in ['+', '-', '*'] and
             all(type(v) is int or v in known for v in [a, b]), 'fresh topological binary ring gate')
        da, db = [0 if type(v) is int else degrees[v] for v in [a, b]]
        degrees[n] = da + db if op == '*' else max(da, db)
        deps[n] = [a, b]
        known.add(n)
    live = set()
    todo = [data['output']]
    while todo:
        v = todo.pop()
        if type(v) is int or v in live:
            continue
        live.add(v)
        todo.extend(deps.get(v, []))
    need(live == known, 'every arithmetic gate, positive input and fixed port is live')
    need(len(rows) == data['operations'] == expected_count, 'actual operation count')
    need(dict(Counter(r[1] for r in rows)) == data['operation_breakdown'] == breakdown, 'actual operation breakdown')
    need(data['exact_degree'] == degree and degrees['N'] == data['syntactic_degree'] == (416 if degree == 368 else 384),
         'inherited exact degree and literal syntactic degree')
    for name, d in data['register_degrees'].items():
        need(degrees[name] == d, 'actual retained register degree ' + name)


def transcription(parent, child, cuts, direct):
    old, rows = parent['source'], child['source']
    deleted = {'qm1L', 'W', 'WBt'} | ({'q4'} if direct else set())
    changed = {'Hn': ['Hn', '*', 'Hp', 'nVL'],
               'q3WBt': ['q3WBt', '*', 'q3', 'B' if direct else 'Bt']}
    if direct:
        changed['P1'] = ['P1', '*', 'q3', 'qbJ']
    records = cuts['all_parent_rows']
    need([r['parent_index'] for r in records] == list(range(len(old))), 'all literal parent rows accounted exactly once')
    coverage = []
    previous = -1
    for rec in records:
        i = rec['parent_index']
        need(rec['old_row'] == old[i], 'all complete actual parent row operands')
        name = old[i][0]
        if name in deleted:
            need(rec == dict(parent_index=i, old_row=old[i], status='deleted_private'), 'only exact private gate deletion')
        else:
            j = rec['child_index']
            need(j > previous, 'relative order of retained parent rows')
            previous = j
            want = changed.get(name, old[i])
            need(rec['new_row'] == rows[j] == want and rec['status'] ==
                 ('replaced_operand' if name in changed else 'retained'), 'all changed and retained complete operands')
            coverage.append(j)
    inserted = cuts['inserted_child_rows']
    need([r['new_row'] for r in inserted] == [['LB', '*', 'L', 'B' if direct else 'Bt'], ['nVL', '-', 'nV', 'LB']],
         'the two exact newly inserted ring gates')
    for rec in inserted:
        need(rows[rec['child_index']] == rec['new_row'], 'new literal row position')
        coverage.append(rec['child_index'])
    names = [r[0] for r in rows]
    need(names.index('LB') == names.index('nV') + 1 and names.index('nVL') == names.index('LB') + 1,
         'new cuts immediately follow n+V')
    need(sorted(coverage) == list(range(len(rows))) and len(set(coverage)) == len(rows), 'complete child row coverage without aliases')
    expected_consumers = {'qm1L': ['W'], 'W': ['WBt'], 'WBt': ['q3WBt']}
    if direct:
        expected_consumers['q4'] = ['P1']
    for name, consumers in expected_consumers.items():
        need([r[0] for r in old if name in r[2:]] == consumers, 'entire deleted register consumer set ' + name)
    start_old = next(i for i, r in enumerate(old) if r[0] == 'U')
    start_new = next(i for i, r in enumerate(rows) if r[0] == 'U')
    need(old[start_old:] == rows[start_new:] and len(rows[start_new:]) == 13, 'identical entire weighted octic norm tail')
    for key in ['witnesses', 'fixed_numerals', 'coefficient_binding', 'domain', 'output']:
        need(child[key] == parent[key], 'unchanged complete parent field ' + key)
    need(child['domain'] == 'strictly positive integers' and len(child['witnesses']) == 10,
         'ten strictly positive coordinates')
    need(child['register_degrees'] == {k: v for k, v in parent['register_degrees'].items() if k != 'W'},
         'every unchanged degree bound and only removed W entry')
    need(child['parent_sha256'] == digest(json.dumps(parent, indent=2, sort_keys=True).encode() + b'\n'),
         'exact actual parent equation bytes')


# Sparse free polynomials over Z. A monomial is a sorted tuple of symbols;
# repeated symbols encode powers, so no external algebra package is trusted.
def add(a, b, scale=1):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0) + scale * coefficient
        if not out[monomial]:
            del out[monomial]
    return out


def mul(a, b):
    out = {}
    for m, c in a.items():
        for n, d in b.items():
            key = tuple(sorted(m + n))
            out[key] = out.get(key, 0) + c * d
    return {m: c for m, c in out.items() if c}


def literal_cut(rows, target, direct):
    definitions = {r[0]: r for r in rows}
    boundary = {'q3', 'q', 'bJ', 'mu2', 'Hp', 'n', 'V', 'L', 'Kpos', 'Y', 'e', 'X', 'B' if direct else 'Bt'}
    memo = {v: {(v,): 1} for v in boundary}

    def visit(v):
        if type(v) is int:
            return {(): v} if v else {}
        if v in memo:
            return memo[v]
        need(v in definitions, 'only declared free-cut boundary variables')
        _, op, a, b = definitions[v]
        p, q = visit(a), visit(b)
        memo[v] = mul(p, q) if op == '*' else add(p, q, -1 if op == '-' else 1)
        return memo[v]

    return visit(target)


def equality(parent, child, direct):
    old, new = parent['source'], child['source']
    p = literal_cut(old, 'Znum', direct)
    q = literal_cut(new, 'Znum', direct)
    need(p == q, 'universal exact recursive literal Z numerator identity')
    need(literal_cut(old, 'Mtot', direct) == literal_cut(new, 'Mtot', direct),
         'universal exact complete carrier M identity')
    need(literal_cut(old, 'P1', direct) == literal_cut(new, 'P1', direct),
         'universal exact shared direct denominator identity')
    return len(p)


def coefficient_binding(child):
    binding = child['coefficient_binding']
    need(load(HERE / 'coefficients/BINDING.json') == binding, 'whole copied binding record')
    values = {}
    for name, pin in binding['ports'].items():
        blob = (HERE / 'coefficients' / pin['file']).read_bytes()
        raw = gzip.decompress(blob)
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'], 'complete compressed and raw payload ' + name)
        values[name] = int.from_bytes(raw, 'little')
        need(values[name].bit_length() == pin['bits'], 'complete coefficient bit width')
    beta = values['beta']
    need(beta >= 31 and beta % 2 == 1 and values['K0'] > 0 and
         0 < values['MC'] < beta < values['MF'] < 2 * beta, 'full coherent original tuple box')


def rejected(parent, child, cuts, direct):
    tests = {}
    bad = deepcopy(child)
    next(r for r in bad['source'] if r[0] == 'Hn')[3] = 'nV'
    tests['missing_integral_center_absorption'] = bad
    bad = deepcopy(child)
    next(r for r in bad['source'] if r[0] == 'q3WBt')[3] = 'Y'
    tests['wrong_transport_numerator'] = bad
    bad = deepcopy(child)
    next(r for r in bad['source'] if r[0] == 'Df')[3] = 2
    tests['changed_unchanged_kernel'] = bad
    bad = deepcopy(child)
    bad['domain'] = 'integers'
    tests['changed_positive_domain'] = bad
    bad = deepcopy(child)
    bad['coefficient_binding']['ports']['K0']['raw_sha256'] = '0' * 64
    tests['individual_payload_substitution'] = bad
    if direct:
        bad = deepcopy(child)
        next(r for r in bad['source'] if r[0] == 'P1')[3] = 'bJ'
        tests['wrong_shared_denominator'] = bad
    caught = []
    for name, bad in tests.items():
        try:
            transcription(parent, bad, cuts, direct)
        except ValueError:
            caught.append(name)
        else:
            raise ValueError('corruption accepted: ' + name)
    # The symbolic oracle must reject both altered center numerators even
    # without the literal map check; this tests the universal identity cut.
    for name in ['missing_integral_center_absorption', 'wrong_transport_numerator']:
        try:
            equality(parent, tests[name], direct)
        except ValueError:
            continue
        raise ValueError('symbolic equality accepted corruption: ' + name)
    return caught


def main():
    local_bindings()
    parents_bound()
    results = {}
    for tag, parent_name, count, degree, breakdown in [
        ('zero98', 'ten-positive-zero-offset', 98, 368, {'*': 58, '+': 22, '-': 18}),
        ('direct103', 'ten-positive-direct-zero-offset', 103, 340, {'*': 61, '+': 23, '-': 19}),
    ]:
        direct = tag == 'direct103'
        parent = load(ROOT / 'candidates' / parent_name / 'equation.json')
        child = load(HERE / (tag + '.json'))
        cuts = load(HERE / (tag + '_CUTS.json'))
        need(cuts['parent_name'] == parent_name, 'actual named parent packet')
        transcription(parent, child, cuts, direct)
        topology(child, count, breakdown, degree)
        terms = equality(parent, child, direct)
        coefficient_binding(child)
        results[tag] = dict(status='PASS', positive_inputs=10, operations=count,
                            operation_breakdown=breakdown, exact_degree=degree,
                            complete_parent_rows_bound=len(parent['source']),
                            universal_literal_center_terms=terms,
                            identical_entire_polynomial=True, identical_positive_witness_map=True,
                            identical_full_norm_tail_operations=13,
                            exact_degree_inherited_by_polynomial_identity=True,
                            complete_coherent_four_payloads=True,
                            rejected_corruptions=rejected(parent, child, cuts, direct),
                            equation_sha256=digest((HERE / (tag + '.json')).read_bytes()),
                            copied_parent_proof_sha256=ANCHORS[parent_name]['PROOF.md'])
    receipt = dict(status='PASS', optimized_python=not __debug__, equations=results,
                   scope='Universal same-polynomial research contractions; ordinary unbounded accepted parent proofs inherited. No Lean, emitter, authentication dependency, frozen endpoint or page changed.')
    filename = 'CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json'
    (HERE / filename).write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps(receipt, sort_keys=True))


if __name__ == '__main__':
    main()
