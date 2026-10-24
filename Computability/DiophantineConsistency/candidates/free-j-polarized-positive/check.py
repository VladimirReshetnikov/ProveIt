#!/usr/bin/env python3
"""Independent complete circuit/cut identity and coherent-tuple verification."""
from collections import Counter
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import random
import sys
import zipfile
import sympy as S

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ARCHIVE_SHA = 'f4119b01e56f586558f0910c6deb21b83c82dfc324f884d7d95d28500ef09e63'
PARENT_SHA = '5d25f7e077cd3ac6c996ec8051113950ac7f7bf5c131dcf524b33638c1dbac95'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(raw):
    return sha256(raw).hexdigest()


def evaluate(rows, values):
    env = dict(values)
    def val(a):
        return a if type(a) is int else env[a]
    for name, op, a, b in rows:
        x, y = val(a), val(b)
        need(op in ('+', '-', '*'), 'binary arithmetic operation')
        env[name] = x+y if op == '+' else x-y if op == '-' else x*y
    return env


def check_cut(old, new):
    d, Q, V, n = S.symbols('d Q V n')
    values = dict(den=d, Q=Q, oneQ=1-Q, V=V, n=n)
    parent = evaluate(old, values)
    child = evaluate(new, values)
    h = (1-Q)*(n+V)**2 + Q*V**2 - 1
    need(S.expand(parent['h']-h) == S.expand(child['h']-h) == 0, 'both literal h polynomials equal required cut form')
    need(S.expand(parent['N']-child['N']) == 0, 'exact universal polarized norm identity')
    poly = S.Poly(S.expand(child['N']), d, Q, V, n)
    serial = [[list(m), int(c)] for m, c in poly.terms()]
    return dict(status='PASS', variables=['d', 'Q', 'V', 'n'], exact_terms=len(serial),
                coefficients_sha256=digest(json.dumps(serial, separators=(',', ':')).encode()))


def main():
    packet = load(HERE / 'equation.json')
    cuts = load(HERE / 'CUT_IDENTITY.json')
    provenance = load(HERE / 'PROVENANCE.json')
    need(provenance['archive_sha256'] == ARCHIVE_SHA, 'archive identity')
    path = REPO / provenance['archive']
    need(digest(path.read_bytes()) == ARCHIVE_SHA, 'complete arrival archive')
    with zipfile.ZipFile(path) as archive:
        raw = archive.read(provenance['parent_member'])
        need(digest(raw) == PARENT_SHA == provenance['parent_sha256'] == cuts['parent_sha256'], 'independently pinned complete free-J parent')
        for name, pin in provenance['source_files'].items():
            raw_source = (HERE / name).read_bytes()
            member = 'con_zfc_congruence_certificates/' + name[len('source/'):]
            need(digest(raw_source) == pin and raw_source == archive.read(member), 'unchanged retained original source')
    parent = json.loads(raw)
    ordinary = load(HERE / 'source/positive/parents/p12_ordinary_degree70.json')
    need(parent['source'] == ordinary['source'][2:], 'whole free-J remainder of ordinary parent')
    need(parent['witnesses'] == ['J']+ordinary['witnesses'][1:], 'exact free input promotion')
    need(packet['domain'] == parent['domain'] == 'strictly positive integers', 'positive domain')
    need(packet['witnesses'] == parent['witnesses'] and len(packet['witnesses']) == 12, 'unchanged complete witness inventory')
    need(packet['fixed_numerals'] == parent['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'], 'whole four-port inventory')
    start, old_length, new_length = (cuts[k] for k in ('source_prefix_length', 'parent_tail_length', 'child_tail_length'))
    old, new = cuts['old_tail'], cuts['new_tail']
    need(old == parent['source'][start:start+old_length] and new == packet['source'][start:start+new_length], 'literal cut blocks')
    need(packet['source'][:start] == parent['source'][:start] and packet['source'][start+new_length:] == parent['source'][start+old_length:], 'entire surrounding circuit unchanged')
    need(old_length == 17 and new_length == 15 and packet['output'] == parent['output'], 'exact two-gate replacement')
    need([row for row in parent['source'][:start] if row[0] == 'oneQ'] == [['oneQ', '-', 1, 'Q']],
         'the unchanged prefix establishes the exact cut relation oneQ=1-Q')
    identity = check_cut(old, new)
    known = set(packet['witnesses'] + packet['fixed_numerals'])
    dependencies = {}
    for name, op, a, b in packet['source']:
        need(name not in known and op in ('+', '-', '*'), 'fresh binary gate')
        need(all(type(x) is int or x in known for x in (a, b)), 'topological complete definition')
        known.add(name)
        dependencies[name] = (a, b)
    live = set()
    todo = [packet['output']]
    while todo:
        name = todo.pop()
        if type(name) is int or name in live:
            continue
        live.add(name)
        todo.extend(dependencies.get(name, ()))
    need(live == known, 'all declared inputs, ports and arithmetic gates live')
    count = Counter(row[1] for row in packet['source'])
    need(sum(count.values()) == packet['operations'] == 96 and dict(count) == packet['operation_breakdown'], 'whole live circuit operation census')
    binding = load(HERE / 'source/positive/coefficients/BINDING.json')
    ports = {}
    for name, entry in binding['ports'].items():
        packed = (HERE / 'source/positive/coefficients' / entry['file']).read_bytes()
        data = gzip.decompress(packed)
        need(digest(packed) == entry['sha256_gzip'] and digest(data) == entry['sha256_raw'], 'complete authentic fixed coefficient')
        need(len(data) == entry['raw_bytes'], 'coefficient raw length')
        ports[name] = int.from_bytes(data, 'little')
        need(ports[name].bit_length() == entry['bits'], 'fixed coefficient width')
    need(ports['beta'] == 2**590069-1 and packet['exact_degree'] == parent['exact_degree'] == 70, 'actual Mersenne parameter and inherited degree')
    # Degree >=70 at the actual fixed tuple; the identity transfers the
    # parent's reviewed degree <=70 without a multivariate expansion.
    lam = S.Symbol('lambda')
    degree_slices = []
    for prime in (1009, 1013, 1019):
        values = {name:S.Poly(lam, lam, modulus=prime) for name in packet['witnesses']}
        values.update({name:value % prime for name, value in ports.items()})
        degree_poly = evaluate(packet['source'], values)[packet['output']]
        degree_slices.append(dict(prime=prime, degree=int(degree_poly.degree()), leading_coefficient=int(degree_poly.LC())))
    need(any(row['degree'] == 70 and row['leading_coefficient'] for row in degree_slices), 'degree70 attained at actual coefficient specialization')
    rng = random.Random(9670)
    for _ in range(100):
        values = {name:rng.randrange(-5, 6) for name in packet['witnesses']}
        values.update({name:value % 1009 for name, value in ports.items()})
        want = evaluate(parent['source'], values)[parent['output']]
        have = evaluate(packet['source'], values)[packet['output']]
        need(want == have, 'full circuit signed-assignment diagnostic')
    bad = deepcopy(new)
    need(bad[-1][0] == 'N' and bad[-1][1] == '+', 'identified output polarity control')
    bad[-1][1] = '-'
    try:
        check_cut(old, bad)
    except ValueError:
        pass
    else:
        raise ValueError('corrupted norm tail accepted')
    for name, pin in load(HERE / 'BUILD.json')['sha256'].items():
        need(digest((HERE / name).read_bytes()) == pin, 'generated artifact seal')
    report = dict(status='PASS', optimized_python=bool(sys.flags.optimize), positive_variables=12,
        live_operations=96, operation_breakdown=dict(count), exact_degree=70,
        generic_cut_identity=identity, actual_tuple_degree_slices=degree_slices,
        whole_circuit_signed_diagnostics=100, corrupted_norm_tail_rejected=True,
        equation_sha256=digest((HERE / 'equation.json').read_bytes()),
        scope='Pointwise equality of complete circuit with free-J parent over all integer inputs/ports; coherent compact44 coefficient binding; ordinary positive correctness inherited. No Lean or internal object-ZFC proof.')
    name = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    (HERE / name).write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
