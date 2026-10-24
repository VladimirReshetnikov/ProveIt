#!/usr/bin/env python3
"""Independent exact audit, with its own AST/sparse ring and no author imports.

All coefficient ports remain formal indeterminates during the identity audit.
Their actual byte payloads are separately reconstructed from the native recipe.
Finite algebra and arithmetic checks do not certify the unbounded proof.
"""
from collections import defaultdict
from pathlib import Path
import ast
import gzip
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
G = HERE.parents[1] / 'guards'


def need(b, message):
    if not b:
        raise RuntimeError(message)


def clean(p):
    return {m: c for m, c in p.items() if c}


def const(n):
    return {(): n} if n else {}


def add(p, q):
    r = defaultdict(int, p)
    for m, c in q.items():
        r[m] += c
    return clean(r)


def neg(p):
    return {m: -c for m, c in p.items()}


def mul(p, q):
    r = defaultdict(int)
    for a, ca in p.items():
        for b, cb in q.items():
            r[tuple(sorted(a + b))] += ca * cb
    return clean(r)


def power(p, n):
    need(isinstance(n, int) and n >= 0, 'nonnegative polynomial power')
    r = const(1)
    while n:
        if n % 2:
            r = mul(r, p)
        p = mul(p, p)
        n //= 2
    return r


def parse(text):
    def walk(n):
        if isinstance(n, ast.Constant):
            need(type(n.value) is int, 'integer literal only')
            return const(n.value)
        if isinstance(n, ast.Name):
            return {(n.id,): 1}
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            return neg(walk(n.operand))
        if isinstance(n, ast.BinOp):
            if isinstance(n.op, ast.Add):
                return add(walk(n.left), walk(n.right))
            if isinstance(n.op, ast.Sub):
                return add(walk(n.left), neg(walk(n.right)))
            if isinstance(n.op, ast.Mult):
                return mul(walk(n.left), walk(n.right))
            if isinstance(n.op, ast.Pow):
                need(isinstance(n.right, ast.Constant), 'literal exponent')
                return power(walk(n.left), n.right.value)
        raise ValueError('unsupported polynomial AST: ' + ast.dump(n))
    return walk(ast.parse(text, mode='eval').body)


def substitute(p, sub):
    out = {}
    for m, c in p.items():
        term = const(c)
        for name in m:
            term = mul(term, sub.get(name, {(name,): 1}))
        out = add(out, term)
    return out


def symbols(p):
    return set(x for m in p for x in m)


def degree(p, variables):
    return max((sum(x in variables for x in m) for m in p), default=-1)


def sos(rows):
    p = {}
    for row in rows:
        p = add(p, mul(row, row))
    return p


def pure_coefficient(p, monomial, variables):
    target = next(iter(parse(monomial)))
    need(all(x in variables for x in target), 'target uses unknowns only')
    return {tuple(x for x in m if x not in variables): c for m, c in p.items()
            if tuple(x for x in m if x in variables) == target}


def metric(data):
    rows = list(map(parse, data['residuals']))
    vs = set(data['variables'])
    ports = set(data['fixed_numerals'])
    live = set().union(*(symbols(p) for p in rows))
    need(len(vs) == len(data['variables']) == data['variable_count'], 'unique variable count')
    need(not vs.intersection(ports), 'ports are not quantified')
    need(live == vs | ports, 'exact live variables and ports')
    need(len(rows) == data['equation_count'], 'residual count')
    p = sos(rows)
    degrees = [degree(r, vs) for r in rows]
    need(degrees == data['residual_degrees'], 'literal residual degrees')
    need(degree(p, vs) == data['exact_degree'], 'exact unknown degree')
    witness = data['degree_witness']
    need(pure_coefficient(p, witness['monomial'], vs) == const(witness['coefficient']),
         'uniform nonzero coefficient certificate')
    return {
        'name': data['name'],
        'unknowns': len(vs), 'residuals': len(rows),
        'exact_degree': degree(p, vs),
        'formal_monomials_in_unknowns_and_ports': len(p),
        'unknown_monomials_with_polynomial_port_coefficients': len(set(
            tuple(x for x in m if x in vs) for m in p)),
        'uniform_degree_witness': witness,
    }


def load(name):
    return json.loads((G / name).read_text())


def audit_packets():
    source = load('upstream/residue/dependencies/quartic41.json')
    need(source['variables'][31:] == ['u', 'FA_pos1', 'FA_pos2', 'FA_pos3',
         'FC_pos1', 'FC_pos2', 'FC_pos3', 'eta_zeta_pos1', 'eta_zeta_pos2', 'eta_zeta_pos3'],
         'retained Q41 coordinate order')
    old = list(map(parse, source['residuals']))
    qpoly = parse('beta*J+1')
    Rpoly = parse('((beta*J)*(beta*J+1-F)+alpha)*((beta*J+1)**2-1)+(MC+(beta*J+1)*MF)*J')
    index = substitute(old[12], {'L': add(mul(qpoly,qpoly),const(-1)), 'N':power(qpoly,3)})
    need(index == add(parse('eta+zeta-1-h*E'),neg(Rpoly)), 'exact signed packing/index exposure')
    need(old[13] == parse('(K0+4*w_scale)*(beta*J+1-F-alpha)-z*beta*J-F'),
         'exact shifted transport convention')
    need(substitute(old[7], {'P':parse('(eta+zeta)*(1+X*Y**2)')}) ==
         parse('tau**2-X*Y**2*(X*Y**2+1)*(eta+zeta)**2-1'),
         'first Pell residual identity')
    need(substitute(old[21], {'Baux':parse('I**2'), 'g':parse('y**2-V**2')}) ==
         parse('I**2*V**2-(I**2-1)*y**2-1'), 'auxiliary norm identity')
    need(old[22] == parse('X-2*u**2'), 'exact deleted square row')
    need(old[23] == parse('F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)'),
         'exact first deleted common-sign row')
    need(old[24] == parse('F*(beta*J+1-F-alpha)-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)'),
         'exact second deleted common-sign row')
    base = old[:22] + old[25:]
    remove = {'u'} | {prefix + str(i) for prefix in ('FA_pos', 'FC_pos') for i in (1, 2, 3)}
    variables = [v for v in source['variables'] if v not in remove] + ['cone1', 'cone2', 'cone3']
    q = '(beta*J+1)'
    C = '(' + q + '-F-alpha)'
    positive = '(1+cone1**2+cone2**2+cone3*(cone3+1))'
    U, V = '(cone_A*F)', '(cone_B*' + C + ')'
    xx, yy, zz = '(beta*F)', '(Walpha*alpha)', '(WC*' + C + ')'
    guards = {
        'determinant': parse(U + '*' + V + '-(' + q + '-' + U + '-' + V + ')**2-' + positive),
        'cone': parse('2*(' + xx + '*' + yy + '+' + xx + '*' + zz + '+' + yy + '*' + zz + ')-'
                      + xx + '**2-' + yy + '**2-' + zz + '**2-' + positive),
    }
    metrics = []
    elimination = []
    for kind, guard in guards.items():
        composed = base + [guard]
        for variant, changes, rename in (
            ('direct', {'X': parse('3*X3-1')}, {'X': 'X3'}),
            ('affine', {'J': parse('3*J3+1'), 'w_scale': parse('3*w3+1')},
             {'J': 'J3', 'w_scale': 'w3'}),
        ):
            name = kind + '37_quartic_' + variant + '.json'
            data = load(name)
            expected = [substitute(r, changes) for r in composed]
            need(list(map(parse, data['residuals'])) == expected, name + ' exact source composition')
            need(data['variables'] == [rename.get(v, v) for v in variables], name + ' exact coordinates')
            need(data['fixed_numerals'] == source['fixed_numerals'] +
                 (['cone_A', 'cone_B'] if kind == 'determinant' else ['Walpha', 'WC']),
                 name + ' complete expected port tuple')
            metrics.append(metric(data))
        parent_name = kind + '37_quartic_affine.json'
        parent = load(parent_name)
        prows = list(map(parse, parent['residuals']))
        for suffix, expected_deleted, expected_count in [('31_sextic', 6, 31), ('26_octic', 11, 26)]:
            name = kind + suffix + '.json'
            data = load(name)
            need(data['parent'] == parent_name, name + ' exact parent')
            sub = {k: parse(v) for k, v in data['full_parent_restoration'].items()}
            retained = set(data['variables'])
            ports = set(data['fixed_numerals'])
            need(set().union(*(symbols(v) for v in sub.values())) <= retained | ports,
                 name + ' all restorations are integer polynomials in retained inputs')
            derived = [substitute(r, sub) for r in prows]
            deleted = [i for i, row in enumerate(derived) if not row]
            need(len(deleted) == expected_deleted, name + ' exact identically deleted rows')
            need([r for r in derived if r] == list(map(parse, data['residuals'])),
                 name + ' all surviving residuals exact')
            gone = set(parent['variables']) - retained
            added = retained - set(parent['variables'])
            need(len(retained) == expected_count and gone == set(sub), name + ' coordinate accounting')
            if suffix == '31_sextic':
                need(added == {'tau_tail'} and sub['tau'] == parse('tau_tail+E*(c-eta)'),
                     name + ' triangular invertible root change')
                need(substitute(sub['tau'], {'tau_tail': parse('tau-E*(c-eta)')}) == parse('tau'),
                     name + ' two-sided root inverse')
            else:
                need(not added, name + ' only forget/restore maps')
            metrics.append(metric(data))
            elimination.append({'name': data['name'], 'deleted_parent_rows_zero_based': deleted,
                                'eliminated_old_coordinates': sorted(gone), 'added_coordinates': sorted(added)})
    return metrics, elimination


def native_recipe():
    """Direct implementation of the prose recipe, not an author builder import."""
    tiles = load('upstream/source34/wang943_tiles.json')
    need(len(tiles) == 943 and tiles[0] == [2, 435, 3, 1], 'literal ordered tile input')
    c = {}
    for i, tile in enumerate(tiles):
        c[i] = 1 + sum(((x + 512) >> j & 1) << (10 + 2*(10*t+j))
                       for t, x in enumerate(tile) for j in range(10)) + sum(1 << (10 + 2*j) for j in range(40, 44))
    for t, offset in enumerate((1020, 1000, 980, 960)):
        for j in range(10):
            c[offset + 2*j] = 1 << (10 + 2*(10*t+j))
    for j, e in enumerate((1095, 1096, 2195, 3296), 40):
        c[e] = 1 << (10 + 2*j)
    c[1063] = c[1064] = 0
    need(len(c) == 989, 'full 989-position native support')
    d = 1064921
    B = 1 << d
    beta = B - 1
    rho = 1 << 121
    DC = sum(1 << (121*e) for e in (40, 41, 1100, 2200)) + sum(
        coeff << (121*(shift-e)) for e, coeff in c.items() for shift in (4393, 5495))
    MC = beta - sum(1 << (121*e) for e in c if e != 1) - (2 << (121*1063))
    mu = 1022 + sum(1 << (10 + 2*j) for j in range(44))
    padding = sum(((1 << 119)-1) << (121*e) for e in range(8792, 8799)) + (((1 << 27)-1) << (121*8799))
    MFn = 4 + (mu << (121*4393)) + (mu << (121*5495)) + sum(
        1 << (121*e) for j in range(10) for e in (1000+2*j, 1021+2*j)) + (1 << (121*2195)) + (1 << (121*3296)) + padding
    K0 = DC + (rho << d)
    T = DC + rho + 1
    expected = {'beta': beta, 'K0': K0, 'MC': MC, 'MF': MFn+beta,
                'cone_A': 1 << 1113, 'cone_B': 1 << 666104,
                'Walpha': 2*T*(1 << (121*3296)), 'WC': T*beta}
    need(0 < MC < beta < MFn + beta < 2*beta, 'authentic packing mask bounds')
    need(beta % 3 == 1 and d % 2 == 1 and beta >= 17, 'radix hypotheses')
    c0 = c[0]
    need(c0 == 105534389824824194647382298625, 'top determinant coefficient')
    need(1 << 96 <= c0 < c0+1 <= 3*(1 << 95) < 1 << 97 < rho, 'determinant leading coefficient bounds')
    need(121*8791+1113 == d-97 and 121*3296+666104 == d-1, 'determinant balancing exponents')
    mass = 991*(2*sum(c.values())+6)
    need(6*sum(c.values())+18 < mass and 4*mass+8 < rho, 'universal canonical F carry bound')
    need(2*(T+1)*((1 << (121*3296))+(1 << (121*2196))) < beta, 'actual cone balancing numeral bound')
    binding = load('COEFFICIENT_BINDING.json')
    upstream = load('upstream/residue/dependencies/PAYLOAD_BINDING.json')['payloads']
    result = {}
    for name, n in expected.items():
        path = G / binding['payloads'][name]['path']
        raw = gzip.decompress(path.read_bytes())
        need(raw and raw[-1] != 0, name + ' minimal unsigned little-endian representation')
        sha = hashlib.sha256(raw).hexdigest()
        need(int.from_bytes(raw, 'little') == n, name + ' full independent recipe equality')
        record = binding['payloads'][name]
        need(sha == record['raw_sha256'] and n.bit_length() == record['bits'] and len(raw) == record['raw_bytes'],
             name + ' exact binding receipt')
        need(hashlib.sha256(path.read_bytes()).hexdigest() == record['gzip_sha256'], name + ' compressed integrity')
        if name in ('beta', 'K0', 'MC', 'MF'):
            oldname = {'K0': 'K', 'MF': 'MF_source'}.get(name, name)
            need(sha == upstream[oldname]['sha256'], name + ' inherited complete-tuple identity')
        result[name] = {'bits': n.bit_length(), 'raw_bytes': len(raw), 'raw_sha256': sha}
    totals = {kind: sum(result[n]['raw_bytes'] for n in ('beta','K0','MC','MF') + extras)
              for kind, extras in [('determinant', ('cone_A','cone_B')), ('cone', ('Walpha','WC'))]}
    need(totals == {'determinant': 615883, 'cone': 881696}, 'full route payload sizes')
    # Local counterexamples refute overstrong transfer claims, not the new full systems.
    q = beta + 1
    bad_det = expected['cone_A']*expected['cone_B'] - (q-expected['cone_A']-expected['cone_B'])**2
    need(bad_det < 0 and beta-1 > 0, 'new determinant does not contain every common-sign triple')
    return result, totals, expected


def audit_specialized_support(metrics, values):
    """Nonzero residues certify each actual coefficient is nonzero exactly.

    Primality is unnecessary: a nonzero residue modulo any integer >1 is
    enough. This is not an inference from finite evaluations of unknowns.
    """
    moduli = (1000000007, 1000000009, 1000000033)
    for item in metrics:
        data = load(item['name']+'.json')
        variables = set(data['variables'])
        expanded = sos(list(map(parse, data['residuals'])))
        groups = defaultdict(dict)
        for m, coefficient in expanded.items():
            unknown_part = tuple(x for x in m if x in variables)
            port_part = tuple(x for x in m if x not in variables)
            groups[unknown_part][port_part] = coefficient
        covered_by = defaultdict(int)
        for unknown_part, coefficient_polynomial in groups.items():
            for modulus in moduli:
                residue = 0
                for monomial, coefficient in coefficient_polynomial.items():
                    term = coefficient % modulus
                    for port in monomial:
                        term = term * (values[port] % modulus) % modulus
                    residue = (residue + term) % modulus
                if residue:
                    covered_by[modulus] += 1
                    break
            else:
                raise RuntimeError('No exact nonvanishing certificate for '+item['name']+' '+str(unknown_part))
        item['exact_monomials_after_authentic_numeral_specialization'] = len(groups)
        item['nonzero_coefficient_residue_certificate_counts'] = dict(covered_by)


def algebraic_lemmas():
    left = parse('(2*(U-1)*Z-5)**2-(U-3)*(4*U*Z**2+2)')
    right = parse('4*(U+1)*Z**2-20*(U-1)*Z+31-2*U')
    need(left == right, 'all-sign Pell ratio identity')
    shifted = substitute(right, {'U': parse('64+u'), 'Z': parse('6+z')})
    need(all(c > 0 for c in shifted.values()), 'positive-coefficient universal ratio certificate')
    cone = parse('2*(x*y+x*z+y*z)-x*x-y*y-z*z')
    need(cone == parse('4*x*y-(z-x-y)**2'), 'cone discriminant identity')
    need(cone == parse('-(x-y)**2+2*z*(x+y)-z*z'), 'mixed-sign cone exclusion')
    vertices = []
    for x in (1,2):
        for y in (1,2):
            for z in (1,2):
                vertices.append(substitute(cone, {'x': const(x), 'y': const(y), 'z': const(z)}).get((),0))
    need(min(vertices) == 3, 'factor-two cone box vertices')
    need(parse('(s+x)*(s+y)-(x+y)**2') == parse('s*s+s*(x+y)-x*x-y*y-x*y'),
         'determinant canonical expansion')
    # A=D=1, F=C=2, q=3 gives a positive determinant but alpha=-1.
    need(2*2-(3-2-2)**2 == 3 and 3-2-2 == -1, 'scale >=2 hypothesis is essential')
    need((-2**3) % 3 == 1 and (2**3) % 3 == 2, 'orientation selects positive sign at odd rank')
    return {'ratio_identity': True, 'ratio_shift_all_coefficients_positive': True,
            'cone_vertices': vertices,
            'negative_controls': {
                'unscaled_determinant_does_not_force_alpha_sign': {'A':1,'D':1,'F':2,'C':2,'q':3,'alpha':-1,'G':3},
                'canonical_restriction_is_not_all_common_sign_triples': 'q=beta+1,F=C=1,alpha=beta-1 has authentic G<0',
                'wrong_residue_would_choose_negative_power': {'R':3,'X':-8,'X_mod_3':1},
            }}


def main():
    receipt = load('UPSTREAM_COPY_RECEIPT.json')
    for name, sha in receipt['sha256'].items():
        need(hashlib.sha256((G/'upstream'/name).read_bytes()).hexdigest() == sha,
             'retained upstream source integrity: ' + name)
    metrics, eliminations = audit_packets()
    payloads, totals, values = native_recipe()
    audit_specialized_support(metrics, values)
    lemmas = algebraic_lemmas()
    bound_files = sorted([p for p in G.glob('*.json') if p.name not in ('METRICS.json',)] +
                         list((G/'upstream').rglob('*.md')) +
                         [G/'build.py', G/'build_coefficients.py', G/'PROOF.md', G/'README.md', G/'section.tex'])
    hashes = {str(p.relative_to(G)): hashlib.sha256(p.read_bytes()).hexdigest() for p in bound_files}
    result = {'status':'PASS', 'implementation':'Independent standard-library AST and sparse polynomial ring; no author-builder imports',
              'optimized_python':not __debug__, 'metrics':metrics, 'exact_eliminations':eliminations,
              'independent_native_recipe':payloads, 'payload_raw_bytes':totals,
              'algebraic_lemmas_and_negative_controls':lemmas, 'reviewed_file_sha256':hashes,
              'scope':'Exact finite algebra and coefficient audit only. Unbounded signed soundness and simultaneous canonical completeness are reviewed separately in MATHEMATICAL_REVIEW.md. No global minimum or new kernel certificate.'}
    path = HERE / ('CHECKS_OPTIMIZED.json' if not __debug__ else 'CHECKS.json')
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status':result['status'], 'metrics':metrics, 'payload_raw_bytes':totals}, indent=2))


if __name__ == '__main__':
    main()
