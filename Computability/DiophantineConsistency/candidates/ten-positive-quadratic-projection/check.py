#!/usr/bin/env python3
"""Independent literal norm/projection certificates and finite proof controls.

Imports no candidate builder or author verifier. Unbounded arithmetic
claims and witness maps are proved in PROOF.md; finite tests supplement them.
"""
from collections import Counter
from copy import deepcopy
from fractions import Fraction
import gzip
from hashlib import sha256
import importlib.util
import json
from math import factorial
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT_SHA = 'b53f25dc8f5e8430cd2c1bece0c396cc315412092d6a3142db8d4882011f0060'


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def digest(raw):
    return sha256(raw).hexdigest()


def evaluate(rows, inputs, prime=None):
    env = dict(inputs)
    def val(x):
        return x if type(x) is int else env[x]
    for name, op, a, b in rows:
        u, v = val(a), val(b)
        need(op in ('+', '-', '*'), 'binary arithmetic gate')
        out = u+v if op == '+' else u-v if op == '-' else u*v
        env[name] = out if prime is None else out % prime
    return env


def pell(A, n):
    """Integer chi,psi for every signed index, by binary ring powering."""
    positive = abs(n)
    D = A*A-1
    x, y, u, v = 1, 0, A, 1
    while positive:
        if positive & 1:
            x, y = x*u+D*y*v, x*v+y*u
        u, v = u*u+D*v*v, 2*u*v
        positive //= 2
    return x, y if n >= 0 else -y


def finite_lemma_controls():
    fold_count = main_count = odd_count = 0
    for A in range(3, 13):
        D = A*A-1
        for m in range(1, 11):
            f, I = pell(A, m)
            need(f > 2*I, 'strong-root height')
            for v in range(-6*m, 6*m+1):
                quotient, t = divmod(v, 2*m)
                p = min(t, 2*m-t)
                eps = -1 if quotient % 2 else 1
                need(0 <= p <= m and (pell(A, v)[1]-eps*pell(A, p)[1]) % f == 0,
                     'all signed-index psi folds in finite range')
                fold_count += 1
            if m > 6:
                continue
            S = D*I
            for h in range(8*m+1):
                v = 2*h+1
                chi, y = pell(S, v)
                need(chi % S == 0, 'odd-index extraction exact division')
                absV = chi//S
                need(S*S*absV*absV-(S*S-1)*y*y == 1, 'actual auxiliary Pell pair')
                need((absV-(-1)**h*pell(A, v)[1]) % f == 0,
                     'odd polynomial reduction at1-A^2')
                odd_count += 1
                for sign in (-1, 1):
                    V = sign*absV
                    c = (-V) % f
                    if not 0 < c <= I:
                        continue
                    options = [p for p in range(1, m+1) if pell(A, p)[1] == c]
                    need(bool(options), 'every admitted small c is an actual main Pell value')
                    main_count += 1
    heights = 0
    for q in (32, 34, 64, 128, 1024):
        for r in (30, 31, 48, 49, 63, 100):
            R = 2*r+1
            for X in (q, q+1, q*q):
                need(q**4*2**(2*R+2)*X*X < X**(r+1), 'whole-product height at stated range')
                D = q**3*(q-1)*(X-2**R)*(2**R*X+1)
                need(abs(D) < q**4*2**(2*R+2)*X*X, 'absolute whole-product bound')
                heights += 1
    need(32**4*2**(2*(2*29+1)+2)*32**2 == 32**30,
         'r29 boundary gives equality and cannot license strict bound')
    need(not 16**4*2**(2*(2*30+1)+2)*16**2 < 16**31,
         'q16 boundary rejected: the strengthened q32 hypothesis is necessary here')
    projections = 0
    for A in range(3, 18):
        H, ap = 4*A-5, A-2
        for R in range(1, 31):
            Dm, c = pell(A, R)
            B = 2**R
            need((Dm-ap*c-B) % H == 0 and (B*(Dm+ap*c)-1) % H == 0,
                 'both Pell projections with cleared inverse')
            for X in (1, 2, B-1, B, B+1, B*B):
                K = X*(X+2*ap*c)-1
                need((B*K-(X-B)*(B*X+1)) % H == 0,
                     'squared projection product with no primewise cancellation')
                projections += 1
    return dict(signed_index_psi_folds=fold_count,
        auxiliary_odd_polynomial_reductions=odd_count,
        recovered_main_classifications=main_count,
        whole_product_height_cases=heights, cleared_projection_cases=projections,
        missing_q32_and_r30_hypotheses_rejected=True,
        scope='Finite diagnostic controls only; PROOF.md gives all-index folding and unbounded classification/height arguments.')


def line_degree(values, prime):
    degree, difference = -1, None
    values = list(values)
    level = 0
    while values:
        if values[0]:
            degree, difference = level, values[0]
        values = [(b-a) % prime for a, b in zip(values, values[1:])]
        level += 1
    return degree, difference


def omega_top(e, prime):
    q = 2*e['beta']*e['j'] % prime
    mu = q*q % prime
    a = e['w']*q*e['Y'] % prime
    Am1 = mu*a % prime
    Delta = Am1*Am1 % prime
    H = 4*Am1 % prime
    c = (e['eta']+e['zeta'])*e['Y'] % prime
    I = e['i']*mu*c*c % prime
    Df = Delta*I*I % prime
    Q = Delta*Delta*I*I % prime
    L = 4*Am1*I % prime
    W = q*L % prime
    Bt = e['w']*(q-e['F']-e['alpha']) % prime
    M = pow(q, 8, prime)*H % prime
    Z00 = -H*pow(q, 7, prime)*W*Bt % prime
    V00 = -Df*pow(q, 3, prime)*(q-e['F']) % prime
    return 2*Q*Z00*M*V00 % prime


def main():
    raw = (HERE/'source/parent-equation.json').read_bytes()
    need(digest(raw) == PARENT_SHA, 'frozen whole122-operation parent')
    parent = json.loads(raw)
    child = load(HERE/'equation.json')
    remap = load(HERE/'PREFIX_REMAP.json')
    provenance = load(HERE/'PROVENANCE.json')
    need(remap['parent_sha256'] == child['parent_sha256'] ==
         provenance['parent_equation_sha256'] == PARENT_SHA, 'consistent complete parent pins')
    need(child['domain'] == parent['domain'] == 'strictly positive integers', 'positive domain')
    need(child['witnesses'] == parent['witnesses'] and len(set(child['witnesses'])) == 10,
         'complete unchanged ten witnesses')
    need(child['fixed_numerals'] == parent['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'],
         'whole unchanged fixed tuple')
    old, rows = parent['source'], child['source']
    old_start = next(i for i, r in enumerate(old) if r[0] == 'ab')
    new_start = next(i for i, r in enumerate(rows) if r[0] == 'ab')
    need(old_start == remap['parent_prefix_length'] == 94 and
         new_start == remap['child_prefix_length'] == 92, 'complete prefix boundaries')
    deleted = {'Dpc2', 'Dmain', 'HnX', 'P2', 'dP2', 'fd'}
    need({r['row'][0] for r in remap['deleted_prefix']} == deleted,
         'all six deleted prefix gates')
    for entry in remap['deleted_prefix']:
        need(old[entry['parent_index']] == entry['row'], 'every deleted row exactly matched')
    retained = remap['retained_prefix']
    need([r['parent_index'] for r in retained] ==
         [i for i, r in enumerate(old[:old_start]) if r[0] not in deleted],
         'all retained parent prefix rows covered in order')
    new_projection = [
        ['2apc', '*', 2, 'apc'], ['X2apc', '+', 'X', '2apc'],
        ['Kquad0', '*', 'X', 'X2apc'], ['Kquad', '-', 'Kquad0', 1]]
    need(remap['new_projection'] == new_projection, 'complete new projection formula')
    positions = [i for i, r in enumerate(rows[:new_start]) if r[0] in {x[0] for x in new_projection}]
    need([rows[i] for i in positions] == new_projection, 'literal new projection gates')
    need(sorted([r['child_index'] for r in retained]+positions) == list(range(new_start)),
         'all child prefix gates covered exactly once')
    changed_values = set()
    for entry in retained:
        i, j = entry['parent_index'], entry['child_index']
        want = ['lin', '+', 'Hn', 'Kquad'] if old[i][0] == 'lin' else old[i]
        need(rows[j] == want and entry['register'] == want[0], 'every copied/replaced prefix row')
        need(entry['definition_copied'] == (old[i] == want), 'copied-definition label')
        if old[i][0] == 'lin' or any(v in changed_values for v in want[2:] if type(v) is str):
            changed_values.add(want[0])
    need(changed_values == {'lin', 'Zpart1', 'Znum', 'Z2', 'fs'}, 'exact affected shared-prefix values')
    need(remap['replaced_tail']['parent_indices'] == list(range(94, 122)) and
         remap['replaced_tail']['child_indices'] == list(range(92, 106)) and
         remap['replaced_tail']['child_rows'] == rows[new_start:], 'complete tail replacement coverage')

    available = set(child['witnesses']+child['fixed_numerals'])
    degrees = {v:1 for v in child['witnesses']} | {v:0 for v in child['fixed_numerals']}
    dependencies = {}
    for name, op, a, b in rows:
        need(name not in available and op in ('+', '-', '*'), 'fresh binary gate')
        need(all(type(x) is int or x in available for x in (a, b)), 'topological literal circuit')
        available.add(name)
        dependencies[name] = (a, b)
        da, db = (0 if type(x) is int else degrees[x] for x in (a, b))
        degrees[name] = da+db if op == '*' else max(da, db)
    live, todo = set(), ['N']
    while todo:
        v = todo.pop()
        if type(v) is int or v in live:
            continue
        live.add(v)
        todo.extend(dependencies.get(v, ()))
    need(live == available, 'all gates, ports and witnesses live')
    counts = Counter(r[1] for r in rows)
    need(len(rows) == child['operations'] == 106 and
         dict(counts) == child['operation_breakdown'] == {'*':62, '+':26, '-':18},
         'complete106-operation census')
    need(degrees['N'] == child['syntactic_degree'] == 464 and child['exact_degree'] == 408,
         'degree contracts')
    need(all(degrees[name] == d for name, d in child['register_degrees'].items()),
         'every register degree contract')
    oracle_path = HERE/'source/independent_norm_oracle.py'
    need(digest(oracle_path.read_bytes()) == provenance['oracle_sha256'], 'independent oracle pin')
    spec = importlib.util.spec_from_file_location('independent_sparse_ring_oracle', oracle_path)
    oracle = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(oracle)
    x, a, b, c, d, omega = [oracle.variable(i) for i in range(6)]
    tail = rows[new_start:]
    norm = oracle.evaluate(tail, dict(fs=x*x, fa=a, fb=b, fc=c))['N']
    need(len(tail) == 14 and norm.t == oracle.norm_oracle(x, [a, b, c]).t,
         'complete literal octic equals independent8-conjugate product')
    centered = oracle.evaluate(tail, dict(fs=x*x, fa=a, fb=b, fc=x*x-omega))['N']
    weights = (58, 78, 84, 0, 0, 102)
    weighted = {mon:sum(e*w for e, w in zip(mon, weights)) for mon in centered.t}
    top = {mon:centered.t[mon] for mon, w in weighted.items() if w == max(weighted.values())}
    need(max(weighted.values()) == 408 and top == {(0,0,0,0,0,4):1},
         'unique centered weight408 term omega^4')
    z, t, a, b, c, delta = [oracle.variable(i) for i in range(6)]
    lhs = oracle.evaluate(old[-28:], dict(fs=delta*(z+t)**2, fa=a, fb=b, fc=c, fd=delta*t*t))['N']
    rhs1 = oracle.evaluate(tail, dict(fs=delta*z*z, fa=a, fb=b, fc=c))['N']
    rhs2 = oracle.evaluate(tail, dict(fs=delta*(z+2*t)**2, fa=a, fb=b, fc=c))['N']
    need(lhs.t == (rhs1*rhs2).t, 'complete exact F16 shift factorization for witness map')
    A, c, X, Dm, B, _ = [oracle.variable(i) for i in range(6)]
    ap, H = A-2, 4*A-5
    K = X*(X+2*ap*c)-1
    Dmain = (A*A-1)*c*c+1
    need(((X+ap*c)**2-Dmain).t == (K-H*c*c).t,
         'quadratic projection equals squared main projection modulo H')
    need((B*K-(X-B)*(B*X+1)).t ==
         (X*((B*(Dm+ap*c)-1)-B*(Dm-ap*c-B))).t,
         'cleared projection product is exact linear combination of both Pell projections')
    bad = deepcopy(tail)
    bad[-1][1] = '+'
    need(oracle.evaluate(bad, dict(fs=x*x, fa=oracle.variable(1), fb=oracle.variable(2),
         fc=oracle.variable(3)))['N'].t != norm.t, 'corrupted norm sign actually evaluated and rejected')
    need((B*(K+2)-(X-B)*(B*X+1)).t !=
         (X*((B*(Dm+ap*c)-1)-B*(Dm-ap*c-B))).t,
         'Kquad plus1 corruption rejected by exact projection identity')

    coefficients, coefficient_pins = {}, {}
    need(child['coefficient_binding'] == parent['coefficient_binding'] ==
         load(HERE/'coefficients/BINDING.json'), 'whole unchanged coefficient binding')
    for name, pin in child['coefficient_binding']['ports'].items():
        blob = (HERE/'coefficients'/pin['file']).read_bytes()
        raw = gzip.decompress(blob)
        need(digest(blob) == pin['gzip_sha256'] and digest(raw) == pin['raw_sha256'],
             'complete authentic port '+name)
        coefficients[name] = int.from_bytes(raw, 'little')
        need(coefficients[name].bit_length() == pin['bits'], 'port bit width')
        coefficient_pins[name] = dict(raw_sha256=digest(raw), bits=pin['bits'])
    beta = coefficients['beta']
    need(beta == 2**590069-1 and beta % 2 == 1 and beta >= 11,
         'actual beta licenses q>=32 and exact leading form')
    need(0 < coefficients['MC'] < beta < coefficients['MF'] < 2*beta and coefficients['K0'] > 0,
         'actual complete fixed-port box')
    rng = random.Random(106408)
    contracts = 0
    for prime in (1009, (1 << 127)-1):
        for _ in range(50):
            inputs = {name:rng.randrange(-20, 21) for name in child['witnesses']}
            inputs.update({name:value % prime for name, value in coefficients.items()})
            old_env, e = evaluate(old, inputs, prime), evaluate(rows, inputs, prime)
            need(all(old_env[r['register']] == e[r['register']] for r in retained
                     if r['register'] not in changed_values), 'every unaffected shared-prefix value')
            K = e['X']*(e['X']+2*e['ap']*e['c'])-1
            want = (e['P1']*e['mu']**2*(e['Hp']*(e['n']+e['V'])+K)
                +e['Hp']*(e['mu']**2*((e['q']-1)*e['Y']-e['q']**3*e['W']*e['Bt'])-e['P1']*e['e']))
            need(e['Kquad'] == K % prime and e['Znum'] == want % prime,
                 'independent full projected numerator formula')
            s, u, v, w = (e[name] for name in ('fs', 'fa', 'fb', 'fc'))
            sig1, sig2, sig3 = u+v+w, u*v+(u+v)*w, u*v*w
            need(e['N'] == (((s-sig1)**2-4*sig2)**2-64*sig3*s) % prime,
                 'independent complete final formula')
            contracts += 1
    slices = []
    for prime in ((1 << 127)-1, (1 << 89)-1):
        for _ in range(2):
            direction = {name:rng.randrange(1, prime) for name in child['witnesses']}
            base = {name:rng.randrange(1, prime) for name in child['witnesses']}
            ports = {name:value % prime for name, value in coefficients.items()}
            values, omega_values = [], []
            for t in range(466):
                env = evaluate(rows, ports | {name:(base[name]+t*direction[name]) % prime
                                               for name in child['witnesses']}, prime)
                values.append(env['N'])
                omega_values.append((env['fs']-env['fc']) % prime)
            degree, difference = line_degree(values, prime)
            dw, diffw = line_degree(omega_values[:132], prime)
            top = omega_top(ports | direction, prime)
            need(degree == 408 and dw == 102, 'actual tuple N/omega attained degrees')
            need(difference*pow(factorial(408) % prime, -1, prime) % prime == pow(top, 4, prime),
                 'new leading coefficient equals actual omega0^4')
            need(diffw*pow(factorial(102) % prime, -1, prime) % prime == top,
                 'actual omega leading coefficient unchanged')
            slices.append(dict(prime_bits=prime.bit_length(), degree_N=degree, degree_omega=dw,
                               leading_coefficient_matches_omega0_fourth_power=True))
    lemma_controls = finite_lemma_controls()
    display = load(HERE/'DISPLAY_BINDING.json')
    proof_pin = digest((HERE/'PROOF.md').read_bytes())
    need(display['equation_sha256'] == digest((HERE/'equation.json').read_bytes()) and
         display['literal_registers'] == rows and display['norm_rows'] == tail,
         'complete display formula snapshot')
    need(display['proof_sha256'] == proof_pin, 'same proof in display snapshot')
    for name in ('proof-peer.json', 'proof-peer-optimized.json'):
        peer = load(HERE/'source'/name)
        need(peer['status'] == 'PASS' and peer['proof_sha256'] == proof_pin,
             'independent ordinary peer receipt binds this full proof')
    for path, pin in load(HERE/'BUILD.json')['sha256'].items():
        need(digest((HERE/path).read_bytes()) == pin, 'generated artifact seal '+path)
    for path in ('parent-check.json', 'parent-check-optimized.json'):
        receipt = load(HERE/'source'/path)
        need(receipt['status'] == 'PASS' and receipt['equation_sha256'] == PARENT_SHA,
             'frozen122-operation parent receipt')
    inherited = load(HERE/'source/original-replays.json')
    need(inherited['status'] == 'PASS' and inherited['source_unchanged'] and
         all(r['exit_code'] == 0 for r in inherited['replays']), 'full original normal/-O author receipts')
    report = dict(status='PASS', optimized_python=bool(sys.flags.optimize), positive_variables=10,
        operations=106, operation_breakdown=dict(counts), syntactic_degree=464, exact_degree=408,
        complete_remapped_parent_prefix=len(retained), unaffected_shared_prefix_registers=len(retained)-len(changed_values),
        deleted_prefix_gates=sorted(deleted), new_prefix_gates=4, norm_tail_operations=14,
        universal_norm_terms=len(norm.t), centered_norm_terms=len(centered.t), unique_weight408_term='omega^4',
        F16_shift_factorization_terms=len(lhs.t), exact_quadratic_projection_cuts=True,
        whole_formula_modular_controls=contracts, actual_tuple_degree_controls=slices,
        lemma_controls=lemma_controls, norm_and_projection_corruptions_rejected=True,
        whole_fixed_tuple=coefficient_pins,
        parent_equation_sha256=PARENT_SHA, equation_sha256=digest((HERE/'equation.json').read_bytes()),
        ordinary_proof_sha256=proof_pin, independent_ordinary_peer_normal_optimized=True,
        scope='Exact finite symbolic norm/shift/projection identities, complete literal remap/topology/liveness, authentic full coefficient tuple, actual leading-form controls and supplemental lemma diagnostics. Unbounded positive-zero equivalence is PROOF.md; no claimed full-polynomial identity with parent and no Lean/internal-ZFC proof.')
    target = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    (HERE/target).write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
