#!/usr/bin/env python3
"""Build and independently audit the 27-integer weighted-root polynomial.

Input is the pinned package-09 circuit; outputs are scratch artifacts for
incorporation into the parent report. The semantic proof is in the sibling
INTEGER27_PROOF.md. All checks remain active with python -O.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
import json
import random

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / 'data'
BASE = ROOT / 'upstream/arithmetic/polynomial13_84.json'


def require(test, msg):
    if not test:
        raise ValueError(msg)


def evaluate(source, values):
    vals = dict(values)
    for n, op, a, b in source:
        a = a if type(a) is int else vals[a]
        b = b if type(b) is int else vals[b]
        vals[n] = a + b if op == '+' else a - b if op == '-' else a * b
    return vals


def validate(p):
    known = set(p['witnesses'] + p['fixed_numerals'])
    for n, op, a, b in p['source']:
        require(n not in known, 'duplicate register ' + n)
        require(op in ('+', '-', '*'), 'invalid operation')
        require(all(type(x) is int or x in known for x in (a, b)), 'undefined operand')
        known.add(n)
    if 'output' in p:
        need = {p['output']}
    else:
        need = {x for row in p['comparisons'] for x in row if type(x) is str}
    for n, op, a, b in reversed(p['source']):
        if n in need:
            need.update(x for x in (a, b) if type(x) is str)
    require(all(n in need for n, _, _, _ in p['source']), 'dead gate')
    require(set(p['witnesses'] + p['fixed_numerals']) <= need, 'dead port')
    c = Counter(row[1] for row in p['source'])
    p['ledger'] = dict(operations=len(p['source']), multiplications=c['*'],
                       additions_subtractions=c['+'] + c['-'], all_gates_live=True,
                       all_ports_live=True)


def build():
    base = json.loads(BASE.read_text())
    src = []
    for n, op, a, b in base['source']:
        if n == 'Qr':
            src += [['ic2', '*', 'i', 'c2'], ['I2', '*', 'ic2', 'ic2']]
        elif n in ('Q', 'ic2'):
            continue
        elif n == 'Dm1':
            src.append(['Dm1', '*', 'A', 'I2'])
        elif n == 'D':
            src += [[n, op, a, b], ['Q', '*', 'A', 'Dm1']]
        elif n == 'M':
            src += [['M0', '+', 'I2', 'v2'], ['M', '*', 2, 'M0']]
        else:
            src.append([n, op, a, b])
    prefix = []
    positive = ['Jrep', 'F', 'alpha', 'transport_quotient', 's', 'eta', 'zeta']
    witnesses = []
    for x in positive:
        xs = [x + '_0', x + '_1', x + '_2']
        witnesses.extend(xs)
        prefix += [
            [x + '_sq0', '*', xs[0], xs[0]],
            [x + '_tri', '+', x + '_sq0', xs[0]],
            [x + '_sq1', '*', xs[1], xs[1]],
            [x + '_sum1', '+', x + '_tri', x + '_sq1'],
            [x + '_sq2', '*', xs[2], xs[2]],
            [x + '_sum2', '+', x + '_sum1', x + '_sq2'],
            [x, '+', x + '_sum2', 1],
        ]
    witnesses += ['h', 'r_i', 'auxiliary_quotient', 'u', 'gamma', 'r_t']
    prefix += [['twice_ri', '*', 2, 'r_i'], ['i', '+', 'twice_ri', 1],
               ['w', '*', 'u', 'u'], ['twice_rt', '*', 2, 'r_t'], ['t', '+', 'twice_rt', 1]]
    p = dict(name='integer27_weighted_root_polynomial139', witnesses=witnesses,
             fixed_numerals=base['fixed_numerals'], domain='unrestricted integers',
             source=prefix + src, output='polynomial', exact_degree=1004,
             coefficient_binding={'manifest':'../COEFFICIENT_BINDING.json','fixed_tuple':'pruned_t4','mask_convention':'MF is native mask plus B minus 1'},
             proof='../proofs/INTEGER27_PROOF.md')
    validate(p)
    require(len(witnesses) == 27, 'wrong witness count')
    require(p['ledger']['operations'] == 139, 'wrong operation count')
    cut = next(i for i, row in enumerate(p['source']) if row[0] == 'norm13')
    system = {k: v for k, v in p.items() if k not in ('output', 'exact_degree', 'ledger')}
    system.update(name='integer27_weighted_root_system133', source=p['source'][:cut],
                  comparisons=[['norm_main', 1], ['norm_index', 1], ['norm_transport', 1],
                               ['UU2', 'sixteenC2PU']], residual_exact_degrees=[35, 13, 4, 952])
    validate(system)
    require(system['ledger']['operations'] == 133, 'wrong system operation count')
    return p, system


def independent(values):
    pos = lambda x: values[x + '_0'] ** 2 + values[x + '_0'] + values[x + '_1'] ** 2 + values[x + '_2'] ** 2 + 1
    J, F, alpha, z, s, eta, zeta = [pos(x) for x in ['Jrep', 'F', 'alpha', 'transport_quotient', 's', 'eta', 'zeta']]
    h, ri, T, u, gamma, rt = [values[x] for x in ['h', 'r_i', 'auxiliary_quotient', 'u', 'gamma', 'r_t']]
    beta, K0, MC, MF = [values[x] for x in ['Bm1', 'Kconstant', 'MC', 'MF']]
    i, w, t = 2 * ri + 1, u * u, 2 * rt + 1
    q = beta * J + 1
    Cw, X, Y = q - F - alpha, w * q, s * q ** 3
    E, k = X * Y, eta + zeta
    c, a = k * Y + eta, E + Y
    H = 4 * a + 3
    delta = a * a + H
    dm = X + a * c + gamma * H
    R = ((q - 1) * (q - F) + alpha) * (q * q - 1) + (MC + q * MF) * J
    n1, nk, nt = dm * dm - delta * c * c, k - h * E - R, (K0 + w) * Cw + q - F - z * (q - 1)
    ell, I = E * k * Y, i * c * c
    aa, dd = 1 + ell * (ell + k), 1 + delta * I * I
    qq = delta * delta * I * I
    vv, zz = c * T, c + R * dd
    d, mm = qq - 1, 2 * (I * I + vv * vv)
    ee = qq * (dd * vv * vv + zz * zz) - 1
    cc = d * (t * t + mm * mm * aa) - ee
    bb = 2 * qq * vv * zz
    uu = cc * cc + dd * bb * bb - 4 * d * d * t * t * mm * mm * aa
    res = uu * uu - dd * (2 * cc * bb) ** 2
    return [n1, nk, nt, res], n1 * nk * nt * (1 + res) - 1


def degree_line(p, seed, prime):
    rng = random.Random(seed)
    vals = {v: [rng.randrange(1, 17), rng.randrange(1, 17)] for v in p['witnesses']}
    vals.update({v: [c] for v, c in zip(p['fixed_numerals'], [31, 127, 10, 45])})
    def plus(a, b, sign):
        c = [((a[i] if i < len(a) else 0) + sign * (b[i] if i < len(b) else 0)) % prime for i in range(max(len(a), len(b)))]
        while len(c) > 1 and not c[-1]:
            c.pop()
        return c
    for n, op, a, b in p['source']:
        a = [a] if type(a) is int else vals[a]
        b = [b] if type(b) is int else vals[b]
        if op == '*':
            c = [0] * (len(a) + len(b) - 1)
            for j, x in enumerate(a):
                for k, y in enumerate(b):
                    c[j + k] = (c[j + k] + x * y) % prime
            while len(c) > 1 and not c[-1]:
                c.pop()
        else:
            c = plus(a, b, 1 if op == '+' else -1)
        vals[n] = c
    if 'output' in p:
        out = [len(vals[p['output']]) - 1]
        expected = [p['exact_degree']]
    else:
        out = [len(plus(vals[a] if type(a) is str else [a], vals[b] if type(b) is str else [b], -1)) - 1 for a, b in p['comparisons']]
        expected = p['residual_exact_degrees']
    require(out == expected, f'degree mismatch {out} != {expected}')
    return dict(prime=prime, seed=seed, degrees=out)


def root_fixtures():
    count = 0
    for rho in [3, 5, 7]:
        Q, d = rho * rho, rho * rho - 1
        chi, y = 1, 0
        for n in range(1, 6):
            chi, y = rho * chi + d * y, chi + rho * y
            if n not in (3, 5):
                continue
            require(chi % rho == 0 and y % 2 == 1, 'fixture Pell parity')
            V = -chi // rho
            for f in [-5, 2, 3, 6]:
                for v in [-2, 1, 4]:
                    D = f * f
                    z0 = v * f - V
                    for tau in [2, 3, -4]:
                        I, A = 3, tau * tau
                        M = 2 * (I * I + v * v)
                        t = M * tau + y
                        require(t % 2 == 1, 'odd primitive fixture')
                        e = Q * (D * v * v + z0 * z0) - 1
                        C = d * (t * t + M * M * A) - e
                        B = 2 * Q * v * z0
                        U = C * C + D * B * B - 4 * d * d * t * t * M * M * A
                        require(U * U == D * (2 * C * B) ** 2, 'resultant fixture')
                        if C * B != 0:
                            fr = Fraction(-U, 2 * C * B)
                            tr = Fraction(C + B * fr, 2 * d * t * M)
                            yr = t - M * tr
                            require((fr, tr, yr) == (f, tau, y), 'inverse fixture')
                            count += 1
    return count


def main():
    p, system = build()
    rng = random.Random(2700139)
    for _ in range(100):
        values = {x: rng.randrange(-3, 4) for x in p['witnesses'] + p['fixed_numerals']}
        got = evaluate(p['source'], values)
        factors, output = independent(values)
        require(got['polynomial'] == output, 'independent polynomial mismatch')
        require([got['norm_main'], got['norm_index'], got['norm_transport'], got['norm13']] == factors, 'independent residual mismatch')
    diagnostics = {}
    for packet in [p, system]:
        packet['degree_diagnostics'] = [degree_line(packet, 27139, 1000000007), degree_line(packet, 27140, 1000000009)]
        (HERE / (packet['name'] + '.json')).write_text(json.dumps(packet, indent=2) + '\n')
        diagnostics[packet['name']] = dict(witnesses=len(packet['witnesses']), ledger=packet['ledger'], degree_diagnostics=packet['degree_diagnostics'])
    receipt = dict(independent_full_formula_fixtures=100, signed_root_inverse_fixtures=root_fixtures(), circuits=diagnostics,
                   scope='Finite algebra and circuit checks only. No K215 halting witness or full formalization.')
    (ROOT / 'verification/integer27.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
