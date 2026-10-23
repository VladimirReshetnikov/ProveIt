#!/usr/bin/env python3
"""Deterministic division-free circuits for the integral-root constructions.

Only Python's standard library is used.  Every binary +, -, * is charged;
constant leaves and references to previous gates are free.  This program
defines finite polynomials.  It neither searches for a ZFC refutation nor
tests the consistency of ZFC.
"""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PORTS = ['beta', 'K0', 'MC', 'MF']


class Circuit:
    def __init__(self):
        self.rows, self.cache = [], {}

    def gate(self, op, x, y, name=None):
        pair = sorted((x, y), key=lambda a: (str(type(a)), str(a))) if op in ('+', '*') else (x, y)
        key = (op, *pair)
        if key in self.cache:
            return self.cache[key]
        name = name or 'g' + str(len(self.rows))
        if any(row[0] == name for row in self.rows):
            raise ValueError('Repeated gate name: ' + name)
        self.rows.append([name, op, x, y])
        self.cache[key] = name
        return name

    def add(self, x, y, name=None): return self.gate('+', x, y, name)
    def sub(self, x, y, name=None): return self.gate('-', x, y, name)
    def mul(self, x, y, name=None): return self.gate('*', x, y, name)
    def sq(self, x, name=None): return self.mul(x, x, name)

    def live(self, outputs):
        needed = set(outputs)
        for name, op, x, y in reversed(self.rows):
            if name in needed:
                needed.update((x, y))
        return [row for row in self.rows if row[0] in needed], needed


def build(degree, certificate=False):
    if degree not in (24, 26, 30):
        raise ValueError('Unknown construction')
    d = Circuit()
    add, sub, mul, sq = d.add, d.sub, d.mul, d.sq
    both = degree in (24, 26)
    witnesses = (['j', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 'X', 'Y',
                  'r', 'eta', 'zeta', 'u', 'gamma'] if both else
                 ['J', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 'w', 'Y',
                  'r', 'eta', 'zeta', 'u', 'gamma'])
    J = add(mul(3, 'j', 'triple_j'), 1, 'Jold') if both else 'J'
    qm = mul('beta', J, 'qm')
    q = add(qm, 1, 'q')
    q2 = sq(q, 'q2')
    q3 = mul(q2, q, 'q3')
    q6 = sq(q3, 'q6')
    qF = sub(q, 'F', 'qF')
    C = sub(qF, 'alpha', 'C')
    X = 'X' if both else mul('w', q, 'Xvalue')
    Y = 'Y'
    E = mul(X, Y, 'E')
    k = add('eta', 'zeta', 'k')
    kY = mul(k, Y, 'kY')
    c = add(kY, 'eta', 'c')
    c2 = sq(c, 'c2')
    a = add(E, Y, 'a')
    H = add(mul(4, a, 'four_a'), 3, 'H')
    Delta = add(sq(a, 'a2'), H, 'Delta')
    ac = mul(a, c, 'ac')
    Z = add(X, mul('gamma', H, 'gammaH'), 'Z')
    D0 = add(ac, Z, 'D0')
    ell = mul(E, kY, 'ell')
    ell_r = add(ell, 'r', 'ell_r')
    if not certificate:
        first_num = add(mul(q3, ell_r), Y, 'first_num')
        first_rhs = add(mul(ell, add(ell, k)), 1, 'first_rhs')
        A = sub(sq(first_num), mul(q6, first_rhs), 'A')
    else:
        # Exact identity (q^3(ell+r)+Y)^2-q^6(ell(ell+k)+1).
        ngap = add(sq('r'), mul(ell, sub(mul(2, 'r'), k)), 'first_gap')
        cross = mul(mul(2, q3), mul(ell_r, Y), 'first_cross')
        A = add(add(mul(q6, sub(ngap, 1)), cross), sq(Y), 'A')
    if certificate:
        N1 = sub(add(mul(mul(2, ac), Z), sq(Z)), mul(H, c2), 'N1')
    else:
        N1 = sub(sq(D0), mul(Delta, c2), 'N1')
    if both:
        XH = mul(X, H, 'XH')
        if not certificate:
            main_num = add(mul(q, D0), XH, 'main_num')
            B = sub(sq(main_num), mul(q2, add(mul(Delta, c2), 1)), 'B')
        else:
            # Exact cancellation identity for the cleared main norm.
            B = add(add(mul(q2, sub(N1, 1)),
                        mul(mul(2, q), mul(D0, XH))), sq(XH), 'B')
    R = add(mul(add(mul(qm, qF), 'alpha'), sub(q2, 1)),
            mul(add('MC', mul(q, 'MF')), J), 'R')
    kmhE = sub(k, mul('h', E), 'kmhE')
    Rhat = sub(kmhE, 1, 'Rhat') if degree == 24 else R
    if both:
        transport_inner = sub(add(mul('K0', C), qF), mul('z', qm))
        transport_num = add(mul(q, transport_inner), mul(X, C), 'transport_num')
        if degree == 24:
            index_res = sub(Rhat, R, 'index_res')
            transport_res = sub(transport_num, q, 'transport_res')
            residuals = [A, B, index_res, transport_res]
        else:
            Nk = sub(kmhE, R, 'Nk')
            coupled = sub(mul(Nk, transport_num), q, 'coupled')
            residuals = [A, B, coupled]
    else:
        Nk = sub(kmhE, R, 'Nk')
        Nt = sub(add(mul(add('K0', 'w'), C), qF), mul('z', qm), 'Nt')
        paired = sub(mul(mul(N1, Nk), Nt), 1, 'paired')
        residuals = [A, paired]
    f2 = sq('f', 'f2')
    U = mul(Delta, sub(f2, 1), 'U')
    I = mul('i', c2, 'I')
    strong = sub(sq(I), U, 'strong')
    V = sub(mul(f2, sub(mul(c, 'T'), Rhat)), c, 'V')
    vu = add(V, 'u', 'vu')
    auxiliary = sub(sub(sq(vu), mul(U, mul('u', add(mul(2, V), 'u')))), 1, 'auxiliary')
    residuals.extend([auxiliary, strong])
    squares = [sq(x, 'residual_square_' + str(i)) for i, x in enumerate(residuals)]
    out = squares[0]
    for i, x in enumerate(squares[1:], 1):
        out = add(out, x, 'sum_' + str(i))
    rows, needed = d.live([out])
    if not set(witnesses + PORTS) <= needed:
        raise ValueError('An advertised input is dead')
    core, _ = d.live(residuals)
    packet = {
        'name': 'fifteen_positive_degree_' + str(degree),
        'domain': 'strictly positive integers',
        'witnesses': witnesses,
        'fixed_numerals': PORTS,
        'coefficient_binding_file': '../coefficients/COEFFICIENT_BINDING.json',
        'port_aliases': {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'},
        'source': rows, 'residuals': residuals, 'output': out,
        'exact_degree': degree,
        'operations': len(rows), 'operation_breakdown': dict(Counter(r[1] for r in rows)),
        'residual_evaluator_operations': len(core),
        'degree_certificate_only': certificate,
        'proof': '../report/report.pdf',
        'status': 'Ordinary proof using the explicitly pinned inherited compiler; no new end-to-end proof-assistant certificate.'
    }
    return packet


def main():
    target = ROOT / 'circuits'
    target.mkdir(exist_ok=True)
    receipt = []
    for degree in (24, 26, 30):
        for cert in (False, True):
            packet = build(degree, cert)
            name = 'p15_degree' + str(degree) + ('_degree_certificate' if cert else '') + '.json'
            (target/name).write_text(json.dumps(packet, indent=2) + '\n')
            receipt.append({'file': name, 'degree': degree, 'operations': packet['operations'],
                            'certificate_only': cert, 'residual_evaluator_operations': packet['residual_evaluator_operations']})
    (ROOT/'certificates'/'BUILD.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()

