#!/usr/bin/env python3
"""Literal source-58 baseline and a one-gate transport refinement.

Every binary +, -, * is charged; fixed numeral leaves and references are
free. Certificate evaluators expose exact cancellations and are not the
counted primary evaluators. Python standard library only.
"""
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
VARIABLES = ['j', 'F', 'alpha', 'z', 'f', 'h', 'i', 'T', 'X', 'Y',
             'r', 'eta', 'zeta', 'u', 'gamma']
PORTS = ['beta', 'K0', 'MC', 'MF']


class Circuit:
    def __init__(self):
        self.rows, self.cache = [], {}

    def gate(self, op, x, y, name=None):
        pair = tuple(sorted((x, y), key=lambda a: (str(type(a)), str(a)))) if op in ('+', '*') else (x, y)
        key = (op, *pair)
        if key in self.cache:
            return self.cache[key]
        name = name or 'g' + str(len(self.rows))
        if any(row[0] == name for row in self.rows):
            raise ValueError('Repeated gate name')
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


def build(shifted=True, certificate=False):
    d = Circuit()
    add, sub, mul, sq = d.add, d.sub, d.mul, d.sq
    J = add(mul(3, 'j', 'triple_j'), 1, 'Jold')
    qm = mul('beta', J, 'qm')
    q = add(qm, 1, 'q')
    q2, q3 = sq(q, 'q2'), None
    q3 = mul(q2, q, 'q3')
    q6 = sq(q3, 'q6')
    qF = sub(q, 'F', 'qF')
    C = sub(qF, 'alpha', 'C')
    E = mul('X', 'Y', 'E')
    k = add('eta', 'zeta', 'k')
    kY = mul(k, 'Y', 'kY')
    c = add(kY, 'eta', 'c')
    c2 = sq(c, 'c2')
    a = add(E, 'Y', 'a')
    H = add(mul(4, a, 'four_a'), 3, 'H')
    Delta = add(sq(a, 'a2'), H, 'Delta')
    ac = mul(a, c, 'ac')
    Z = add('X', mul('gamma', H, 'gammaH'), 'Z')
    D0 = add(ac, Z, 'D0')
    ell = mul(E, kY, 'ell')
    ell_r = add(ell, 'r', 'ell_r')
    if not certificate:
        first_num = add(mul(q3, ell_r), 'Y', 'first_num')
        first_rhs = add(mul(ell, add(ell, k)), 1, 'first_rhs')
        A0 = sub(sq(first_num), mul(q6, first_rhs), 'A0')
    else:
        ngap = add(sq('r'), mul(ell, sub(mul(2, 'r'), k)), 'first_gap')
        cross = mul(mul(2, q3), mul(ell_r, 'Y'), 'first_cross')
        A0 = add(add(mul(q6, sub(ngap, 1)), cross), sq('Y'), 'A0')
    XH = mul('X', H, 'XH')
    if not certificate:
        main_num = add(mul(q, D0), XH, 'main_num')
        A1 = sub(sq(main_num), mul(q2, add(mul(Delta, c2), 1)), 'A1')
    else:
        N1 = sub(add(mul(mul(2, ac), Z), sq(Z)), mul(H, c2), 'N1')
        A1 = add(add(mul(q2, sub(N1, 1)),
                     mul(mul(2, q), mul(D0, XH))), sq(XH), 'A1')
    R = add(mul(add(mul(qm, qF), 'alpha'), sub(q2, 1)),
            mul(add('MC', mul(q, 'MF')), J), 'R')
    Rhat = sub(sub(k, mul('h', E)), 1, 'Rhat')
    Ak = sub(Rhat, R, 'Ak')
    if shifted:
        At = sub(mul(C, add(mul(q, 'K0'), 'X')),
                 mul(q, add('F', mul('z', qm))), 'At')
    else:
        transport_inner = sub(add(mul('K0', C), qF), mul('z', qm))
        transport_num = add(mul(q, transport_inner), mul('X', C))
        At = sub(transport_num, q, 'At')
    f2 = sq('f', 'f2')
    U = mul(Delta, sub(f2, 1), 'U')
    I = mul('i', c2, 'I')
    As = sub(sq(I), U, 'As')
    V = sub(mul(f2, sub(mul(c, 'T'), Rhat)), c, 'V')
    Aa = sub(sub(sq(add(V, 'u')),
                 mul(U, mul('u', add(mul(2, V), 'u')))), 1, 'Aa')
    residuals = [A0, A1, Ak, At, Aa, As]
    squares = [sq(x) for x in residuals]
    out = squares[0]
    for value in squares[1:]:
        out = add(out, value)
    rows, needed = d.live([out])
    if not set(VARIABLES + PORTS) <= needed:
        raise ValueError('Advertised input is dead')
    core, _ = d.live(residuals)
    return {
        'name': 'p15_degree24_' + ('transport89' if shifted else 'source58_baseline90'),
        'domain': 'strictly positive integers',
        'witnesses': VARIABLES, 'fixed_numerals': PORTS,
        'coordinate_z': 'z_new = z_old - 1' if shifted else 'source58 z_old',
        'coefficient_binding_file': '../native/COEFFICIENT_BINDING.json',
        'port_aliases': {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'},
        'source': rows, 'residuals': residuals, 'output': out,
        'exact_degree': 24,
        'operations': len(rows),
        'operation_breakdown': dict(Counter(row[1] for row in rows)),
        'operation_metric': 'One per live binary +, -, or * including fixed-scalar multiplication; integer leaves and earlier-gate references are free.',
        'residual_evaluator_operations': len(core),
        'degree_certificate_only': certificate,
        'proof': '../PROOF.md',
        'status': 'Ordinary source58 proof dependencies retained; no new end-to-end kernel or object-ZFC certificate.'
    }


def main():
    target = ROOT / 'circuits'
    target.mkdir(exist_ok=True)
    receipt = []
    for shifted in (False, True):
        for certificate in (False, True):
            packet = build(shifted, certificate)
            name = packet['name'] + ('_degree_certificate' if certificate else '') + '.json'
            (target / name).write_text(json.dumps(packet, indent=2) + '\n')
            receipt.append({'file': name, 'operations': packet['operations'],
                            'certificate_only': certificate})
    (ROOT / 'certificates' / 'BUILD.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
