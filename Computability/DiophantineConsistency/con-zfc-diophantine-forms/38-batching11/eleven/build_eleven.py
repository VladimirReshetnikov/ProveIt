#!/usr/bin/env python3
"""An explicit eleven-positive-variable norm with the index quotient absorbed.

All fixed coefficient ports must come from ONE authentic blank-K215 tuple.
Every binary +, -, * costs one operation. Comparisons in a system are free.
This generator and its finite checks do not certify the inherited compiler.
"""
import json
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
WITNESSES = ['J', 'F', 'alpha', 'z', 'i', 'T', 's', 'w', 'eta', 'zeta', 't']
PORTS = ['beta', 'K0', 'MC', 'MF']

class Circuit:
    def __init__(self):
        self.rows = []
        self.cache = {}
    def op(self, operation, left, right, name=None):
        pair = tuple(sorted((left, right), key=str)) if operation in ('+', '*') else (left, right)
        key = (operation,) + pair
        if key in self.cache:
            return self.cache[key]
        name = name or 'g' + str(len(self.rows) + 1)
        self.rows.append([name, operation, left, right])
        self.cache[key] = name
        return name
    def m(self, a, b, n=None): return self.op('*', a, b, n)
    def a(self, a, b, n=None): return self.op('+', a, b, n)
    def s(self, a, b, n=None): return self.op('-', a, b, n)
    def sq(self, a, n=None): return self.m(a, a, n)

def build(kind='product'):
    circuit = Circuit()
    mul, add, sub, sq = circuit.m, circuit.a, circuit.s, circuit.sq
    qm1 = mul('beta', 'J', 'qm1')
    q = add(qm1, 1, 'q')
    q2 = sq(q, 'q2')
    q3 = mul(q2, q, 'q3')
    s0 = add('s', mul(3, q), 's0')
    X = mul('w', q, 'X')
    Y = mul(s0, q3, 'Y')
    E = mul(X, Y, 'E')
    k = add('eta', 'zeta', 'k')
    kY = mul(k, Y, 'kY')
    ell = mul(E, kY, 'ell')
    A = add(mul(ell, add(ell, k)), 1, 'A')
    c = add(kY, 'eta', 'c')
    a = add(E, Y, 'a')
    H = add(mul(4, a), 3, 'H')
    Delta = add(sq(a), H, 'Delta')
    c2 = sq(c, 'c2')
    G = add(mul(Delta, c2), 1, 'G')
    b0 = add(X, mul(a, c), 'b0')
    qF = sub(q, 'F', 'qF')
    Cw = sub(qF, 'alpha', 'Cw')
    R = add(mul(add(mul(qm1, qF), 'alpha'), sub(q2, 1)),
            mul(add('MC', mul(q, 'MF')), 'J'), 'R')
    transport_left = mul(add('K0', 'w'), Cw, 'transport_left')
    transport_z = mul('z', qm1, 'transport_z')
    if kind == 'shifted_system':
        transport_right = add('F', transport_z, 'transport_right')
        transport_comparison = [transport_left, transport_right]
    else:
        Nt = sub(add(transport_left, qF), transport_z, 'Nt')
        transport_comparison = [Nt, 1]
    I = mul('i', c2, 'I')
    I2 = sq(I, 'I2')
    Dm1 = mul(Delta, I2, 'Dm1')
    D = add(Dm1, 1, 'D')
    Q = mul(Delta, Dm1, 'Q')
    d = sub(Q, 1, 'd')
    v = mul(c, 'T', 'v')
    v2 = sq(v, 'v2')
    b = add(c, mul(R, D), 'b')
    Cstar = add(add(E, mul(2, add(X, Y))), mul(s0, q2), 'Cstar')
    M = mul(I, add(mul(2, 'T'), mul(mul(R, Cstar), mul('i', c))), 'M')
    HM = mul(H, M, 'HM')
    L0 = add(HM, 1, 'L0')
    S = mul(H, E, 'S')
    L = mul(E, L0, 'L')
    carrier_index = sub(sub(add(mul(E, 't'), k), R), 1, 'carrier_index')
    W = add(mul(L, b0), mul(H, carrier_index), 'W')
    SM = mul(S, M, 'SM')
    n = mul(sq(SM), A, 'n')
    dn = mul(d, n, 'dn')
    S2 = sq(S, 'S2')
    S2Q = mul(S2, Q, 'S2Q')
    HP = mul(S2Q, mul(D, v2), 'HP')
    HU = mul(S2Q, sq(b), 'HU')
    He = sub(add(HP, HU), S2, 'He')
    j = mul(4, mul(HP, HU), 'j')
    W2 = sq(W, 'W2')
    L2G = mul(sq(L), G, 'L2G')
    Trace = mul(2, mul(d, add(W2, L2G)), 'Trace')
    Knorm = sq(mul(d, sub(W2, L2G)), 'Knorm')
    AA = mul(2, add(dn, He), 'AA')
    constant = sub(sq(sub(dn, He)), j, 'constant')
    at = sub(Trace, AA, 'at')
    bt = sub(constant, Knorm, 'bt')
    coef = mul(16, mul(dn, j), 'coef')
    # A sign choice allows a direct comparison for the final quadratic norm.
    vr = sub(coef, mul(at, add(mul(at, Trace), mul(2, bt))), 'vr')
    ur = sub(sq(bt), mul(sq(at), Knorm), 'ur')
    term_left = mul(ur, sub(mul(Trace, vr), ur), 'term_left')
    term_right = mul(Knorm, sq(vr), 'term_right')
    packet = {'name': 'absorbed_index_eleven_' + kind,
              'domain': 'strictly positive integers',
              'witnesses': WITNESSES,
              'fixed_numerals': PORTS,
              'source': circuit.rows,
              'coefficient_interface': 'one whole authentic normalized blank-K215 tuple; MF is shifted',
              'coefficient_binding': '../compiler/COEFFICIENT_BINDING.json',
              'fixed_port_payloads': {'beta': '../compiler/coefficients/beta.bin.gz',
                                      'K0': '../compiler/coefficients/K.bin.gz',
                                      'MC': '../compiler/coefficients/MC.bin.gz',
                                      'MF': '../compiler/coefficients/MF_source.bin.gz'},
              'proof': 'ELEVEN_POSITIVE_PROOF.md',
              'construction_source_pin': '22e75dd6b87b1b199bb08c778d7cf075ae5aae08'}
    if kind == 'product':
        norm = sub(term_right, term_left, 'N')
        packet['output'] = sub(mul(Nt, add(norm, 1)), 1, 'polynomial')
        packet['exact_degree'] = 1154
    else:
        packet['comparisons'] = [transport_comparison, [term_left, term_right]]
        packet['residual_exact_degrees'] = [2, 1152]
        if kind == 'shifted_system':
            packet['coordinate_relation'] = 'z_old = z_new + 1'
    counts = Counter(row[1] for row in circuit.rows)
    packet['ledger'] = {'operations': len(circuit.rows), 'multiplications': counts['*'],
                        'additions_subtractions': counts['+'] + counts['-']}
    return packet

def evaluate(packet, values, modulus=None):
    values = dict(values)
    for name, operation, left, right in packet['source']:
        left = left if isinstance(left, int) else values[left]
        right = right if isinstance(right, int) else values[right]
        value = left + right if operation == '+' else left - right if operation == '-' else left * right
        values[name] = value if modulus is None else value % modulus
    return values

def audit_live(packet):
    known = set(WITNESSES + PORTS)
    source_names = []
    for name, operation, left, right in packet['source']:
        if name in known: raise ValueError('duplicate gate: ' + name)
        if operation not in ('+', '-', '*'): raise ValueError(operation)
        for operand in (left, right):
            if not isinstance(operand, int) and operand not in known:
                raise ValueError('undefined operand: ' + operand)
        known.add(name)
        source_names.append(name)
    outputs = [packet['output']] if 'output' in packet else sum(packet['comparisons'], [])
    needed = {value for value in outputs if isinstance(value, str)}
    for name, operation, left, right in reversed(packet['source']):
        if name in needed:
            for operand in (left, right):
                if isinstance(operand, str): needed.add(operand)
    dead = set(source_names + WITNESSES + PORTS) - needed
    if dead: raise ValueError('dead gates or inputs: ' + repr(sorted(dead)))

def main():
    out = HERE / 'generated'
    out.mkdir(exist_ok=True)
    for kind in ('product', 'system', 'shifted_system'):
        packet = build(kind)
        audit_live(packet)
        (out / (packet['name'] + '.json')).write_text(json.dumps(packet, indent=2) + '\n')
        print(packet['name'], packet['ledger'])

if __name__ == '__main__': main()
