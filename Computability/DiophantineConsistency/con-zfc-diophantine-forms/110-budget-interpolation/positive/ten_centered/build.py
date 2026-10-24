#!/usr/bin/env python3
"""Build a literal, division-free ten-positive-variable consistency polynomial.

Only Python's standard library is used. Every binary +, -, * is charged;
numeral leaves and aliases of existing registers are free.
"""
from pathlib import Path
from collections import Counter
import json

ROOT = Path(__file__).resolve().parent
VARIABLES = ['j', 'F', 'alpha', 'i', 'T', 'X', 's', 'n', 'eta', 'zeta']
PORTS = ['beta', 'K0', 'MC', 'MF']

class DAG:
    def __init__(self):
        self.rows, self.cache, self.named = [], {}, {}
    def gate(self, op, a, b, name=None):
        if op in ('+', '*') and str(a) > str(b):
            a, b = b, a
        key = op, a, b
        if key not in self.cache:
            v = 'g%03d' % len(self.rows)
            self.rows.append([v, op, a, b])
            self.cache[key] = v
        v = self.cache[key]
        if name is not None:
            self.named[name] = v
        return v
    def add(self, a, b, name=None): return self.gate('+', a, b, name)
    def sub(self, a, b, name=None): return self.gate('-', a, b, name)
    def mul(self, a, b, name=None): return self.gate('*', a, b, name)
    def sq(self, a, name=None): return self.mul(a, a, name)
    def live(self, out):
        needed = {out}
        for v, op, a, b in reversed(self.rows):
            if v in needed:
                needed.update((a, b))
        return [r for r in self.rows if r[0] in needed], needed

def build():
    d = DAG()
    add, sub, mul, sq = d.add, d.sub, d.mul, d.sq
    J = add(mul(3, 'j'), 1, 'J')
    qm = mul('beta', J, 'q_minus_1')
    q = add(qm, 1, 'q')
    q2 = sq(q, 'q2')
    q3 = mul(q2, q, 'q3')
    q4 = sq(q2, 'q4')
    U = mul(q4, q, 'U')
    h = add('F', 'alpha', 'h')
    C = sub(q, h, 'C')
    Y = mul(q3, 's', 'Y')
    E = mul('X', Y, 'E')
    k = add('eta', 'zeta', 'k')
    kY = mul(k, Y, 'kY')
    c = add(kY, 'eta', 'c')
    c2 = sq(c, 'c2')
    a = add(E, Y, 'a')
    H = add(mul(4, a), 3, 'H')
    Delta = add(sq(a), H, 'Delta')
    ell = mul(E, kY, 'ell')
    R = add(mul(add(mul(qm, sub(q, 'F')), 'alpha'), sub(q2, 1)),
            mul(add('MC', mul(q, 'MF')), J), 'R')
    Bt = sub(mul(add(mul(q, 'K0'), 'X'), C), mul(q, 'F'), 'Bt')
    I = mul('i', c2, 'I')
    I2 = sq(I, 'I2')
    Dfm = mul(Delta, I2, 'Df_minus_1')
    Df = add(Dfm, 1, 'Df')
    Q = mul(Delta, Dfm, 'Q')
    delta = sub(Q, 1, 'delta')
    Told = add('T', h, 'Told')
    Cf = mul(add(a, 2), I, 'Cf')
    cT = mul(c, Told, 'cT')
    V = sub(mul(Df, sub(cT, R)), c, 'V')
    Dt = add(mul(ell, add(ell, k)), 1, 'Dt')
    Dd = add(mul(Delta, c2), 1, 'Dd')
    L = mul(k, Told, 'L')
    W = add(mul(qm, L), 1, 'W')
    v = sub(sub(k, R), 1, 'v')
    b0 = add('X', mul(a, c), 'b0')
    M = mul(qm, U, 'M')
    # Z/M = H*(ell+k+n+L+s - W*Bt/(q-1)) + b0
    #       + H*(q4*X-v)/U. No division is performed by the circuit.
    center = add(add(add(add(add(add(ell, k), 'n'), L), 's'), V), Cf, 'center')
    Z = add(sub(mul(M, add(mul(H, center), b0)),
                mul(mul(mul(H, U), W), Bt)),
            mul(mul(H, qm), sub(mul(q4, 'X'), v)), 'Z')
    M2 = sq(M, 'M2')
    MH2 = mul(M2, sq(H), 'M2H2')
    A = mul(MH2, Dt, 'A')
    B = mul(MH2, Df, 'B')
    D = mul(M2, Dd, 'D')
    Cnum = mul(MH2, sub(mul(Q, sq(V)), 1), 'Cnum')
    # delta^8 * F16(Z; A,B,D,Cnum/delta).
    sigma = add(add(A, B), D, 'sigma')
    AB = mul(A, B, 'AB')
    pairs = add(AB, mul(add(A, B), D), 'pairs')
    prod = mul(AB, D, 'prod')
    Z2 = sq(Z, 'Z2')
    delta2 = sq(delta, 'delta2')
    delta3 = mul(delta2, delta, 'delta3')
    dz = mul(delta, Z2, 'delta_Z2')
    ahat = add(mul(delta, sub(Z2, sigma)), Cnum, 'ahat')
    ahat2 = sq(ahat, 'ahat2')
    tz = mul(mul(delta, Cnum), Z2, 'tz')
    khat = add(ahat2, mul(4, sub(tz, mul(delta2, pairs))), 'khat')
    rhat = mul(16, mul(delta3, prod), 'rhat')
    bhat = sub(mul(ahat, khat), rhat, 'bhat')
    ehat = sub(add(sq(khat), mul(16, mul(tz, ahat2))),
               mul(4, mul(rhat, add(dz, Cnum))), 'ehat')
    out = sub(sq(ehat), mul(64, mul(tz, sq(bhat))), 'P10')
    rows, needed = d.live(out)
    if not set(VARIABLES + PORTS) <= needed:
        raise ValueError('A declared input is unused')
    return {
        'name':'centered_four_root_residue_p10',
        'domain':'strictly positive integers',
        'variables':VARIABLES, 'fixed_numerals':PORTS,
        'source':rows, 'named_registers':d.named, 'output':out,
        'operations':len(rows),
        'operation_breakdown':dict(Counter(row[1] for row in rows)),
        'exact_total_degree':912,
        'coefficient_binding':'coefficients/BINDING.json',
        'count_convention':'Every live binary +,-,* gate, including squares and scalar products; numeral leaves and register reuse free.',
        'proof':'PROOF.md',
    }

def main():
    packet = build()
    (ROOT/'generated').mkdir(exist_ok=True)
    (ROOT/'generated'/'p10_positive.json').write_text(json.dumps(packet,indent=2)+'\n')
    natural = dict(packet)
    natural['name'] = 'four_root_residue_p10_natural'
    natural['domain'] = 'nonnegative integers'
    natural['variables'] = [v+'0' for v in VARIABLES]
    natural['source'] = [[v,'+',v+'0',1] for v in VARIABLES] + packet['source']
    natural['operations'] = packet['operations'] + len(VARIABLES)
    natural['operation_breakdown'] = dict(Counter(r[1] for r in natural['source']))
    natural['coordinate_map'] = {v:v+'0 + 1' for v in VARIABLES}
    (ROOT/'generated'/'p10_natural.json').write_text(json.dumps(natural,indent=2)+'\n')
    print(json.dumps({k:packet[k] for k in ['name','domain','operations','operation_breakdown','exact_total_degree']},indent=2))

if __name__ == '__main__': main()
