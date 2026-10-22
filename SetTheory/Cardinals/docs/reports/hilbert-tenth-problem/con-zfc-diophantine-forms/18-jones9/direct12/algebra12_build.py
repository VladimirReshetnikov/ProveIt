"""Generate a literal 12-positive-variable polynomial via three quadratic norms.

This is an ordinary polynomial circuit.  Root symbols below are represented
only by integer coefficient pairs; no roots, divisions, or quantifiers occur
in the generated circuit.  Fixed ports must be bound to one valid complete
native compiler tuple, e.g. wave-1 package06's tuple.
"""
import json
from pathlib import Path


class Circuit:
    def __init__(self):
        self.gates = []
        self.memo = {}
        self.labels = {}

    def gate(self, op, a, b):
        if op == '+' and a == 0:
            return b
        if op == '+' and b == 0:
            return a
        if op == '-' and b == 0:
            return a
        if op == '-' and a == b:
            return 0
        if op == '*' and (a == 0 or b == 0):
            return 0
        if op == '*' and a == 1:
            return b
        if op == '*' and b == 1:
            return a
        if isinstance(a, int) and isinstance(b, int):
            return {'+': lambda: a + b, '-': lambda: a - b,
                    '*': lambda: a * b}[op]()
        if op in ('+', '*') and str(a) > str(b):
            a, b = b, a
        key = op, a, b
        if key not in self.memo:
            out = 'g' + str(len(self.gates) + 1)
            self.memo[key] = out
            self.gates.append([out, op, a, b])
        return self.memo[key]

    def add(self, a, b): return self.gate('+', a, b)
    def sub(self, a, b): return self.gate('-', a, b)
    def mul(self, a, b): return self.gate('*', a, b)
    def sq(self, a): return self.mul(a, a)

    def label(self, name, x):
        self.labels[name] = x
        return x


def build():
    c = Circuit()
    add, sub, mul, sq = c.add, c.sub, c.mul, c.sq
    q = c.label('q', add(mul('beta', 'J'), 1))
    qm = sub(q, 1)
    qF = sub(q, 'F')
    Cw = sub(qF, 'alpha')
    X = mul('w', q)
    q2 = sq(q)
    Y = mul('s', mul(q2, q))
    E = mul(X, Y)
    k = add('eta', 'zeta')
    kY = mul(k, Y)
    cc = c.label('c', add(kY, 'eta'))
    a = c.label('a', add(E, Y))
    H = c.label('H', add(mul(4, a), 3))
    Delta = c.label('Delta', add(sq(a), H))
    R = c.label('R', add(mul(add(mul(qm, qF), 'alpha'), sub(q2, 1)),
                         mul(add('MC', mul(q, 'MF')), 'J')))
    Nk = c.label('Nk', sub(sub(k, mul('h', E)), R))
    Nt = c.label('Nt', sub(add(mul(add('Kconstant', 'w'), Cw), qF),
                          mul('z', qm)))
    Lfirst = c.label('Lfirst', mul(E, kY))
    A = c.label('A', add(1, mul(Lfirst, add(Lfirst, k))))
    cc2 = sq(cc)
    I = c.label('I', mul(mul(H, 'i'), cc2))
    I2 = sq(I)
    D = c.label('D', add(1, mul(Delta, I2)))
    Q = c.label('Q', mul(Delta, sub(D, 1)))
    d = c.label('d', sub(Q, 1))
    v = mul(cc, 'T')
    v2 = sq(v)
    z0 = c.label('z0', add(cc, mul(R, D)))
    P0 = mul(Q, mul(D, v2))
    Z0 = mul(Q, sq(z0))
    e = c.label('e', sub(add(P0, Z0), 1))
    B = c.label('B', mul(2, mul(Q, mul(v, z0))))
    M = c.label('M', mul(2, add(D, v2)))
    tauBound = c.label('tauBound', add(add(Lfirst, k), 1))
    fBound = c.label('fBound', add(mul(add(a, 2), I), 1))
    yBound = c.label('yBound', mul(2, add(mul(v, fBound), z0)))
    Ubound = c.label('Ubound', add(mul(M, tauBound), yBound))
    ell = c.label('ell', add(1, mul(H, Ubound)))
    G = c.label('G', add(1, mul(Delta, cc2)))
    S = c.label('S', add(mul(H, 't'), mul(ell, add(mul(a, cc), X))))
    W = c.label('W', mul(H, M))
    H2 = sq(H)

    # Pair (u,v) denotes u+v*r with r^2=G.  All operations are polynomial.
    def padd(p, q): return add(p[0], q[0]), add(p[1], q[1])
    def psub(p, q): return sub(p[0], q[0]), sub(p[1], q[1])
    def pscale(p, x): return mul(p[0], x), mul(p[1], x)
    def pmul(p, q):
        return (add(mul(p[0], q[0]), mul(G, mul(p[1], q[1]))),
                add(mul(p[0], q[1]), mul(p[1], q[0])))
    def psq(p):
        return add(sq(p[0]), mul(G, sq(p[1]))), mul(2, mul(p[0], p[1]))

    # Norm in f first, then tau. Start E=d(S-ell*r-W*tau)^2-H^2(e-B*f).
    Z = S, sub(0, ell)
    ZZ = psq(Z)
    UU = psub(pscale(padd(ZZ, (mul(sq(W), A), 0)), d),
               (mul(H2, e), 0))
    VV = pscale(Z, mul(2, mul(d, W)))
    UU2 = psq(UU)
    VV2A = pscale(psq(VV), A)
    # H^4 B^2 D = 4 H^4 P0 Z0 saves evaluator gates.
    F0 = psub(padd(UU2, VV2A), (mul(4, mul(sq(H2), mul(P0, Z0))), 0))
    F1 = pscale(pmul(UU, VV), 2)
    RR = psub(psq(F0), pscale(psq(F1), A))
    R12 = c.label('R12', sub(sq(RR[0]), mul(G, sq(RR[1]))))
    P12 = c.label('P12', sub(mul(mul(Nk, Nt), add(1, R12)), 1))

    # Prune intermediate labels which are not used in the literal circuit.
    byname = {g[0]: g for g in c.gates}
    live = set()
    def mark(x):
        if x in byname and x not in live:
            live.add(x)
            mark(byname[x][2]); mark(byname[x][3])
    mark(P12)
    source = [g for g in c.gates if g[0] in live]
    return {
        'name': 'radical12_product',
        'domain': 'strictly positive integers',
        'unknowns': ['J', 'F', 'alpha', 'z', 'h', 'i', 'T', 's', 'w',
                     'eta', 'zeta', 't'],
        'fixed_ports': ['beta', 'Kconstant', 'MC', 'MF'],
        'coefficient_binding': '../coefficients/T4_CONSTANTS.upstream.json',
        'coefficient_port_mapping': {'beta':'beta', 'Kconstant':'K0', 'MC':'MC', 'MF':'MF'},
        'source': source, 'output': P12,
        'system_outputs': [Nk, Nt, R12], 'system_targets': [1, 1, 0],
        'labels': {name: x for name, x in c.labels.items()
                   if isinstance(x, int) or x in live},
        'operations': len(source),
        'multiplications': sum(g[1] == '*' for g in source),
        'additions_subtractions': sum(g[1] != '*' for g in source),
        'exact_degree': 1609,
        'exact_system_degree': 1600,
        'degree_certificate': 'See PROOF.md: eight real-branch Laurent factors',
    }


def build_system(product=None):
    """Emit the three-equation system, pruning the four finalizer gates."""
    if product is None:
        product = build()
    byname = {gate[0]: gate for gate in product['source']}
    live = set()
    def mark(value):
        if value in byname and value not in live:
            live.add(value)
            mark(byname[value][2])
            mark(byname[value][3])
    for output in product['system_outputs']:
        mark(output)
    source = [gate for gate in product['source'] if gate[0] in live]
    if len(source) != 147:
        raise RuntimeError('Expected exactly 147 live system gates')
    return {
        'name': 'radical12_system147',
        'kind': 'polynomial_system',
        'domain': product['domain'],
        'unknowns': product['unknowns'],
        'fixed_ports': product['fixed_ports'],
        'coefficient_binding': product['coefficient_binding'],
        'coefficient_port_mapping': product['coefficient_port_mapping'],
        'source': source,
        'outputs': product['system_outputs'],
        'targets': product['system_targets'],
        'labels': {name: value for name, value in product['labels'].items()
                   if isinstance(value, int) or value in live},
        'operations': len(source),
        'multiplications': sum(gate[1] == '*' for gate in source),
        'additions_subtractions': sum(gate[1] != '*' for gate in source),
        'exact_degree': product['exact_system_degree'],
        'degree_certificate': product['degree_certificate'],
        'equation_convention': 'Each outputs[j] equals targets[j].',
    }


def evaluate(artifact, supplied):
    env = dict(supplied)
    def val(x): return x if isinstance(x, int) else env[x]
    for out, op, a, b in artifact['source']:
        aa, bb = val(a), val(b)
        env[out] = {'+': lambda: aa+bb, '-': lambda: aa-bb,
                    '*': lambda: aa*bb}[op]()
    return env


if __name__ == '__main__':
    artifact = build()
    destination = Path(__file__).resolve().with_name('radical12_product.json')
    destination.write_text(json.dumps(artifact, indent=2) + '\n')
    system = build_system(artifact)
    system_destination = Path(__file__).resolve().with_name('radical12_system147.json')
    system_destination.write_text(json.dumps(system, indent=2) + '\n')
    print(json.dumps({k: artifact[k] for k in ('name', 'operations',
          'multiplications', 'additions_subtractions', 'exact_degree',
          'exact_system_degree')}, indent=2))
    print(json.dumps({k: system[k] for k in ('name', 'operations',
          'multiplications', 'additions_subtractions', 'exact_degree')}, indent=2))
