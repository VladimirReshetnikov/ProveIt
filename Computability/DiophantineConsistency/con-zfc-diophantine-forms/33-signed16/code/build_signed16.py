#!/usr/bin/env python3
"""Build the explicit sixteen-integer polynomial; Python standard library only.

Every output node is an integer literal, an explicitly defined fixed coefficient,
one of sixteen variables, or a binary +,-,* gate. Powers are expanded. The
polynomial is defined without executing any supplied source program.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


class Circuit:
    def __init__(self):
        self.nodes = []
        self.cache = {}
        self.values = {}
        self.names = {}

    def intern(self, node):
        key = tuple(sorted(node.items()))
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(node)
        index = self.cache[key]
        if node['kind'] == 'literal':
            self.values[index] = node['value']
        return index

    def const(self, value):
        return self.intern(dict(kind='literal', value=value))

    def var(self, name):
        return self.intern(dict(kind='variable', name=name))

    def fixed(self, name):
        return self.intern(dict(kind='fixed', name=name))

    def binary(self, kind, left, right):
        a, b = self.values.get(left), self.values.get(right)
        if a is not None and b is not None:
            return self.const({'add': lambda: a+b, 'sub': lambda: a-b,
                               'mul': lambda: a*b}[kind]())
        if kind == 'add' and a == 0:
            return right
        if kind in ('add', 'sub') and b == 0:
            return left
        if kind == 'mul':
            if a == 0 or b == 0:
                return self.const(0)
            if a == 1:
                return right
            if b == 1:
                return left
        if kind in ('add', 'mul') and left > right:
            left, right = right, left
        return self.intern(dict(kind=kind, left=left, right=right))

    def add(self, *args):
        ans = self.const(0)
        for arg in args:
            ans = self.binary('add', ans, arg)
        return ans

    def mul(self, *args):
        ans = self.const(1)
        for arg in args:
            ans = self.binary('mul', ans, arg)
        return ans

    def sub(self, a, b):
        return self.binary('sub', a, b)

    @lru_cache(None)
    def power(self, a, n):
        if n == 0:
            return self.const(1)
        if n == 1:
            return a
        half = self.power(a, n//2)
        square = self.mul(half, half)
        return self.mul(square, a) if n % 2 else square

    def save(self, name, value):
        self.names[name] = value
        return value

    def pack(self, root):
        alive, pending = set(), [root]
        while pending:
            i = pending.pop()
            if i in alive:
                continue
            alive.add(i)
            n = self.nodes[i]
            if n['kind'] in ('add', 'sub', 'mul'):
                pending.extend((n['left'], n['right']))
        renumber = {old: new for new, old in enumerate(sorted(alive))}
        nodes = []
        for i in sorted(alive):
            n = self.nodes[i].copy()
            if n['kind'] in ('add', 'sub', 'mul'):
                n['left'] = renumber[n['left']]
                n['right'] = renumber[n['right']]
            nodes.append(n)
        counts = Counter(n['kind'] for n in nodes)
        return dict(nodes=nodes, output=renumber[root],
                    named_nodes={k: renumber[v] for k, v in self.names.items() if v in alive},
                    variables=[n['name'] for n in nodes if n['kind'] == 'variable'],
                    operation_counts={k: counts[k] for k in ('add', 'sub', 'mul')})


def coefficient_keys(d, constants):
    """Identical integer recipes share leaves; literal recipes are folded."""
    unique, keys, aliases = {}, [], {}
    for row in constants['coefficient_records']:
        recipe = row['coefficient_polynomial_in_fixed_ports']
        if len(recipe) == 1 and not any(recipe[0]['powers']):
            val = recipe[0]['coefficient']
            node = d.const(val)
            aliases[row['name']] = {'literal': val}
        else:
            signature = json.dumps(recipe, sort_keys=True, separators=(',', ':'))
            name = unique.setdefault(signature, row['name'])
            node = d.fixed(name)
            aliases[row['name']] = {'fixed': name}
        keys.append((tuple(row['alpha']), node))
    return keys, aliases


def coding_blocks(d, B, nu, keys, z):
    """Complete-homogeneous digit baseline and multivariate Horner correction.

    Identity and algorithm are from wave-4 package 27. Every coefficient,
    index and parent quartic in this specialization instead comes together
    from the new affine quartic and package 30's complete compiler tuple.
    """
    a, m, p, c = d.add, d.mul, d.power, d.const
    powers = [B]
    for _ in range(nu+1):
        powers.append(p(powers[-1], 5))
    gaps = [None]*(nu+1)
    gaps[nu] = c(1)
    for j in range(nu-1, -1, -1):
        gaps[j] = m(p(powers[j], 4), gaps[j+1])
    weights = [powers[nu]] + gaps
    homogeneous = [c(1)] + [c(0)]*4
    for weight in weights:
        for degree in range(1, 5):
            homogeneous[degree] = a(homogeneous[degree], m(weight, homogeneous[degree-1]))
    terms = tuple(((4-sum(alpha),)+alpha, coefficient) for alpha, coefficient in keys)
    # Fixed tie priorities found by finite circuit optimization. This changes
    # only the order of Horner identities, never the polynomial or its leaves.
    priority = (9,14,25,27,22,3,31,8,5,13,15,29,21,4,1,2,30,11,19,32,23,28,12,24,6,18,20,10,16,26,0,7,17)
    assert len(priority) == len(weights)

    @lru_cache(None)
    def horner(terms):
        if not terms:
            return c(0)
        positive = [sum(ex[j] > 0 for ex, _ in terms) for j in range(len(weights))]
        if max(positive) == 0:
            return a(*(coef for _, coef in terms))
        j = max(range(len(weights)), key=lambda j: (positive[j], priority[j]))
        yes, no = [], []
        for ex, coef in terms:
            if ex[j]:
                new = list(ex)
                new[j] -= 1
                yes.append((tuple(new), coef))
            else:
                no.append((ex, coef))
        return a(horner(tuple(no)), m(weights[j], horner(tuple(yes))))

    e = m(powers[nu], a(m(z, homogeneous[4]), horner(terms)))
    factors = [a(c(1), m(t, a(c(1), t), a(c(1), p(t, 2)))) for t in powers[:nu+1]]
    q = powers[nu+1]
    lam = m(*factors, a(c(1), q), a(c(1), p(q, 2)))
    ell = a(*powers[1:nu+1])
    return q, ell, lam, e, powers[nu]


def construct(constants):
    d = Circuit()
    c, a, m, sub, p, save = d.const, d.add, d.mul, d.sub, d.power, d.save
    nu, L = constants['nu'], constants['L']
    assert nu == 31 and L == 5**32
    variables = {name: d.var(name) for name in ('epsilon', 'g', 'h', 's', 'w', 'phi', 'i', 'j')}
    eps, g, h, s, w, phi, ii, jj = variables.values()
    z, yi = d.fixed('z_index'), d.fixed('y_index')
    keys, aliases = coefficient_keys(d, constants)
    b = save('b', a(yi, c(1), eps))
    B = save('B', p(b, 5))
    q, ell, lam, e, top = coding_blocks(d, B, nu, keys, z)
    for name, val in [('q', q), ('ell', ell), ('lambda', lam), ('e', e)]:
        save(name, val)
    theta = sub(B, m(c(2), z))
    N = save('N', p(q, 16))
    cap = save('Gcap', m(c(32), b, top))
    left = a(g, m(e, p(q, 3)), m(ell, p(q, 5)),
             m(a(m(c(2), sub(e, m(z, lam)), p(a(c(1), B, g), 4)),
                 m(lam, B), m(lam, B, p(q, 4))), p(q, 7)))
    right = a(sub(p(q, 3), m(b, ell)), ell, m(theta, lam, p(q, 3)), m(sub(B, c(2)), p(q, 8)))
    R = save('R', a(m(left, sub(p(N, 2), N)), m(right, sub(p(N, 2), c(1)))))
    U = save('U', m(p(N, 2), w))
    Y = save('Y', m(p(N, 2), s))
    M = save('M', m(R, Y))
    P = save('P', m(c(2), p(M, 2), U))
    K = save('K', a(R, c(1), m(h, sub(P, c(1)))))
    A = save('A', m(M, a(U, c(1))))
    B1 = save('B1', a(m(c(2), R), c(1)))
    W1 = save('W1', m(b, w))
    C = save('C', a(B1, W1, phi))
    J = save('J', sub(m(c(4), A), c(5)))
    Q = save('Q', sub(m(c(3), W1, C), m(c(2), sub(p(W1, 2), c(1)))))
    D = save('D', a(m(sub(p(A, 2), c(1)), p(C, 2)), c(1)))
    E = save('E', m(ii, J, D, p(C, 2)))
    F = save('F', a(m(sub(p(A, 2), c(1)), p(E, 2)), c(1)))
    G1 = save('G1', a(A, m(F, sub(a(m(C, D), c(1)), A))))
    H = save('H', a(B1, m(jj, C)))
    I = save('I', a(m(sub(p(G1, 2), c(1)), p(H, 2)), c(1)))
    a0 = save('a0', a(m(sub(p(P, 2), c(1)), p(K, 2)), c(1)))
    a1 = save('a1', m(D, F, I))
    margin = save('margin', sub(sub(m(p(K, 2), cap), m(c(4), p(sub(C, m(K, Y)), 2), cap)),
                              m(c(8), g, p(K, 2))))
    divisor = save('Ddiv', m(J, F))
    dividend = save('Tdiv', a(m(Q, F), m(J, sub(H, C))))
    zs = [d.var('z'+str(k)) for k in range(1, 7)]
    discriminants = [a(m(c(3), eps), c(2)), sub(m(c(3), g), c(1)),
                     sub(m(c(3), s), c(1)), sub(m(c(3), w), c(1)),
                     a(m(c(3), phi), c(2)), sub(m(c(3), margin), c(1))]
    stack = c(1)
    for k, (disc, witness) in enumerate(zip(discriminants, zs), 1):
        factor = a(c(1), m(c(4), disc, p(m(stack, witness), 2)))
        stack = save('Cguard'+str(k), m(stack, factor))
    nonzero = save('Znonzero', m(ii, *zs))
    S = save('Smerge', m(nonzero, p(divisor, 5)))
    residue, root = d.var('residue'), d.var('normroot')
    r = a(dividend, m(divisor, residue))
    dd = p(divisor, 2)
    T = save('Tmerge', m(sub(sub(p(r, 3), m(dd, r)), m(dd, divisor)), a(p(r, 2), m(c(23), dd))))
    weight1 = save('weight1', a(stack, c(1)))
    weight2 = save('weight2', m(weight1, a(p(P, 2), p(K, 2), c(2))))
    X = save('Xnorm', sub(m(S, root), T))
    S2 = p(S, 2)
    A0 = save('A0norm', m(S2, stack))
    A1 = save('A1norm', m(p(m(S, weight1), 2), a0))
    A2 = save('A2norm', m(p(m(S, weight2), 2), a1))
    X2 = p(X, 2)
    V = save('Vnorm', sub(sub(a(X2, A2), A0), A1))
    V2 = p(V, 2)
    fourXA2 = m(c(4), X2, A2)
    W = save('Wnorm', sub(a(V2, fourXA2), m(c(4), A0, A1)))
    out = save('signed16', sub(p(W, 2), m(c(4), V2, fourXA2)))
    packet = d.pack(out)
    assert len(packet['variables']) == len(set(packet['variables'])) == 16
    packet.update(schema='proveit-signed16-v1', domain='unrestricted integers', nu=nu, L=L,
                  model='Live binary +,-,* gates; scalar products and squares charged; reuse and fixed constants free.',
                  exact_degree=406528*L+10008, exact_degree_formula='406528*5^32+10008',
                  fixed_coefficient_recipes='data/coefficients31.json',
                  compiler_tuple='upstream/compiler/binding.json', coefficient_aliases=aliases)
    return packet


def degree_certificate(body):
    prime, values = 1000003, []
    for node in body['nodes']:
        k = node['kind']
        if k == 'literal':
            row = (0, node['value'] % prime, False)
        elif k == 'fixed':
            row = (0, 0, True)
        elif k == 'variable':
            row = (1, 1, False)
        else:
            a, b = values[node['left']], values[node['right']]
            if k == 'mul':
                row = (a[0]+b[0], a[1]*b[1] % prime, a[2] or b[2])
            else:
                deg = max(a[0], b[0])
                sign = 1 if k == 'add' else -1
                row = (deg, ((a[1] if a[0] == deg else 0)+sign*(b[1] if b[0] == deg else 0)) % prime,
                       (a[2] if a[0] == deg else False) or (b[2] if b[0] == deg else False))
        values.append(row)
    deg, lead, uncertain = values[body['output']]
    assert deg == body['exact_degree'], (deg, body['exact_degree'])
    assert lead and not uncertain, (lead, uncertain)
    return dict(degree=deg, diagonal_leading_residue=lead, modulus=prime,
                leading_term_independent_of_fixed_coefficients=True,
                selected={name: values[i] for name, i in body['named_nodes'].items()
                          if name in ('R', 'P', 'K', 'a0', 'a1', 'margin', 'Cguard5', 'Cguard6',
                                      'Smerge', 'Tmerge', 'weight1', 'weight2', 'A2norm', 'signed16')})


def main():
    constants = json.loads((ROOT/'data/coefficients31.json').read_text())
    body = construct(constants)
    certificate = degree_certificate(body)
    path = ROOT/'data/signed16.json'
    path.write_text(json.dumps(body, separators=(',', ':'))+'\n')
    result = dict(variables=body['variables'], operation_counts=body['operation_counts'],
                  operations=sum(body['operation_counts'].values()), degree_certificate=certificate,
                  circuit_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    (ROOT/'verification/signed16_build.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
