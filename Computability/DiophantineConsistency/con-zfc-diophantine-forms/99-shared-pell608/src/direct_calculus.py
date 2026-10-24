"""Literal numerical C222 arithmetic, independently matched to the pinned source.

The formulas are those of Code254.lean and KCode222.lean. audit_calculus.py
checks their exact compositional equality with the branch source. All code
constructors use nonnegative arithmetic and numeral leaves at most four.
This module can be used as Builder.source_pair through method assignment.
"""


def source_pair_calculus(self, source, env, index, include_label_slacks):
    zero, one, two, three, four = [("c", n) for n in range(5)]
    expected_names = ['truth', 'rho1', 'rho2', 'rho3', 'rho4', 'rho5', 'rho6',
                      'growG', 'rho8', 'bundle', 'mp', 'gen']
    if [branch['name'] for branch in source['horn_branches']] != expected_names:
        raise ValueError('source branch names differ from pinned C222 interface')
    add, mul, square = self.add, self.mul, self.square

    def I(x, y):
        s = add(x, y)
        return add(mul(two, mul(s, add(s, one))), mul(four, y))

    def A(x, y):
        return add(I(x, y), two)

    def M(x, y):
        return add(I(x, y), one)

    def E(x, y):
        return add(I(x, y), three)

    def N(x):
        return I(x, one)

    def X(x, y):
        return N(A(x, N(y)))

    def req(x, k, matrix):
        return A(x, I(matrix, N(A(x, I(matrix, N(M(x, k)))))))

    def clos(x, y, k, matrix):
        subset = A(k, I(M(k, x), M(k, y)))
        tail = I(subset, req(y, k, matrix))
        tail = N(A(x, tail))
        tail = N(A(x, I(matrix, tail)))
        return A(y, I(M(y, k), tail))

    def bundle(x, y, z):
        nks = A(z, I(clos(x, y, z, z), N(req(y, z, z))))
        vrel = I(M(x, y), A(z, M(x, y)))
        return N(I(vrel, nks))

    a, b, c, d, p, q, v = [env[name] for name in ('a', 'b', 'c', 'd', 'p', 'q', 'v')]
    codes = [X(a, E(a, b)),
             I(A(a, I(b, c)), I(A(a, b), A(a, c))),
             I(E(a, b), I(M(c, a), M(c, b))),
             I(A(a, A(b, c)), A(b, A(a, c))),
             I(E(c, a), I(M(c, b), M(a, b))),
             I(X(a, A(a, b)), b),
             I(E(c, a), I(E(c, b), A(M(a, b), E(a, b)))),
             I(I(I(c, d), a), I(I(a, c), I(b, c))),
             bundle(a, b, c)]
    pq = self.sum([square(p), square(q)])
    branch_pairs = [(add(pq, square(v)), zero)]
    for code in codes:
        branch_pairs.append(self.pair_add((pq, zero), self.pair_square((v, code))))

    # ((c-a)(c-b))^2 - (d+1)^2, split without expanding its quartic.
    guard_positive = add(square(c), mul(a, b))
    guard_negative = mul(c, add(a, b))
    gp, gn = self.pair_square((guard_positive, guard_negative))
    guard = (gp, add(gn, square(add(d, one))))
    branch_pairs[-1] = self.pair_add(branch_pairs[-1], self.pair_square(guard))
    branch_pairs.append(self.pair_square((q, I(p, v))))
    branch_pairs.append(self.pair_add((square(q), zero), self.pair_square((v, A(a, p)))))

    total = (one, zero)
    for branch_pair in branch_pairs:
        total = self.pair_mul(total, branch_pair)

    carrier = add(env['M0'], one)
    def weight(name):
        return add(one, mul(env[name], carrier))
    rows = [(mul(env['Sp'], weight('v')),
             self.product([env['S'], weight('p'), weight('q')]))]
    if include_label_slacks:
        rows += [(add(env[name], env['d' + name]), env['m']) for name in ('p', 'q', 'v')]
    denominator = add(mul(add(index, one), env['y']), one)
    next_denominator = add(denominator, env['y'])
    rows += [(env['x'], add(env['S'], mul(denominator, env['u']))),
             (env['x'], add(env['Sp'], mul(next_denominator, env['vq'])))]
    for row in rows:
        total = self.pair_add(total, self.pair_square(row))
    return total
