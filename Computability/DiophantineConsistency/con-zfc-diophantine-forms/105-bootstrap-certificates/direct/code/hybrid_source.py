"""Factored numerical C222 arithmetic with eleven bounded local coordinates.

The formulas are those of Code254.lean and KCode222.lean. audit_calculus.py
checks the inherited constructors. The factored branch product has the same zero set. All code
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

    a, b, c, d, v = [env[name] for name in ('a', 'b', 'c', 'd', 'v')]
    codes = [X(a, E(a, b)),
             I(A(a, I(b, c)), I(A(a, b), A(a, c))),
             I(E(a, b), I(M(c, a), M(c, b))),
             I(A(a, A(b, c)), A(b, A(a, c))),
             I(E(c, a), I(M(c, b), M(a, b))),
             I(X(a, A(a, b)), b),
             I(E(c, a), I(E(c, b), A(M(a, b), E(a, b)))),
             I(I(I(c, d), a), I(I(a, c), I(b, c))),
             bundle(a, b, c)]
    carrier = add(env['M0'], one)
    S, Sp = env['S'],env['Sp']
    def weight(z): return add(one,mul(z,carrier))
    axupdate=(mul(Sp,weight(v)),S)
    axis=(v,zero)
    for code in codes[:-1]:
        axis=self.pair_mul(axis,(v,code))
    guard_positive=add(square(c),mul(a,b))
    guard_negative=mul(c,add(a,b))
    gp,gn=self.pair_square((guard_positive,guard_negative))
    guard=(gp,add(gn,square(add(d,one))))
    guarded=self.pair_add(self.pair_square((v,codes[-1])),self.pair_square(guard))
    axiom=self.pair_add(self.pair_mul(self.pair_square(axis),guarded),self.pair_square(axupdate))
    mpupdate=(mul(Sp,weight(v)),self.product([S,weight(a),weight(I(a,v))]))
    genupdate=(mul(Sp,weight(v)),mul(S,weight(b)))
    gen=self.pair_add(self.pair_square((v,A(a,b))),self.pair_square(genupdate))
    total=self.pair_mul(self.pair_mul(axiom,self.pair_square(mpupdate)),gen)
    denominator=add(mul(add(index,one),env['y']),one)
    next_denominator=add(denominator,env['y'])
    rows=[(env['x'],add(S,mul(denominator,env['u']))),
          (env['x'],add(Sp,mul(next_denominator,env['vq'])))]
    for row in rows: total=self.pair_add(total,self.pair_square(row))
    return total
