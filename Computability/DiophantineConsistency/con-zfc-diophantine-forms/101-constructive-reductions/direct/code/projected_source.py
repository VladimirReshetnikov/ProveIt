"""C222 row with deterministic labels projected before bounded compilation.

The only bounded columns are a,b,c,d,S,Sp,u,vq.  A branch-specific
accumulator identity replaces its three deterministic p,q,v coordinates.
All pairs denote their first coordinate minus their second coordinate.
"""

def constructors(b, env):
    zero, one, two, three, four = [("c", n) for n in range(5)]
    add, mul = b.add, b.mul
    def I(x, y):
        s = add(x, y)
        return add(mul(two, mul(s, add(s, one))), mul(four, y))
    def A(x, y): return add(I(x, y), two)
    def M(x, y): return add(I(x, y), one)
    def E(x, y): return add(I(x, y), three)
    def N(x): return I(x, one)
    def X(x, y): return N(A(x, N(y)))
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
    a, bb, c, d = [env[n] for n in ('a', 'b', 'c', 'd')]
    codes = [X(a, E(a, bb)),
             I(A(a, I(bb, c)), I(A(a, bb), A(a, c))),
             I(E(a, bb), I(M(c, a), M(c, bb))),
             I(A(a, A(bb, c)), A(bb, A(a, c))),
             I(E(c, a), I(M(c, bb), M(a, bb))),
             I(X(a, A(a, bb)), bb),
             I(E(c, a), I(E(c, bb), A(M(a, bb), E(a, bb)))),
             I(I(I(c, d), a), I(I(a, c), I(bb, c))),
             bundle(a, bb, c)]
    return codes, I(a, bb), A(a, bb)

def label_bound_certificate(Builder):
    b = Builder(True)
    m = b.new('m')
    codes, imp, gen = constructors(b, {n:m for n in ('a','b','c','d')})
    outputs = [m, imp, gen]+codes
    exponents = {m[1]:1}
    def weight(a):
        return max(0,(a[1]-1).bit_length()) if a[0]=='c' else exponents[a[1]]
    gates = []
    for (op,a,c),out in b.cache.items():
        e = max(weight(a),weight(c))+1 if op=='add' else weight(a)+weight(c)
        exponents[out[1]] = e
        gates.append({'output':out[1], 'operation':op, 'left':list(a),
                      'right':list(c), 'exponent':e})
    maximum = max(map(weight,outputs))
    emitted = 1 << (maximum-1).bit_length()
    return {'schema':'projected_label_majorant_v1','base':'m+2',
            'input':m[1], 'gates':gates, 'outputs':list(map(list,outputs)),
            'exponent':maximum, 'emitted_exponent':emitted,
            'reason':'m+2>=2; each constructor is monotone; all four inputs<=m'}

def source_pair_calculus(b, source, env, index, include_label_slacks=False):
    if include_label_slacks:
        raise ValueError('Projected labels have no local label slacks')
    expected=['truth','rho1','rho2','rho3','rho4','rho5','rho6','growG','rho8','bundle','mp','gen']
    if [x['name'] for x in source['horn_branches']] != expected:
        raise ValueError('Unrecognized C222 branch order')
    zero, one = ('c',0), ('c',1)
    add,mul,square=b.add,b.mul,b.square
    codes,imp,gen=constructors(b,env)
    carrier=add(env['M0'],one)
    carried_next=mul(env['Sp'],carrier)
    def weight(value): return add(one,mul(carrier,value))
    def update(p,q,v):
        return (add(env['Sp'],mul(carried_next,v)),
                b.product([env['S'],weight(p),weight(q)]))
    axis=update(zero,zero,zero)
    for code in codes[:-1]:
        axis=b.pair_mul(axis,update(zero,zero,code))
    a,bb,c,d=[env[n] for n in ('a','b','c','d')]
    gp,gn=b.pair_square((add(square(c),mul(a,bb)),mul(c,add(a,bb))))
    # Existential d>=0 now represents ((c-a)(c-b))^2-1.
    # This is equivalent to the inherited guard's existential d=|...|-1,
    # since no conclusion code of the bundle branch uses d.
    guard=(gp,add(gn,add(d,one)))
    bundle=b.pair_add(b.pair_square(update(zero,zero,codes[-1])),b.pair_square(guard))
    axis=b.pair_mul(b.pair_mul(axis,update(a,imp,bb)),update(bb,zero,gen))
    total=b.pair_mul(b.pair_square(axis),bundle)
    den=add(mul(add(index,one),env['y']),one)
    nxt=add(den,env['y'])
    for row in [(env['x'],add(env['S'],mul(den,env['u']))),
                (env['x'],add(env['Sp'],mul(nxt,env['vq'])))]:
        total=b.pair_add(total,b.pair_square(row))
    return total
