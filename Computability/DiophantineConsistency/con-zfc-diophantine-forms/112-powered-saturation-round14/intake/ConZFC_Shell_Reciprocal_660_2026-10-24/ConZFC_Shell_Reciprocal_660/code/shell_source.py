"""Square-shell re-encoding of the C222 source calculus.

This changes numeric codes; it does not claim polynomial identity with old
Cantor codes.  The constructor-preserving bijection in shell_encoding_proof.md
transports refutability exactly.  Truth code 0 and falsity code 1 are fixed.
The default xx0 scheme is the low-height choice.  The xy0 alternative rotates
the complementary shell; both have the same elementary decoding theorem.
"""
from build_equation import ZERO,ONE,TWO,FOUR
SHELL_SCHEME='xx0'

def direct_source(b,source,env,index,include_label_slacks,codes_only=False):
    if not hasattr(b,'sqdiff') and not codes_only:
        raise ValueError("shell source requires nonnegative difference-square gates")
    add,mul,square,sd=b.add,b.mul,b.square,getattr(b,'sqdiff',None)
    def square_sum(x,y): return square(add(x,y))
    def I(x,y): return mul(TWO,add(square_sum(x,y),x))
    def M(x,y): return add(I(x,y),ONE)
    def A(x,y):
        # Both orientations enumerate the complementary square-shell interval.
        a,c=(x,y) if SHELL_SCHEME == 'xx0' else (y,x)
        return mul(TWO,b.sum([square_sum(x,y),mul(('c',3),a),mul(FOUR,c),('c',3)]))
    def E(x,y): return add(A(x,y),ONE)
    def N(x):return I(x,ONE)
    def X(x,y):return N(A(x,N(y)))
    def req(x,k,h):return A(x,I(h,N(A(x,I(h,N(M(x,k)))))))
    def clos(x,y,k,h):
        s=A(k,I(M(k,x),M(k,y)))
        tail=I(s,req(y,k,h))
        tail=N(A(x,tail))
        tail=N(A(x,I(h,tail)))
        return A(y,I(M(y,k),tail))
    def bundle(x,y,z):
        nks=A(z,I(clos(x,y,z,z),N(req(y,z,z))))
        vrel=I(M(x,y),A(z,M(x,y)))
        return N(I(vrel,nks))
    a,c_b,c,d,p,q,v=[env[s] for s in ('a','b','c','d','p','q','v')]
    codes=[X(a,E(a,c_b)),I(A(a,I(c_b,c)),I(A(a,c_b),A(a,c))),
           I(E(a,c_b),I(M(c,a),M(c,c_b))),I(A(a,A(c_b,c)),A(c_b,A(a,c))),
           I(E(c,a),I(M(c,c_b),M(a,c_b))),I(X(a,A(a,c_b)),c_b),
           I(E(c,a),I(E(c,c_b),A(M(a,c_b),E(a,c_b)))),
           I(I(I(c,d),a),I(I(a,c),I(c_b,c))),bundle(a,c_b,c)]
    if codes_only:return {'codes':codes,'I':I,'A':A}
    guard=sd(mul(sd(c,a),sd(c,c_b)),square(add(d,ONE)))
    bundle_factor=add(sd(v,codes[-1]),guard)
    axis_squared=b.product([square(v)]+[sd(v,code) for code in codes[:-1]])
    axiom=add(add(square(p),square(q)),mul(axis_squared,bundle_factor))
    mp=sd(q,I(p,v))
    gen=add(square(q),sd(v,A(a,p)))
    horn=b.product([axiom,mp,gen])
    carrier=add(env['M0'],ONE)
    def weight(name):return add(ONE,mul(env[name],carrier))
    rows=[(mul(env['Sp'],weight('v')),b.product([env['S'],weight('p'),weight('q')]))]
    if include_label_slacks:
        rows += [(add(env[name],env['d'+name]),env['m']) for name in ('p','q','v')]
    den=add(mul(add(index,ONE),env['y']),ONE)
    rows += [(env['x'],add(env['S'],mul(den,env['u']))),
             (env['x'],add(env['Sp'],mul(add(den,env['y']),env['vq'])))]
    return b.sum([horn]+[sd(left,right) for left,right in rows]),ZERO
