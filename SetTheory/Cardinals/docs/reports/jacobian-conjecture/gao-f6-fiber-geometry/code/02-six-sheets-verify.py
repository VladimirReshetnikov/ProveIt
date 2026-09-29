#!/usr/bin/env python3
"""Exact reproducibility checks for Six Sheets, Three Escapes.

Run: python code/verify.py
Requires Python >=3.10 and SymPy 1.14.0 (tested).
This is a computer-algebra certificate, not a Lean/Rocq kernel proof.
No floating-point arithmetic, external data, or network access is used.
"""
from __future__ import annotations
import json
import platform
import sys
from pathlib import Path
import sympy as s
from build_map import build_map

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'
DATA.mkdir(exist_ok=True)
LOG: list[str] = []
CHECKS = 0

def say(text: str) -> None:
    LOG.append(text)
    print(text, flush=True)

def check(condition: object, message: str) -> None:
    global CHECKS
    if not bool(condition):
        raise AssertionError(message)
    CHECKS += 1
    say('PASS ' + message)

w, v, c, A, B, D, E, K = s.symbols('w v c A B D E K')
g = 2*w**4 - 2*w**3 - w + 1
J = g + c*A
T = -A + 2*c*B - c**3*K
L = B - c*D
R = s.expand(w*w*J - c*T*w - c*c*L)
Q = s.expand(v*v*J.subs(w, c*v) - T*v - L)


def target_sub(target):
    if len(target) != 5:
        raise ValueError('A target must have five coordinates (c,A,B,D,E).')
    cc, aa, bb, dd, ee = map(s.Rational, target)
    return {c: cc, A: aa, B: bb, D: dd, E: ee,
            K: ee + bb*bb - aa*dd}


def fiber_polynomial(target):
    """Uniform polynomial for source points with x != 0."""
    return s.Poly(Q.subs(target_sub(target)), v, domain=s.QQ)


def simple_part(f: s.Poly) -> s.Poly:
    """Monic product of just the multiplicity-one irreducible factors."""
    if f.is_zero:
        raise ValueError('The zero polynomial has no finite simple part.')
    G = f.gcd(f.diff())
    S = f.exquo(G)
    return S.exquo(S.gcd(G)).monic()


def reconstruct(target, root):
    """Recover the x != 0 preimage of an exact simple Q-root.

    Accepts rational roots. Symbolic algebraic extensions can use the same
    formulas from the article, reducing operations modulo their minimal
    polynomial. Approximate roots are deliberately not accepted here.
    """
    vv = s.Rational(root)
    sub = target_sub(target)
    f = fiber_polynomial(target)
    if f.eval(vv) != 0:
        raise ValueError('Not a root of the uniform fiber polynomial.')
    delta = f.diff().eval(vv)
    if delta == 0:
        raise ValueError('Multiple roots are deleted, not source points.')
    cc, aa, bb, dd, kk = (sub[t] for t in (c,A,B,D,K))
    u1 = vv/delta
    u2 = (dd-2*vv*bb+vv*vv*aa)/delta**3
    u3 = (kk+2*cc*vv**5-2*vv**4)/delta**4
    a1 = (2*u1-2-u3)/58
    a2 = (27*a1-u1+1)/5
    a3 = u2-a1+12*a2-s.Rational(2128,5)*a1*a1
    a4 = cc*delta-1+29*a1-999*a1*a1-355*a1*a2+41553*a1**3
    return tuple(s.cancel(t) for t in
                 (1/delta, a1*delta, a2*delta**2,
                  a3*delta**3, a4*delta**4))


def section(target):
    """The unique preimage on x=0, for a target with c=0."""
    cc, aa, bb, dd, ee = map(s.Rational, target)
    if cc != 0:
        raise ValueError('The section is defined only over c=0.')
    yy = aa
    z1 = (bb+s.Rational(4636,5)*yy**2)/29
    z2 = (dd-s.Rational(6039,5)*yy**3+1041*yy*z1)/5
    z3 = (s.Rational(74000249,25)*yy**4-s.Rational(92717,5)*yy**2*z1
          +5*yy*z2-1041*z1**2-ee)/2
    return (s.S.Zero, yy, z1, z2, z3)


def eval_sparse(poly, point):
    total = s.S.Zero
    for monomial, coefficient in poly.items():
        term = s.Rational(str(coefficient))
        for a, exponent in zip(point, monomial):
            term *= a**exponent
        total += term
    return total


def powmod(base: s.Poly, exponent: int, modulus: s.Poly) -> s.Poly:
    result = s.Poly(1, base.gen, modulus=base.get_modulus())
    while exponent:
        if exponent & 1:
            result = (result*base).rem(modulus)
        base = (base*base).rem(modulus)
        exponent >>= 1
    return result


def irreducible_certificate(f, prime: int) -> bool:
    """Rabin's finite-field irreducibility criterion, using only pow/gcd."""
    ff = s.Poly(f, w, modulus=prime).monic()
    n = ff.degree()
    xx = s.Poly(w, w, modulus=prime)
    if not (powmod(xx, prime**n, ff)-xx).rem(ff).is_zero:
        return False
    for q in s.factorint(n):
        residue = powmod(xx, prime**(n//q), ff)-xx
        if ff.gcd(residue).degree() != 0:
            return False
    return True


def main():
    say('Six Sheets, Three Escapes: exact verification report')
    say('Python '+platform.python_version()+'; SymPy '+s.__version__)
    say('Arithmetic: rational polynomial rings and finite fields only.')

    # Independently construct the actual polynomial map, not its rational chart.
    ring, maps = build_map()
    degrees = [max(map(sum, p)) for p in maps]
    terms = [len(p) for p in maps]
    check(degrees == [7,38,40,42,44], 'polynomial degrees')
    check(terms == [6,342,421,507,904], 'sparse monomial counts')
    say('Degrees: '+str(degrees)+'; monomial counts: '+str(terms))
    data = [[[list(m), str(co)] for m,co in sorted(p.items())] for p in maps]
    (DATA/'map_coefficients.json').write_text(json.dumps(data, separators=(',',':'))+'\n')
    x,y,z1,z2,z3 = s.symbols('x y z1 z2 z3')
    expected = [0,y, -s.Rational(4636,5)*y*y+29*z1,
                s.Rational(6039,5)*y**3-1041*y*z1+5*z2,
                s.Rational(74000249,25)*y**4-s.Rational(92717,5)*y*y*z1
                +5*y*z2-1041*z1*z1-2*z3]
    for i,p in enumerate(maps):
        expr = sum(s.Rational(str(co))*y**m[1]*z1**m[2]*z2**m[3]*z3**m[4]
                   for m,co in p.items() if m[0]==0)
        check(s.expand(expr-expected[i])==0, 'x=0 section coordinate '+str(i))

    a1,a2,a3,a4,ga,u1,u2,u3=s.symbols('a1 a2 a3 a4 ga u1 u2 u3')
    stage=[1-29*a1+999*a1*a1+355*a1*a2-41553*a1**3+a4,
           1+27*a1-5*a2, a1-12*a2+s.Rational(2128,5)*a1*a1+a3,
           -4*a1-10*a2]
    check(s.Matrix(stage).jacobian([a1,a2,a3,a4]).det()==-290,
          'stage Jacobian is -290')
    inv1=(2*u1-2-u3)/58
    inv2=(27*inv1-u1+1)/5
    inv3=u2-inv1+12*inv2-s.Rational(2128,5)*inv1**2
    inv4=ga-1+29*inv1-999*inv1**2-355*inv1*inv2+41553*inv1**3
    for i, expr in enumerate((inv1,inv2,inv3,inv4)):
        check(s.expand(expr.subs(dict(zip((ga,u1,u2,u3),stage)), simultaneous=True)
                       -(a1,a2,a3,a4)[i])==0, 'stage inverse coordinate '+str(i+1))

    ww,vv,kk=s.symbols('ww vv kk')
    G2=vv+ww*kk+ww**2-ww**3
    G3=2*ww*G2+vv
    G4=kk-G2**2+2*ww**4-2*ww**5
    X1=-kk+2*vv-2*ww+2*ww*kk+5*ww**2-2*ww**3+8*ww**4-10*ww**5
    sweep=[X1+ga, G2+ww*(X1+ga), G3+ww**2*(X1+ga), G4+vv*(X1+ga)]
    det=s.factor(s.Matrix(sweep).jacobian([ga,ww,vv,kk]).det(method='domain-ge'))
    check(det==ga, 'sweep Jacobian is gamma')
    Y1,Y2,Y3,Y4=s.symbols('Y1 Y2 Y3 Y4')
    Ry=2*w**6-2*w**5-w**3+(Y1+1)*w*w+(Y4+Y2**2-Y1*Y3-2*Y2+Y1)*w+Y3-Y2
    vy=Y3-2*w*Y2+w*w*Y1
    ky=Y4+Y2*Y2-Y1*Y3+2*w**5-2*w**4
    gamma=Y1-X1.subs({ww:w,vv:vy,kk:ky}, simultaneous=True)
    check(s.expand(gamma-s.diff(Ry,w)+2*Ry)==0, 'gamma = R prime - 2 R')
    check(s.expand(R.subs(w,c*v)-c*c*Q)==0, 'uniform root chart R(cv)=c^2 Q(v)')

    # Normalized order and its six-element free basis.
    zeta=w*J/c
    field=s.QQ.frac_field(c,A,B,D,K)
    rr=s.Poly(R,w,domain=field)
    def zero_mod(expr):
        return s.Poly(s.cancel(expr),w,domain=field).rem(rr).is_zero
    check(zero_mod(w*zeta-T*w-c*L), 'normalization relation w*zeta')
    check(zero_mod(zeta*zeta-T*zeta-L*J), 'normalization relation zeta^2')
    check(s.expand(2*w**5-c*zeta-2*w**4-w*w+(1+c*A)*w)==0,
          'normalization relation w^5')
    check(s.expand(Q.subs(c,0)-(v*v+A*v-B))==0, 'exceptional quadratic')

    aa,bb,dd=s.symbols('aa bb dd')
    Delta=s.discriminant(2*w**6-2*w**5-w**3+aa*w*w+bb*w+dd,w)
    # K is an independent coordinate: E=K-B^2+AD.
    substituted=s.Poly(s.expand(Delta.subs({aa:1+c*A, bb:-c*T, dd:-c*c*L},
                                         simultaneous=True)),c,A,B,D,K)
    check(min(m[0] for m in substituted.monoms())==2,
          'sextic discriminant has exactly the forced factor c^2')
    H=s.Poly.from_dict({(m[0]-2,)+m[1:]:co for m,co in substituted.terms()},
                       (c,A,B,D,K)).as_expr()
    check(s.expand(H.subs(c,0)+108*(A*A+4*B))==0,
          'normalized discriminant H(0)=-108(A^2+4B)')
    check(s.discriminant(g,w)==-108, 'four residual boundary roots are distinct')
    (DATA/'normalized_discriminant.json').write_text(json.dumps({
        'variables':['c','A','B','D','K'], 'K':'E+B^2-A*D',
        'terms':[[list(m),str(co)] for m,co in s.Poly(H,c,A,B,D,K).terms()]
    },separators=(',',':'))+'\n')
    say('Normalized discriminant terms: '+str(len(s.Poly(H,c,A,B,D,K).terms())))

    # Exhaustive all-multiple partitions of six.
    r,t=s.symbols('r t')
    for exponents in ((6,), (4,2), (3,3)):
        if exponents==(6,): f=(w-r)**6; unknown=(r,)
        else: f=(w-r)**exponents[0]*(w-t)**exponents[1]; unknown=(r,t)
        f=s.Poly(f,w)
        equations=[f.nth(5)+1,f.nth(4),f.nth(3)+s.Rational(1,2)]
        basis=s.groebner(equations,*unknown)
        check(list(basis)==[1], 'all-multiple partition '+str(exponents)+' impossible')
    cubic=w**3-w*w/2-w/8-s.Rational(5,16)
    square=2*cubic*cubic
    check(s.Poly(s.expand(square),w).all_coeffs()[:4]==[2,-2,0,-1],
          'unique square matches all fixed leading coefficients')
    check(s.discriminant(cubic,w)==-s.Rational(401,128),
          'omitted fiber has three distinct double roots')

    witnesses={
       0:(1,-s.Rational(11,32),0,s.Rational(25,128),s.Rational(1773,4096)),
       1:(0,0,0,0,0),
       2:(1,-s.Rational(11,8),0,-s.Rational(1,16),s.Rational(171,128)),
       3:(1,-8,0,-7,79),
       4:(1,0,0,0,0),
       6:(1,0,0,1,0),
    }
    for count,target in witnesses.items():
        q=fiber_polynomial(target)
        result=simple_part(q).degree()+int(target[0]==0)
        check(result==count, 'geometric fiber witness '+str(count))
        say('  target '+str(target)+'; Q='+str(s.factor(q.as_expr())))
    tpar=s.symbols('tpar')
    missing={c:1,A:-s.Rational(11,32), B:tpar,
             D:tpar+s.Rational(25,128),
             K:2*tpar+s.Rational(1,2)}
    check(s.expand(R.subs(missing)-square)==0, 'entire omitted surface parametrization')

    # Exact round trips including the gamma=0 chart.
    for point in [(1,0,0,0,0),(1,0,0,0,-1),(2,1,0,0,0),(-1,1,2,-1,3)]:
        point=tuple(map(s.Rational,point))
        target=tuple(eval_sparse(p,point) for p in maps)
        root=1/point[0]+27*point[1]-5*point[0]*point[2]
        check(reconstruct(target,root)==point, 'exact reconstruction '+str(point))
    for target in [(0,0,0,0,0),(0,1,2,3,4),(0,0,1,0,0)]:
        point=section(target)
        check(tuple(eval_sparse(p,point) for p in maps)==tuple(map(s.Rational,target)),
              'exact section inverse '+str(target))

    # Geometric S6 and an arithmetic S6 specialization.
    p0=2*w**6-2*w**5-w**3+w*w
    h=s.symbols('h')
    dh=s.factor(s.discriminant(p0+h,w))
    expected=-4*h*(32*h+3)*(11664*h**3-5680*h*h+1149*h-36)
    check(s.expand(dh-expected)==0, 'Morse-line discriminant factorization')
    check(s.Poly(dh,h).gcd(s.Poly(s.diff(dh,h),h)).degree()==0,
          'five distinct simple branch values on the Morse line')
    ff=p0+1
    check(s.discriminant(ff,w)==-993580, 'arithmetic specialization discriminant')
    modular={
       3: [w**6-w**5+w**3-w*w-1],
       13: [w-4,w**5+3*w**4-w**3+2*w*w+2*w-5],
       37: [w+14,w-16,w-7,w-5,w*w+13*w+14],
    }
    for prime,factors in modular.items():
        check(s.Poly(ff-2*s.prod(factors),w,modulus=prime).is_zero,
              'displayed factorization modulo '+str(prime))
        for i,factor in enumerate(factors):
            check(irreducible_certificate(factor,prime),
                  'Rabin certificate modulo '+str(prime)+' factor '+str(i+1))
        check(s.Poly(ff,w,modulus=prime).gcd(s.Poly(s.diff(ff,w),w,modulus=prime)).degree()==0,
              'unramified reduction modulo '+str(prime))

    # Real simple root counts, by exact Sturm sequences.
    for target,count in [((1,0,0,1,0),0),((0,0,0,0,0),1),
                         ((1,0,0,0,0),2),((0,0,1,0,0),3),
                         ((1,-8,0,-6,70),4)]:
        sp=simple_part(fiber_polynomial(target))
        real_count=sp.count_roots(-s.oo,s.oo)+int(target[0]==0)
        check(real_count==count, 'real fiber witness '+str(count))

    say('ALL '+str(CHECKS)+' EXACT CHECKS PASSED.')
    say('The written proofs, not these finite tests alone, establish the universal theorems.')
    (DATA/'verification_report.txt').write_text('\n'.join(LOG)+'\n')

if __name__=='__main__':
    main()
