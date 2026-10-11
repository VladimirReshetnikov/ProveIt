#!/usr/bin/env python3
"""Independent checks for Ordered Hurwitz Germs.

The analytic proofs are in article.tex. Floating-point tests here are
regression diagnostics, NOT interval certificates or proofs.
Run: python verification/verify.py --part exact|integrals|rays|all
Requires mpmath and sympy. All arithmetic is local; no network access.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
from fractions import Fraction
from pathlib import Path
import json
import platform
import time
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent
mp.mp.dps = 55


def enc(x):
    if isinstance(x, (mp.mpf, mp.mpc)):
        return mp.nstr(x, 48)
    return str(x)


def kernel(t):
    if abs(t) < mp.mpf('0.001'):
        # The omitted term is O(t^21); use enough Bernoulli terms for 55 digits.
        return -mp.mpf('0.5') + sum(mp.bernoulli(2*k)*t**(2*k-1)/mp.factorial(2*k) for k in range(1, 11))
    return 1/mp.expm1(t)-1/t


def ell(t):
    return -mp.log(-mp.expm1(-t))


def shifted_L1(t, aa):
    """L_1(exp(-t);a), using its endpoint-subtracted beta integral series."""
    q=mp.exp(-t)
    if q < mp.mpf('0.7'):
        return mp.exp(-aa*t)/aa*mp.hyp2f1(1,aa,aa+1,q)
    w=-mp.expm1(-t)
    val=-mp.log(w)-mp.digamma(aa)-mp.euler
    coefficient=mp.mpf(1)
    wpower=mp.mpf(1)
    for k in range(1,300):
        coefficient *= -(aa-k)/k
        wpower *= w
        term=coefficient*wpower/k
        val-=term
        if abs(term)<mp.mpf('1e-62'):
            return val
    raise ArithmeticError('The endpoint series did not reach its stopping threshold.')


def shifted_generator(t, aa, zz):
    """G_a(z,t) with explicit beta endpoint subtraction near t=0.

    This form stays finite when exp(-t) rounds to 1. Reciprocal Gamma
    also handles a+z=0 without an artificial Gamma-pole exception.
    """
    q=mp.exp(-t)
    if q < mp.mpf('0.7'):
        return zz/aa*mp.exp(-aa*t)*mp.hyp2f1(1,aa+zz,aa+1,q)
    w=-mp.expm1(-t)
    val=mp.gamma(aa)*mp.gamma(1+zz)*mp.rgamma(aa+zz)*w**(-zz)-1
    coefficient=mp.mpf(1)
    wpower=mp.mpf(1)
    for k in range(1,300):
        coefficient *= -(aa-k)/k
        wpower *= w
        term=zz*coefficient*wpower/(zz+k)
        val-=term
        if abs(term)<mp.mpf('1e-62'):
            return val
    raise ArithmeticError('The beta endpoint series did not converge adequately.')


def quad(f):
    return mp.quad(f, [0, mp.mpf('.05'), mp.mpf('.5'), 2, 8, 25, mp.inf])


def g(k, a=1):
    return (-1)**k*mp.stieltjes(k,a)/mp.factorial(k)


def C(d, a=1):
    """Gamma-ratio coefficients from Newton recurrence, not differentiation."""
    p = [mp.mpf(1)]
    for n in range(1,d+1):
        p.append(sum((g(0,a) if k==1 else (-1)**(k+1)*mp.zeta(k,a))*p[n-k] for k in range(1,n+1))/n)
    return p[d]


def P_values(n, L):
    """[z^j] t^z/Gamma(1+z), j <= n, using logarithmic coefficients."""
    p=[mp.mpf(1)]
    for j in range(1,n+1):
        p.append(sum(((L+mp.euler) if k==1 else (-1)**(k+1)*mp.zeta(k))*p[j-k] for k in range(1,j+1))/j)
    return p


def assert_num(records, name, lhs, rhs, tol='1e-40', **meta):
    err=abs(lhs-rhs)
    if err > mp.mpf(tol):
        raise AssertionError(f'{name}: error {enc(err)} > {tol}')
    records.append(dict(name=name, lhs=enc(lhs), rhs=enc(rhs), abs_error=enc(err), tolerance=tol, **meta))


def exact_checks():
    count=0
    controls=0
    t,x,y,z=sp.symbols('t x y z')
    c,d,e=sp.symbols('c d e', nonzero=True)
    h10,h01,g0,g1,g2,C3=sp.symbols('h10 h01 g0 g1 g2 C3')
    # Six individually ordered ray constants versus the labelled symmetric sum.
    from itertools import permutations, product
    fp=lambda a,b,k: C3+(b*h10+k*h01)/a+k*k*g2/(a*(a+b))
    sym=sum(fp(*r) for r in permutations((c,d,e)))
    ratios=sum(a/b for i,a in enumerate((c,d,e)) for j,b in enumerate((c,d,e)) if i!=j)
    target=6*C3+(h10+h01)*ratios+g2*(c*c/(d*e)+d*d/(c*e)+e*e/(c*d))
    assert sp.factor(sym-target)==0; count+=1
    assert sp.factor(sym-target+g2)!=0; controls+=1
    # Divided-difference coefficient for all monomials up to degree 10.
    for m in range(6):
        for n in range(6):
            k=m+n+1
            pol=sp.div((x+y)**k-y**k,x)[0]
            assert sp.expand(pol).coeff(x,m).coeff(y,n)==sp.binomial(k,m+1); count+=1
    # Sharp nonlinear depth-three reparametrization coefficients.
    a,b,k=sp.symbols('a b k')
    f=t+a*t*t+b*t**3+k*t**4
    expect=[-a,3*a*a-2*b,-10*a**3+12*a*b-3*k]
    for j in range(1,4):
        assert sp.expand(sp.series((f/t)**(-j),t,0,j+1).removeO()).coeff(t,j)==expect[j-1]; count+=1
    # Tangential path u=t,v=-t+t^2,w=t.
    pol=1/(t**4*(1+t))+(g0+g1*t+g2*t*t+z*t**3)/t**3+(x+h10*(-t+t*t)+h01*t)/t+C3
    assert sp.series(pol,t,0,1).removeO().coeff(t,0)==1+z-h10+h01+C3; count+=1
    # Reciprocal-gamma polynomial coefficients through degree 7.
    zetas=sp.symbols('Z2:9')
    gg=sp.symbols('G')
    coeff=[sp.Integer(1)]
    logcs=[None,gg]+[(-1)**(j+1)*zetas[j-2] for j in range(2,9)]
    for n in range(1,8):
        coeff.append(sp.expand(sum(logcs[j]*coeff[n-j] for j in range(1,n+1))/n))
        # Independent coefficient extraction by integer partitions, rather
        # than testing the recurrence against its own defining expression.
        direct=0
        for part in sp.utilities.iterables.partitions(n):
            term=sp.Integer(1)
            for j,multiplicity in part.items():
                term *= (logcs[j]/j)**multiplicity/sp.factorial(multiplicity)
            direct += term
        assert sp.expand(coeff[n]-direct)==0; count+=1
    assert sp.expand(coeff[3]-(gg**3-3*gg*zetas[0]+2*zetas[1])/6)==0; count+=1
    # Exact stuffles with arbitrary rational log labels. Merge adds both indices.
    @lru_cache(None)
    def stuffle(A,B):
        if not A: return Counter({B:1})
        if not B: return Counter({A:1})
        out=Counter()
        for w,v in stuffle(A[1:],B).items(): out[(A[0],)+w]+=v
        for w,v in stuffle(A,B[1:]).items(): out[(B[0],)+w]+=v
        merged=(A[0][0]+B[0][0],A[0][1]+B[0][1])
        for w,v in stuffle(A[1:],B[1:]).items(): out[(merged,)+w]+=v
        return out
    @lru_cache(None)
    def finite(w,N,aa):
        if not w: return Fraction(1)
        k,m=w[0]
        # Arbitrary rational "log labels" ensure exact finite algebra checks.
        return sum((Fraction(n+2,n+3)**m/(aa+n)**k)*finite(w[1:],n,aa) for n in range(N))
    words=[((1,0),),((1,1),),((2,0),),((1,0),(1,1)),((1,1),(2,0)),((1,0),)*3]
    for N,aa,A,B in product((3,5),(Fraction(1),Fraction(2,3)),words,words):
        assert finite(A,N,aa)*finite(B,N,aa)==sum(v*finite(w,N,aa) for w,v in stuffle(A,B).items()); count+=1
    # Finite root-of-unity residue selection at q=2 and q=3, algebraic.
    for q in (2,3):
        for p in range(1,q+1):
            for n in range(1,18):
                # Exact modular filter via cyclotomic polynomial remainder.
                X=sp.Symbol('X'); poly=sum(X**((j*(n-p))%q) for j in range(q))
                rem=sp.rem(poly,sp.cyclotomic_poly(q,X),X)
                assert sp.expand(rem)==(q if (n-p)%q==0 else 0); count+=1
    return dict(exact_assertions=count, rejected_corruptions=controls)


def integral_checks():
    rec=[]
    # A complete local master identity checked away from the origin, including complex z.
    for z in [mp.mpf('0.2'),mp.mpf('-0.3'),mp.mpf('1.25'),mp.mpc('.17','.23')]:
        lhs=quad(lambda t: kernel(t)*t**z*mp.expm1(z*ell(t)))
        rhs=1/z-mp.gamma(1+z)*mp.zeta(1+z)
        assert_num(rec,'elementary_master',lhs,rhs,'1e-34',z=enc(z))
    # Full half-plane shifted master, including a negative order and an
    # exceptional value a+z=0 where inverse Gamma, not Gamma, is needed.
    for aa, zz in [(mp.mpf('.7'),mp.mpf('.2')),
                   (mp.mpf('1.3'),mp.mpc('.18','.11')),
                   (mp.mpf('.7'),mp.mpf('-.3')),
                   (mp.mpf('1.3'),mp.mpf('1.2')),
                   (mp.mpf('.4'),mp.mpc('-.25','.2')),
                   (mp.mpf('.4'),mp.mpf('-.4'))]:
        lhs=zz/mp.gamma(1+zz)*quad(lambda t:kernel(t)*t**zz*shifted_generator(t,aa,zz))
        rhs=mp.gamma(aa)*mp.rgamma(aa+zz)-1-zz*(mp.zeta(1+zz,aa)-1/zz)
        assert_num(rec,'Hurwitz_hypergeometric_master',lhs,rhs,'1e-34',a=enc(aa),z=enc(zz))
    # Extracted integral identities at every printed depth, via independent Newton coefficients.
    for depth in range(2,7):
        def integ(t):
            P=P_values(depth-2,mp.log(t)); L=ell(t)
            return kernel(t)*sum(P[depth-r]*L**(r-1)/mp.factorial(r-1) for r in range(2,depth+1))
        lhs=quad(integ)
        assert_num(rec,'all_depth_elementary_Mellin',lhs,C(depth)-g(depth-1),'1e-38',depth=depth)
    # Orientation from two independent, absolutely convergent elementary integrals.
    Iu=quad(lambda t: kernel(t)*(mp.log(t)+mp.euler)*ell(t))
    I3=quad(lambda t: kernel(t)*ell(t)**2/2)
    h10=Iu+g(2)
    assert_num(rec,'cubic_orientation_consistency',h10,C(3)-I3,'1e-42')
    hsum=g(0)*g(1)-mp.diff(lambda s:mp.zeta(s),2)
    omega=2*h10-hsum
    # Independent Euler--Maclaurin accelerated sum for h01, uses only digamma.
    for aa in [mp.mpf(1),mp.mpf('0.7')]:
        N=48; M=22; X=aa+N
        A_v=-sum(mp.log(aa+n)*(mp.log(aa+n)-mp.digamma(aa+n+1))/(aa+n) for n in range(N))
        A_v-=mp.diff(lambda s:mp.zeta(s,X),2)/2
        for j in range(1,M+1):
            A_v+=mp.bernoulli(2*j)/(2*j)*mp.diff(lambda s:mp.zeta(s,X),2*j+1)
        h01=A_v+2*g(2,aa)
        if aa==1:
            assert_num(rec,'orientation_digamma_tail',hsum-h01,h10,'1e-39',N=N,EM_terms=M)
        else:
            iu_shift=quad(lambda t:kernel(t)*(mp.log(t)+mp.euler)*shifted_L1(t,aa))
            total=g(0,aa)*g(1,aa)-mp.diff(lambda ss:mp.zeta(ss,aa),2)
            assert_num(rec,'nonunit_shift_orientation',iu_shift+g(2,aa)+h01,total,'1e-39',a=enc(aa),N=N,EM_terms=M)
        # Gamma-ratio coefficient at an independently evaluated complex circle.
        for depth in (2,3,4):
            radius=mp.mpf('.035'); nodes=32
            lhs=sum(mp.gamma(aa)/mp.gamma(aa+radius*mp.exp(2j*mp.pi*j/nodes))*mp.exp(-2j*mp.pi*depth*j/nodes) for j in range(nodes))/(nodes*radius**depth)
            assert_num(rec,'gamma_ratio_Cauchy',lhs,C(depth,aa),'1e-38',depth=depth,a=enc(aa),nodes=nodes)
        # Convergent-polygamma primitive derivative.
        for depth in (2,3,4):
            deriv=mp.diff(lambda x:C(depth,x),aa)
            rhs=sum((-1)**j*mp.zeta(j+1,aa)*C(depth-j,aa) for j in range(1,depth+1))
            assert_num(rec,'Gamma_polygamma_primitive',deriv,rhs,'1e-42',depth=depth,a=enc(aa))
    (ROOT/'orientation.json').write_text(json.dumps({'a':'1','h10':enc(h10),'h01':enc(hsum-h10),'omega':enc(omega),'Iu':enc(Iu),'I3':enc(I3)},indent=2)+'\n')
    return rec


def double_tail(s,t,A,M):
    """Independent Euler--Maclaurin approximation, not the holomorphic-germ formula."""
    val=mp.zeta(s+t-1,A)/(s-1)-mp.zeta(s+t,A)/2
    for j in range(1,M+1):
        val+=mp.bernoulli(2*j)/mp.factorial(2*j)*mp.rf(s,2*j-1)*mp.zeta(s+t+2*j-1,A)
    return val


def triple_tail(s,t,v,A,M):
    # Collect equal Hurwitz orders before evaluation. This is the same two
    # Euler--Maclaurin expansions, not the theorem being tested.
    bern=[mp.bernoulli(2*j)/mp.factorial(2*j) for j in range(1,M+1)]
    outer=[(-1,1/(s-1)),(0,-mp.mpf(1)/2)]
    outer += [(2*j-1,bern[j-1]*mp.rf(s,2*j-1)) for j in range(1,M+1)]
    coeff={}
    for p,cp in outer:
        st=s+t+p
        inner=[(-1,1/(st-1)),(0,-mp.mpf(1)/2)]
        inner += [(2*j-1,bern[j-1]*mp.rf(st,2*j-1)) for j in range(1,M+1)]
        for q,cq in inner:
            coeff[p+q]=coeff.get(p+q,0)+cp*cq
    return sum(c*mp.zeta(s+t+v+k,A) for k,c in coeff.items())


def finite_nested(ss,N,a):
    # Update suffixes from left to right, so each uses its old inner prefix.
    vals=[mp.mpc(0) for _ in ss]+[mp.mpf(1)]
    for n in range(N):
        x=a+n
        for j,s in enumerate(ss):
            vals[j]+=x**(-s)*vals[j+1]
    return vals[0]


def triple_em(ss,a=1,N=36,M=10):
    s,t,v=ss; A=a+N
    return (finite_nested(ss,N,a)+mp.zeta(s,A)*finite_nested((t,v),N,a)
            +double_tail(s,t,A,M)*finite_nested((v,),N,a)+triple_tail(s,t,v,A,M))


def ray_checks():
    rec=[]
    # Compute orientation by an ordinary integral, separately from the nested-zeta EM evaluator.
    h10=quad(lambda t: kernel(t)*(mp.log(t)+mp.euler)*ell(t))+g(2)
    h01=g(0)*g(1)-mp.diff(lambda s:mp.zeta(s),2)-h10
    rays=[(mp.mpf(1),mp.mpf(1),mp.mpf(2)),(mp.mpf(1),mp.mpf(2),mp.mpf(1))]
    radius=mp.mpf('.025'); nodes=32
    for slopes in rays:
        c,d,e=slopes
        lhs=mp.mpc(0)
        for j in range(nodes):
            eps=radius*mp.exp(2j*mp.pi*j/nodes)
            lhs+=triple_em(tuple(1+x*eps for x in slopes))/nodes
        rhs=C(3)+(d*h10+e*h01)/c+e*e*g(2)/(c*(c+d))
        assert_num(rec,'ordered_triple_directional_FP',lhs,rhs,'1e-25',slopes=list(map(enc,slopes)),radius=enc(radius),Cauchy_nodes=nodes,N=36,EM_terms=10)
    # A non-diagonal ordinary value checked by splitting the cutoff two ways.
    ss=(mp.mpf('1.17'),mp.mpf('1.23'),mp.mpf('1.31'))
    assert_num(rec,'triple_EM_cutoff_stability',triple_em(ss,N=36,M=10),triple_em(ss,N=48,M=12),'1e-26',orders=list(map(enc,ss)))
    return rec


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--part',choices=('exact','integrals','rays','all'),default='all')
    args=ap.parse_args()
    funcs={'exact':exact_checks,'integrals':integral_checks,'rays':ray_checks}
    output={}
    for name,fn in funcs.items():
        if args.part not in (name,'all'): continue
        start=time.time(); data=fn()
        entry={'part':name,'status':'passed','mpmath_dps':mp.mp.dps,'seconds':round(time.time()-start,3),'data':data,
               'python':platform.python_version(),'mpmath':mp.__version__,'sympy':sp.__version__,
               'notice':'Numerical diagnostics are not interval certificates. Analytic proofs are separate.'}
        (ROOT/f'results_{name}.json').write_text(json.dumps(entry,indent=2)+'\n')
        output[name]={'status':'passed','seconds':entry['seconds'],'checks':data if isinstance(data,dict) else len(data)}
        print(json.dumps(output[name]),flush=True)
    return output

if __name__=='__main__': main()
