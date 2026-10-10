#!/usr/bin/env python3
"""Exact rational and symbolic checks supporting (not replacing) the proofs."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json
import random
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def mean(xs):
    xs=list(xs)
    return sum(xs,F(0))/len(xs)

def c4(W):
    m,n=len(W),len(W[0])
    return mean(mean(mean(W[i][j]*W[k][j] for j in range(n))**2
                     for k in range(m)) for i in range(m))

def stats(W):
    m,n=len(W),len(W[0])
    p=mean(z for row in W for z in row)
    a=[mean(row)-p for row in W]
    b=[mean(W[i][j] for i in range(m))-p for j in range(n)]
    C=[[W[i][j]-p-a[i]-b[j] for j in range(n)] for i in range(m)]
    A2,B2=mean(z*z for z in a),mean(z*z for z in b)
    ca=[mean(C[i][j]*a[i] for i in range(m)) for j in range(n)]
    cb=[mean(C[i][j]*b[j] for j in range(n)) for i in range(m)]
    mixed=mean(a[i]*cb[i] for i in range(m))
    D=c4(W)-p**4
    C4=c4(C)
    rhs=C4+A2*A2+B2*B2+2*p*p*(A2+B2)+2*mean(x*x for x in ca)+2*mean(x*x for x in cb)+4*p*mixed
    assert D==rhs
    assert D>=C4+A2*A2+B2*B2+F(3,2)*p*p*(A2+B2)
    return p,D,C4,A2,B2

def cut_norm(W,p):
    m,n=len(W),len(W[0]); ans=F(0)
    for I in range(1<<m):
        col=[sum((W[i][j]-p for i in range(m) if I>>i&1),F(0)) for j in range(n)]
        ans=max(ans,sum((x for x in col if x>0),F(0)), -sum((x for x in col if x<0),F(0)))
    return ans/(m*n)

def root_lower(x,bits=60):
    lo,hi=F(0),F(2)
    assert hi**4>=x>=0
    for _ in range(bits):
        mid=(lo+hi)/2
        if mid**4<=x:lo=mid
        else:hi=mid
    return lo

def step(W,rr,cc):
    m,n=len(W),len(W[0])
    R=[[i for i in range(m) if rr[i]==v] for v in sorted(set(rr))]
    C=[[j for j in range(n) if cc[j]==v] for v in sorted(set(cc))]
    out=[[F(0) for j in range(n)] for i in range(m)]
    for I in R:
        for J in C:
            av=mean(W[i][j] for i in I for j in J)
            for i in I:
                for j in J:out[i][j]=av
    return out

def symbolic_checks():
    a,b,c,p=s.symbols('a b c p',real=True)
    M=s.Matrix([[p,b],[a,c]])
    expected=p**4+c**4+a**4+b**4+2*(p*p+c*c)*(a*a+b*b)+4*p*a*b*c
    assert s.expand(s.trace((M.T*M)**2)-expected)==0
    # Rescaled six-variable IFT system at t=0; order fixes determinant sign.
    v,l,x,y,h,k=s.symbols('v l x y h k')
    E=s.Matrix([v**4-1,s.Rational(1,4)-4*l*v**3,
                s.Rational(1,4)-4*l*x,s.Rational(1,4)-4*l*y,
                y/2-h*v,x/2-k*v])
    point={v:1,l:s.Rational(1,16),x:1,y:1,h:s.Rational(1,2),k:s.Rational(1,2)}
    J=E.jacobian([v,l,x,y,h,k]).subs(point)
    assert E.subs(point)==s.zeros(6,1)
    assert J.det()==-1
    t=s.symbols('t')
    expansions={}
    for sg in (-1,1):
        uu=t**3-sg*t**4-2*t**5+7*sg*t**6+t**7
        vv=t-t**3+sg*t**4+s.Rational(5,2)*t**5-9*sg*t**6
        qq=s.Rational(1,2)+t*t/2-sg*t**3/2-t**4+s.Rational(7,2)*sg*t**5-t**6/2
        ss=s.series(s.sqrt(qq*(1-qq)),t,0,9).removeO()
        E1=vv**4+4*(1+sg*vv+vv**2)*uu**2+2*uu**4-t**4
        E2=qq*(vv**3+(sg+2*vv)*uu**2)-ss*uu*(1+sg*vv+vv**2+uu**2)
        E3=uu*qq*(3-4*qq)+vv*ss*(1-2*qq)
        assert s.series(E1,t,0,10).removeO()==0
        assert s.series(E2,t,0,8).removeO()==0
        assert s.series(E3,t,0,8).removeO()==0
        phi=s.series(2*qq*ss*uu+qq*(1-qq)*vv,t,0,7).removeO().expand()
        target=t/4+t**3/4-sg*t**4/4-t**5/8+sg*3*t**6/4
        assert s.expand(phi-target)==0
        expansions[str(sg)]=str(phi)
    # Exact elimination for the one-parameter formula.
    r,kk,vv,sg=s.symbols('r k v sg')
    A=r*(1+2*kk**2)-kk*(1+kk**2)
    B=sg*(r*kk**2-kk)
    ratio=r*(vv**3+(sg+2*vv)*(kk*vv)**2)-kk*vv*(1+sg*vv+vv**2+(kk*vv)**2)
    assert s.expand(ratio-vv*(A*vv**2+B*vv-kk))==0
    # Rounding-curvature identities and inverse-envelope series.
    xx=s.symbols('xx', positive=True)
    gg=2*xx*s.sqrt(xx*(1-xx))
    assert s.simplify(s.diff(gg,xx,2)-(8*xx**2-12*xx+3)/(2*s.sqrt(xx)*(1-xx)**s.Rational(3,2)))==0
    assert s.simplify(s.diff(gg,xx,3)+3/(4*xx**s.Rational(3,2)*(1-xx)**s.Rational(5,2)))==0
    assert s.simplify(s.diff(gg,xx,2).subs(xx,s.Rational(1,3))+s.sqrt(2)/8)==0
    assert s.simplify(s.diff(gg,xx,2).subs(xx,s.Rational(2,3))+13*s.sqrt(2)/4)==0
    zz=s.symbols('zz')
    tt=zz-zz**3-zz**4+s.Rational(7,2)*zz**5
    assert s.series(tt+tt**3+tt**4-tt**5/2-zz,zz,0,6).removeO()==0
    assert s.series(tt**4,zz,0,9).removeO()==zz**4-4*zz**6-4*zz**7+20*zz**8
    return {'scalar_identity':True,'ift_jacobian_determinant':-1,
            'series_through_t6':expansions,'parametric_elimination':True,
            'rounding_curvature_identities':True,'inverse_envelope_series':True}

def main():
    symbolic=symbolic_checks()
    cases=0
    for bits in product((0,1),repeat=9):
        W=[[F(bits[3*i+j]) for j in range(3)] for i in range(3)]
        p,D,*_=stats(W)
        K=cut_norm(W,p)
        if not D:assert K==0
        elif p:
            d=root_lower(D)
            assert K<=d/4+F(2,3)*d**3/p**2
        V=step(W,[0,1,1],[0,0,1])
        assert c4(V)<=c4(W)
        cases+=1
    rng=random.Random(20261008)
    for _ in range(120):
        m,n=rng.randrange(2,6),rng.randrange(2,6)
        W=[[F(rng.randrange(21),20) for _ in range(n)] for _ in range(m)]
        p,D,*_=stats(W)
        K=cut_norm(W,p)
        if D and p:
            d=root_lower(D)
            assert K<=d/4+F(2,3)*d**3/p**2
        V=step(W,[i%2 for i in range(m)],[j%2 for j in range(n)])
        assert c4(V)<=c4(W)
        cases+=1
    p,a=F(2,5),F(1,100); f=[F(1),F(-1)]
    W=[[p+a*(x+y)-p*x*y/2 for y in f] for x in f]
    p,D,C4,A2,B2=stats(W)
    sharp_ratio=(D-C4-A2*A2-B2*B2)/(p*p*(A2+B2))
    assert sharp_ratio==F(3,2)
    p,v=F(1,2),F(1,10);u=v**3
    W=[[p*(1-u*(x+y)-v*x*y) for y in f] for x in f]
    p,D,*_=stats(W);K=cut_norm(W,p)
    assert (4*K)**4>D
    result={'status':'PASS','method':'Exact Fraction arithmetic and symbolic polynomial identities',
            'matrix_cases':cases,'exhaustive_3_by_3_binary_cases':512,
            'seeded_rational_matrix_cases':120,'symbolic':symbolic,
            'sharp_degree_coefficient':str(sharp_ratio),
            'irregular_witness':{'p':str(p),'u':str(u),'v':str(v),
                'cut_norm':str(K),'C4_excess':str(D),
                'excess_of_256_cut_fourth_over_C4_excess':str((4*K)**4-D)},
            'limitation':'Finite checks are not a formalization or a substitute for the analytic proofs.'}
    (ROOT/'results'/'exact_verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
