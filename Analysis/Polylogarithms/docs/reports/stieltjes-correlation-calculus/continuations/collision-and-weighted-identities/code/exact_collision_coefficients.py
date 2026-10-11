"""Exact finite coefficient extraction for the colliding-grid jet kernel.

Uses only truncated rational polynomial algebra; gamma ratios are expanded
by the proved logarithmic identity. Z_j means zeta^(j)(N+1), while zeta(j)
inside the gamma-ratio coefficients retains its ordinary exact meaning.
"""
import argparse
import json
from pathlib import Path
import sympy as sp

z,w,A,B,K,P,Q=sp.symbols('z w A B K P Q')


def truncate(expr, degree):
    return sp.Add(*(c*z**i*w**j for (i,j),c in sp.Poly(sp.expand(expr),z,w).terms()
                    if i+j<=degree))


def exponential(expr,degree):
    total,term=sp.Integer(1),sp.Integer(1)
    for j in range(1,degree+1):
        term=truncate(term*expr/j,degree)
        total+=term
    return sp.expand(total)


def divide(poly,var):
    other=w if var==z else z
    assert sp.expand(poly.subs(var,0))==0
    return sp.Poly(poly,var).exquo(sp.Poly(var,var)).as_expr()


def coefficient(m,n,r,k):
    if r+k==0:
        return coefficient_zero_order(m,n)
    N,D=r+k,m+n+1
    Z=sp.symbols('Z0:'+str(D+1))
    W=truncate(sp.rf(1-z-w,N)*sum((-1)**j*Z[j]*(z+w)**j/sp.factorial(j)
                                 for j in range(D+1)),D)
    logR=sum(sp.zeta(j)*((z+w)**j+(-1)**j*z**j-w**j)/j for j in range(2,D+1))
    R=exponential(logR,D)
    V=truncate(R*W,D)
    Ww=W.subs(z,0)
    pr=sp.rf(1-z,r)/sp.factorial(r)
    pk=sp.rf(1-w,k)/sp.factorial(k)
    first=divide(truncate(V-exponential(K*z,D)*pr*Ww,D),z)
    Vswap=V.xreplace({z:w,w:z})
    second=divide(truncate(Vswap-exponential(K*w,D)*pk*Ww.xreplace({w:z}),D),w)
    expression=truncate(exponential(-B*z-A*w,D-1)*
                        ((-1)**k*first+(-1)**r*second),D-1)
    return sp.expand(Q**r*P**k*sp.factorial(m)*sp.factorial(n)*
                     expression.coeff(z,m).coeff(w,n))


def coefficient_zero_order(m,n):
    """Zero-argument-derivative Stieltjes coefficients, including scalar poles."""
    M,D=m+n,m+n+2
    G=sp.symbols('G0:'+str(M+2))
    logR=sum(sp.zeta(j)*((z+w)**j+(-1)**j*z**j-w**j)/j for j in range(2,D+1))
    R=exponential(logR,D)
    numerator=w*R+z*R.xreplace({z:w,w:z})
    T=sp.Poly(numerator,z,w).exquo(sp.Poly(z+w,z,w)).as_expr()
    gs=sum(G[j]*(z+w)**j/sp.factorial(j) for j in range(M+2))
    gz=gs.subs(w,0)
    gw=gs.subs(z,0)
    numerator=truncate(1-T+(z+w)*T*gs-w*gw-z*gz,D)
    base=divide(divide(numerator,z),w)
    Lp,Lq=K-B,K-A
    first=divide(exponential(-B*z,M+1)-exponential(Lp*z,M+1),z)
    second=divide(exponential(-A*w,M+1)-exponential(Lq*w,M+1),w)
    scalar=(1-exponential(-B*z-A*w,D)-exponential(Lp*z,D)+
            exponential(Lp*z-A*w,D)-exponential(Lq*w,D)+
            exponential(Lq*w-B*z,D))
    scalar=divide(divide(sp.expand(scalar),z),w)
    expression=truncate(exponential(-B*z-A*w,M)*base+
                        exponential(-A*w,M)*first*gw+
                        exponential(-B*z,M)*second*gz+scalar,M)
    return sp.expand(sp.factorial(m)*sp.factorial(n)*expression.coeff(z,m).coeff(w,n))


def certificates():
    rows=[]
    for r in range(4):
        for k in range(4):
            if not r+k:
                continue
            N=r+k
            Z0,Z1=sp.symbols('Z0 Z1')
            h=lambda j:sp.harmonic(j) if j else 0
            expected=sp.factorial(N)*Q**r*P**k*(
                (-1)**(k+1)*(Z1+(h(N)-h(r)+K)*Z0)+
                (-1)**(r+1)*(Z1+(h(N)-h(k)+K)*Z0))
            assert sp.expand(coefficient(0,0,r,k)-expected)==0
    Z0,Z1,Z2=sp.symbols('Z0 Z1 Z2')
    expected10=P*(Z2/2+K*Z1+(K*K/2+K-B-1)*Z0)
    expected01=P*(-Z2/2-(K+1)*Z1-(K*K/2+A)*Z0)
    assert sp.expand(coefficient(1,0,0,1)-expected10)==0
    assert sp.expand(coefficient(0,1,0,1)-expected01)==0
    for case in [(1,0,0,1),(0,1,0,1),(1,1,0,1),(2,0,1,1),(0,2,1,1)]:
        expr=coefficient(*case)
        swapped=coefficient(case[1],case[0],case[3],case[2]).xreplace({A:B,B:A,P:Q,Q:P})
        assert sp.expand(expr-swapped)==0
        m,n,r,k=case
        M,N=m+n,r+k
        top=((-1)**(M+1)*sp.factorial(N)*Q**r*P**k*
             (sp.Rational((-1)**k,m+1)+sp.Rational((-1)**r,n+1)))
        assert sp.expand(expr.coeff(sp.Symbol('Z'+str(M+1)))-top)==0
        rows.append({'m':case[0],'n':case[1],'r':case[2],'k':case[3],
                     'N':case[2]+case[3],'expression':str(expr),'latex':sp.latex(expr)})
    for r,k in [(0,1),(2,1),(1,2)]:
        N=r+k
        diagonal=(coefficient(1,1,r,k)+A*coefficient(1,0,r,k)+
                  B*coefficient(0,1,r,k)+A*B*coefficient(0,0,r,k))
        kap=lambda j:sp.expand(exponential(K*z,2)*sp.rf(1-z,j)/sp.factorial(j)).coeff(z,2)
        omega=-sp.factorial(N)*(sp.Symbol('Z1')+sp.harmonic(N)*sp.Symbol('Z0'))
        expected=(-1)**k*Q**r*P**k*(kap(k)-kap(r))*omega
        assert sp.expand(diagonal-expected)==0
    G0,G1,G2,G3=sp.symbols('G0:4')
    expected00=2*G1-2*sp.zeta(2)-2*G0*K-K*K+(K-B)*(K-A)
    assert sp.expand(coefficient(0,0,0,0)-expected00)==0
    assert sp.expand(coefficient(1,0,0,0).subs({A:0,B:0,K:0})-
                     (sp.Rational(3,2)*G2+2*sp.zeta(2)*G0-sp.zeta(3)))==0
    assert sp.expand(coefficient(1,1,0,0).subs({A:0,B:0,K:0})-
                     (G3+4*sp.zeta(2)*G1+2*sp.zeta(3)*G0-sp.zeta(2)**2-sp.zeta(4)))==0
    out={'convention':'Z_j = zeta^(j)(N+1) for N>0; G_j=gamma_j for N=0; A=log P, B=log Q, K=log lcm(p,q)',
         'exact_checks':{'polygamma_coefficients':15,'first_jet_identities':2,
                         'factor_exchange_symmetries':5,'highest_derivative_coefficients':5,
                         'odd_order_diagonal_collapses':3,'zero_order_stieltjes_coefficients':3},
         'coefficients':rows}
    (Path(__file__).resolve().parent.parent / 'results' / 'exact_collision_coefficients.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out['exact_checks']))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('indices',type=int,nargs='*',help='nonnegative indices m n r k')
    args=parser.parse_args()
    if not args.indices:
        certificates()
    else:
        if len(args.indices)!=4:
            parser.error('provide m n r k')
        print(sp.latex(coefficient(*args.indices)))
