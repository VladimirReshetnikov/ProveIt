"""Exact identities and independent numerical checks for quartic Tornheim rays.

The Jonquiere/incomplete-Gamma evaluator is adapted from the incoming
Independent Orders report's check_cubic_rays.py. Floating-point output is a
diagnostic, not an interval certificate. Exact rational/polynomial assertions
verify the printed finite algebra and the formal dimension count.
"""
from pathlib import Path
import argparse
import json
import time
import mpmath as mp
import sympy as sp


def exact_checks():
    a,b,c = sp.symbols('a b c')
    L,z2,z3,z4,y4,La,U,X = sp.symbols('L z2 z3 z4 y4 Lambda U Xi')
    w=(z2*z2-z4)/4
    y=(-L*z3/2-z4-U)/3
    z=(y4-z4)/4
    x=(La+8*L*z3-12*z2*z2+16*z4)/24-X
    direct=-(a**4+b**4)*z4/2-2*a*b*(a*a+b*b)*L*z3+6*a*a*b*b*z2*z2
    direct-=c*(b**4/(a+c)+a**4/(b+c))*y4
    direct+=4*c*(U*(a**3+b**3)+3*X*a*b*(a+b)+3*w*c*(a*a+b*b)
                 +6*x*a*b*c+3*y*c*c*(a+b)+z*c**3)
    expected=a*b*c*c*La+4*c*(a**3+b**3-c*c*(a+b))*U+12*a*b*c*(a+b-2*c)*X
    expected-=2*(a*b*(a*a+b*b-4*c*c)+c**3*(a+b))*L*z3
    expected+=3*(2*a*a*b*b+c*c*(a*a+b*b-4*a*b))*z2*z2
    expected+=(-(a**4+b**4)/2+16*a*b*c*c-3*c*c*(a*a+b*b)-4*c**3*(a+b)-c**4)*z4
    expected+=(c**4-c*b**4/(a+c)-c*a**4/(b+c))*y4
    assert sp.cancel(direct-expected)==0
    cyclic=sp.cancel(sum(expected.xreplace(dict(zip((a,b,c),v)))
                         for v in ((a,b,c),(b,c,a),(c,a,b))))
    e1=a+b+c;e2=a*b+a*c+b*c;e3=a*b*c
    target=e1*e3*La+(-4*e1*e1*e2+8*e2*e2+12*e1*e3)*L*z3
    target+=(12*e2*e2-36*e1*e3)*z2*z2
    target+=(-2*e1**4+4*e1*e1*e2-2*e2*e2+24*e1*e3)*z4
    assert sp.cancel(cyclic-target)==0
    assert sp.cancel(expected.subs({a:1,b:1,c:1})-La)==0
    # T(t,0,t) = (zeta(t)^2-zeta(2t))/2.
    assert sp.cancel(expected.subs({a:1,b:0,c:1})+sp.Rational(17,2)*z4
                     +2*L*z3-3*z2*z2)==0
    assert sp.cancel(target.subs({a:1,b:2,c:3})
                     -(36*La-184*L*z3+156*z2*z2-386*z4))==0
    # Directly construct the constraint matrix, instead of testing a
    # dimension formula against a hardcoded sequence.
    dimension_rows=[]
    for degree in range(0,11):
        monomials=[]
        for k in range(degree+1):
            for i in range(degree-k+1):
                j=degree-k-i
                if i<j:continue
                monomials.append(a**i*b**j*c**k+(a**j*b**i*c**k if i!=j else 0))
        boundary=[sp.expand(p.subs(b,0)) for p in monomials]
        axis=[sp.expand(p.subs({a:0,b:0})) for p in monomials]
        euler=[sp.expand(c*q+a*q.xreplace({a:c,c:a})) for q in boundary]
        rows=[]
        rows.append([sp.expand(p).coeff(c,degree) for p in axis])
        for i in range(degree+2):
            rows.append([sp.Poly(q,a,c).coeff_monomial(a**i*c**(degree+1-i)) for q in euler])
        rank=sp.Matrix(rows).rank()
        freedom=len(monomials)-rank
        predicted=degree//2+degree*degree//4 if degree>=2 else 0
        assert freedom==predicted,(degree,freedom,predicted)
        cyc_polys=[sp.expand(c*p+a*p.xreplace({a:b,b:c,c:a})
                            +b*p.xreplace({a:c,b:a,c:b})) for p in monomials]
        ker=sp.Matrix(rows).nullspace()
        cyc_free=[sp.expand(sum(v[j]*cyc_polys[j] for j in range(len(monomials)))) for v in ker]
        if cyc_free:
            powers=sorted(set().union(*(sp.Poly(p,a,b,c).monoms() for p in cyc_free)))
            mat=sp.Matrix([[sp.Poly(p,a,b,c).coeff_monomial(a**i*b**j*c**k)
                            for p in cyc_free] for i,j,k in powers])
            cyc_rank=mat.rank()
        else:cyc_rank=0
        cyc_pred=((degree+1)**2+3)//12 if degree>=2 else 0
        assert cyc_rank==cyc_pred,(degree,cyc_rank,cyc_pred)
        dimension_rows.append({'remainder_degree':degree,'raw_dimension':len(monomials),
                               'constraint_rank':rank,'free_dimension':freedom,
                               'cyclic_free_dimension':cyc_rank})
    # The explicit elementary correction accompanying the convergent Xi
    # integral is checked from Gamma's Taylor series, independently of
    # the hand expansion in the article.
    A,B,g,h2,h3,z1,z_2,y1,y2=sp.symbols('A B g h2 h3 z1 z_2 y1 y2')
    G=lambda t:1+g*t+(g*g+h2)*t*t/2+(g**3+3*g*h2+2*h3)*t**3/6
    Z=lambda t:-sp.Rational(1,2)+z1*t+z_2*t*t/2
    Y=lambda t:-sp.Rational(1,12)+y1*t+y2*t*t/2
    J=lambda t:g+(g*g+h2)*t/2+(g**3+3*g*h2+2*h3)*t*t/6
    rational=G(A)*G(B)/(A+B-2)+G(A)*Z(B)/(A-1)+G(B)*Z(A)/(B-1)
    rational+=g*Z(A)*Z(B)-J(A)*Y(B)-J(B)*Y(A)
    differentiated=sp.diff(rational,A,2,B).subs({A:0,B:0})
    printed=-(g**3+g*h2)/2-(3*g*g+h2)/4-3*g/4-sp.Rational(3,8)
    printed-=(g*g+h2+2*g+2)*z1+(g+1)*z_2
    printed+=g*z_2*z1-(g**3+3*g*h2+2*h3)*y1/3-(g*g+h2)*y2/2
    assert sp.expand(differentiated-printed)==0
    return {'quartic_polynomial':True,'cyclic_polynomial':True,'diagonal':True,
            'Euler_diagonal':True,'cyclic_123':True,'Xi_elementary_correction':True,
            'formal_dimension_checks':dimension_rows}


def tornheim(a,b,c,K,N):
    ga,gb=mp.gamma(1-a),mp.gamma(1-b)
    za=[(-1)**k*mp.zeta(a-k)/mp.factorial(k) for k in range(K+1)]
    zb=[(-1)**k*mp.zeta(b-k)/mp.factorial(k) for k in range(K+1)]
    terms=[ga*gb/(a+b+c-2)]
    terms.extend(ga*zb[k]/(a+c-1+k) for k in range(K+1))
    terms.extend(gb*za[k]/(b+c-1+k) for k in range(K+1))
    terms.extend(za[j]*zb[k]/(c+j+k) for j in range(K+1) for k in range(K+1))
    small=mp.fsum(terms)
    left=[mp.power(j,-a) for j in range(1,N)]
    right=[mp.power(j,-b) for j in range(1,N)]
    large=mp.fsum(mp.gammainc(c,k,mp.inf)/mp.power(k,c)
                  *mp.fsum(left[j-1]*right[k-j-1] for j in range(1,k))
                  for k in range(2,N+1))
    return (small+large)/mp.gamma(c)


def fourth_ray(a,b,c,K,N,h):
    nodes=list(range(-8,0))+list(range(1,9))
    weights=sp.finite_diff_weights(4,nodes,0)[-1][-1]
    terms=[]
    for n,w in zip(nodes,weights):
        terms.append(mp.mpf(int(w.p))/int(w.q)*tornheim(a*n*h,b*n*h,c*n*h,K,N))
    return mp.fsum(terms)/h**4


def u_coordinate(ncut=45,order=22):
    L=mp.log(2*mp.pi)
    def rho(n):
        n=mp.mpf(n)
        return mp.loggamma(n+1)-(n+mp.mpf('0.5'))*mp.log(n)+n-L/2-1/(12*n)
    direct=mp.fsum(mp.log(n)**3*rho(n) for n in range(1,ncut))
    tail=mp.fsum(-mp.bernpoly(2*j,0)/(2*j*(2*j-1))*mp.zeta(2*j-1,ncut,derivative=3)
                 for j in range(2,order+1))
    M3=direct+tail
    U=-M3-mp.zeta(-1,derivative=4)-mp.zeta(0,derivative=4)/2-mp.zeta(-1,derivative=3)-mp.stieltjes(3)/12
    return U,M3


def xi_coordinate(K,N):
    g=mp.euler;h2=mp.zeta(2);h3=mp.zeta(3)
    z1=mp.zeta(0,derivative=1);z2=mp.zeta(0,derivative=2)
    y1=mp.zeta(-1,derivative=1);y2=mp.zeta(-1,derivative=2)
    c1=[(-1)**k*mp.zeta(-k,derivative=1)/mp.factorial(k) for k in range(K+1)]
    c2=[(-1)**k*mp.zeta(-k,derivative=2)/mp.factorial(k) for k in range(K+1)]
    small=mp.fsum(c1[k]*(2/mp.mpf(k-1)**3-2*g/mp.mpf(k-1)**2+(g*g+h2)/(k-1))
                  +c2[k]*(g/(k-1)-1/mp.mpf(k-1)**2) for k in range(2,K+1))
    small+=mp.fsum(c2[j]*c1[k]/(j+k) for j in range(K+1) for k in range(K+1) if j+k)
    large=-mp.fsum(mp.e1(k)*mp.fsum(mp.log(j)**2*mp.log(k-j) for j in range(1,k))
                   for k in range(2,N+1))
    correction=-(g**3+g*h2)/2-(3*g*g+h2)/4-3*g/4-mp.mpf(3)/8
    correction-=(g*g+h2+2*g+2)*z1+(g+1)*z2
    correction+=g*z2*z1-(g**3+3*g*h2+2*h3)*y1/3-(g*g+h2)*y2/2
    return small+large+correction,small+large,correction


def prediction(a,b,c,La,U,X):
    L=mp.log(2*mp.pi);z2=mp.zeta(0,derivative=2);z3=mp.zeta(0,derivative=3)
    z4=mp.zeta(0,derivative=4);y4=mp.zeta(-1,derivative=4)
    ans=a*b*c*c*La+4*c*(a**3+b**3-c*c*(a+b))*U+12*a*b*c*(a+b-2*c)*X
    ans-=2*(a*b*(a*a+b*b-4*c*c)+c**3*(a+b))*L*z3
    ans+=3*(2*a*a*b*b+c*c*(a*a+b*b-4*a*b))*z2*z2
    ans+=(-(a**4+b**4)/2+16*a*b*c*c-3*c*c*(a*a+b*b)-4*c**3*(a+b)-c**4)*z4
    ans+=(c**4-c*b**4/(a+c)-c*a**4/(b+c))*y4
    return ans


def main():
    p=argparse.ArgumentParser();p.add_argument('--numeric',action='store_true')
    p.add_argument('--output',default=str(Path(__file__).resolve().parents[1]/'results/latest/quartic_tornheim_checks.json'));args=p.parse_args()
    start=time.time();out={'exact':exact_checks()}
    print(json.dumps(out),flush=True)
    if args.numeric:
        mp.mp.dps=70;K=68;N=165;h=mp.mpf('0.000015')
        U,M3=u_coordinate();X,I,C=xi_coordinate(K,N)
        out['numeric']={'precision':mp.mp.dps,'Jonquiere_max_index':K,'incomplete_Gamma_max_sum':N,
                        'difference_step':str(h),'difference_nodes':list(range(-8,0))+list(range(1,9)),
                        'U':mp.nstr(U,60),'M3':mp.nstr(M3,60),'Xi':mp.nstr(X,60),
                        'Xi_integral':mp.nstr(I,60),'Xi_correction':mp.nstr(C,60),
                        'qualification':'Floating-point diagnostics; no interval certification.'}
        print(json.dumps(out['numeric']),flush=True)
        La=fourth_ray(mp.mpf(1),mp.mpf(1),mp.mpf(1),K,N,h)
        out['numeric']['Lambda']=mp.nstr(La,60)
        print('Lambda',mp.nstr(La,50),'elapsed',time.time()-start,flush=True)
        rows=[]
        for raw in [(1,2,3),(2,3,1),(1,-2,3)]:
            a,b,c=map(mp.mpf,raw)
            value=fourth_ray(a,b,c,K,N,h)
            predicted=prediction(a,b,c,La,U,X);err=abs(value-predicted)
            row={'slopes':raw,'direct_Mellin':mp.nstr(value,55),'prediction':mp.nstr(predicted,55),
                 'absolute_discrepancy':mp.nstr(err,10)}
            rows.append(row);print(json.dumps(row),'elapsed',time.time()-start,flush=True)
            assert err<mp.mpf('1e-30'),row
        out['numeric']['rays']=rows
    out['seconds']=time.time()-start
    Path(args.output).parent.mkdir(parents=True,exist_ok=True)
    Path(args.output).write_text(json.dumps(out,indent=2)+'\n')


if __name__=='__main__':main()
