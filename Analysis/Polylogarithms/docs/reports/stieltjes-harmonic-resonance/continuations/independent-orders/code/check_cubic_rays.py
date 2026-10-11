"""Cubic Tornheim ray diagnostics; all values use mpmath, not interval arithmetic.

The prediction follows the new exact holomorphic-remainder classification.
The independent evaluator integrates Jonquiere series and an incomplete-Gamma
series; it does not use the classified cubic polynomial.
"""
import json
from pathlib import Path
import time
import mpmath as mp
import sympy as sp

mp.mp.dps = 65
K = 62
N = 155
STEP = mp.mpf("0.00002")


def tornheim(a, b, c):
    ga, gb = mp.gamma(1-a), mp.gamma(1-b)
    za = [(-1)**k*mp.zeta(a-k)/mp.factorial(k) for k in range(K+1)]
    zb = [(-1)**k*mp.zeta(b-k)/mp.factorial(k) for k in range(K+1)]
    terms = [ga*gb/(a+b+c-2)]
    terms.extend(ga*zb[k]/(a+c-1+k) for k in range(K+1))
    terms.extend(gb*za[k]/(b+c-1+k) for k in range(K+1))
    terms.extend(za[j]*zb[k]/(c+j+k) for j in range(K+1)
                 for k in range(K+1))
    small = mp.fsum(terms)
    head = [mp.power(j, -a) for j in range(1,N)]
    other = [mp.power(j, -b) for j in range(1,N)]
    large = mp.fsum(
        mp.gammainc(c,k,mp.inf)/mp.power(k,c)
        * mp.fsum(head[j-1]*other[k-j-1] for j in range(1,k))
        for k in range(2,N+1)
    )
    return (small+large)/mp.gamma(c)


def gamma_coordinate(ncut=40, order=24):
    L = mp.log(2*mp.pi)
    def rem(n):
        n = mp.mpf(n)
        return mp.loggamma(n+1)-(n+mp.mpf('0.5'))*mp.log(n)+n-L/2-1/(12*n)
    direct = mp.fsum(mp.log(n)**2 * rem(n) for n in range(1,ncut))
    tail = mp.fsum(mp.bernpoly(2*j,0)/(2*j*(2*j-1))*mp.zeta(2*j-1,ncut,derivative=2)
                   for j in range(2,order+1))
    bound = abs(mp.bernpoly(2*order+2,0))/((2*order+2)*(2*order+1))*mp.zeta(2*order+1,ncut,derivative=2)
    D = direct+tail
    kap = D-mp.zeta(-1,derivative=3)-mp.zeta(0,derivative=3)/2-mp.zeta(-1,derivative=2)+mp.stieltjes(2)/12
    return kap,D,bound


def prediction(a,b,c,omega,kappa):
    L=mp.log(2*mp.pi);z2=mp.zeta(0,derivative=2);z3=mp.zeta(0,derivative=3);y3=mp.zeta(-1,derivative=3)
    ans=a*b*c*omega+3*c*(a*a+b*b-c*(a+b))*kappa
    ans-=mp.mpf('1.5')*(a*b*(a+b-4*c)+c*c*(a+b))*L*z2
    ans+=(-(a**3+b**3)/2+8*a*b*c-3*c*c*(a+b)-c**3)*z3
    ans+=(c**3-c*b**3/(a+c)-c*a**3/(b+c))*y3
    return ans


def third_ray(a,b,c,h=STEP):
    nodes=list(range(-7,8))
    weights=sp.finite_diff_weights(3,nodes,0)[-1][-1]
    out=[]
    for n,w in zip(nodes,weights):
        if w:
            v=tornheim(a*n*h,b*n*h,c*n*h)
            out.append(mp.mpf(int(w.p))/int(w.q)*v)
    return mp.fsum(out)/h**3


def exact_algebra():
    a,b,c=sp.symbols('a b c');z2,z3,y3,L,Om,kap=sp.symbols('z2 z3 y3 L Om kap')
    r=(-L*z2/2-z3-kap)/2
    q=(Om+6*L*z2+8*z3)/6
    s=(y3-z3)/3
    direct=-(a**3+b**3)*z3/2-sp.Rational(3,2)*a*b*(a+b)*L*z2
    direct-=c*(b**3/(a+c)+a**3/(b+c))*y3
    direct+=3*c*kap*(a*a+b*b)+6*c*q*a*b+6*c*c*r*(a+b)+3*c**3*s
    expected=a*b*c*Om+3*c*(a*a+b*b-c*(a+b))*kap
    expected-=sp.Rational(3,2)*(a*b*(a+b-4*c)+c*c*(a+b))*L*z2
    expected+=(-(a**3+b**3)/2+8*a*b*c-3*c*c*(a+b)-c**3)*z3
    expected+=(c**3-c*b**3/(a+c)-c*a**3/(b+c))*y3
    assert sp.cancel(direct-expected)==0
    cyclic=sp.cancel(sum(expected.xreplace(dict(zip((a,b,c),v))) for v in ((a,b,c),(b,c,a),(c,a,b))))
    e1=a+b+c;e2=a*b+a*c+b*c;e3=a*b*c
    symmetric=3*e3*Om+3*(9*e3-e1*e2)*L*z2+(-2*e1**3+3*e1*e2+27*e3)*z3
    assert sp.cancel(cyclic-symmetric)==0
    assert sp.simplify(expected.subs({a:1,b:1,c:1})-Om)==0
    assert sp.simplify(expected.subs({a:1,b:0,c:1})+sp.Rational(3,2)*L*z2+sp.Rational(9,2)*z3)==0
    return {'classification_identity':True,'cyclic_identity':True,'diagonal':True,'Euler_diagonal':True}


def main():
    start=time.time();out={'algebra':exact_algebra(),'precision':mp.mp.dps,'qualification':'Floating-point diagnostics, not interval-certified final digits','jonquiere_max_index':K,'incomplete_gamma_max_sum':N,'finite_difference_step':str(STEP),'finite_difference_nodes':list(range(-7,8)),'stirling_start':40,'stirling_order':24}
    kap,D,bound=gamma_coordinate()
    out['kappa']=mp.nstr(kap,55);out['log_gamma_series']=mp.nstr(D,55);out['analytic_stirling_tail_bound']=mp.nstr(bound,6)
    print(json.dumps(out),flush=True)
    omega=third_ray(mp.mpf(1),mp.mpf(1),mp.mpf(1))
    out['omega_cubic_from_mellin']=mp.nstr(omega,55)
    print('omega',mp.nstr(omega,50),'elapsed',round(time.time()-start,1),flush=True)
    records=[]
    for raw in [(1,2,3),(2,3,1),(1,-2,3)]:
        a,b,c=map(mp.mpf,raw)
        numeric=third_ray(a,b,c)
        exact=prediction(a,b,c,omega,kap)
        error=abs(numeric-exact)
        row={'slopes':raw,'prediction':mp.nstr(exact,50),'independent_Mellin':mp.nstr(numeric,50),'absolute_discrepancy':mp.nstr(error,6)}
        records.append(row);print(json.dumps(row),'elapsed',round(time.time()-start,1),flush=True)
        assert error<mp.mpf('1e-35')
    out['records']=records
    out['seconds']=time.time()-start
    (Path(__file__).resolve().parents[1]/'results'/'cubic_rays.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':
    main()
