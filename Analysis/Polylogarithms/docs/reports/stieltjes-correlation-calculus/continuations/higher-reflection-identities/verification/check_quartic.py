"""Quartic Tornheim layer: exact algebra and independent Mellin diagnostics.

All decimal diagnostics use mpmath; they are not interval certificates.
"""
from pathlib import Path
import json
import time
import mpmath as mp
import sympy as sp

K_MELLIN=48
N_MELLIN=118

def tornheim(a,b,c):
    """Direct Mellin continuation, adapted from incoming check_cubic_rays.py."""
    ga,gb=mp.gamma(1-a),mp.gamma(1-b)
    za=[(-1)**k*mp.zeta(a-k)/mp.factorial(k) for k in range(K_MELLIN+1)]
    zb=[(-1)**k*mp.zeta(b-k)/mp.factorial(k) for k in range(K_MELLIN+1)]
    terms=[ga*gb/(a+b+c-2)]
    terms.extend(ga*zb[k]/(a+c-1+k) for k in range(K_MELLIN+1))
    terms.extend(gb*za[k]/(b+c-1+k) for k in range(K_MELLIN+1))
    terms.extend(za[j]*zb[k]/(c+j+k) for j in range(K_MELLIN+1) for k in range(K_MELLIN+1))
    head=[mp.power(j,-a) for j in range(1,N_MELLIN)]
    other=[mp.power(j,-b) for j in range(1,N_MELLIN)]
    large=mp.fsum(mp.gammainc(c,k,mp.inf)/mp.power(k,c)*mp.fsum(head[j-1]*other[k-j-1] for j in range(1,k)) for k in range(2,N_MELLIN+1))
    return (mp.fsum(terms)+large)/mp.gamma(c)

def exact_algebra():
    a,b,c=sp.symbols('a b c')
    L,z2,z3,z4,y4,Om,al,be=sp.symbols('L z2 z3 z4 y4 Om alpha beta')
    de=(z2*z2-z4)/4
    ph=(-L*z3/2-z4-al)/3
    ch=(y4-z4)/4
    ep=(Om+8*L*z3-12*z2*z2+16*z4)/24-be
    direct=-(a**4+b**4)*z4/2-2*L*z3*a*b*(a*a+b*b)+6*z2*z2*a*a*b*b
    direct-=c*(b**4/(a+c)+a**4/(b+c))*y4
    direct+=4*c*al*(a**3+b**3)+12*c*be*a*b*(a+b)+12*c*c*de*(a*a+b*b)
    direct+=24*a*b*c*c*ep+12*c**3*ph*(a+b)+4*c**4*ch
    pred=a*b*c*c*Om+4*c*(a+b)*(a*a-a*b+b*b-c*c)*al+12*a*b*c*(a+b-2*c)*be
    pred-=2*(a*b*(a*a+b*b)-4*a*b*c*c+c**3*(a+b))*L*z3
    pred+=3*(2*a*a*b*b+c*c*(a*a+b*b-4*a*b))*z2*z2
    pred+=(-(a**4+b**4)/2-3*c*c*(a*a+b*b)+16*a*b*c*c-4*c**3*(a+b)-c**4)*z4
    pred+=(c**4-c*b**4/(a+c)-c*a**4/(b+c))*y4
    assert sp.cancel(direct-pred)==0
    cyc=sp.cancel(sum(pred.xreplace(dict(zip((a,b,c),v))) for v in ((a,b,c),(b,c,a),(c,a,b))))
    e1=a+b+c;e2=a*b+a*c+b*c;e3=a*b*c
    sym=e1*e3*Om+(-4*e1*e1*e2+8*e2*e2+12*e1*e3)*L*z3
    sym+=(12*e2*e2-36*e1*e3)*z2*z2
    sym+=(-2*e1**4+4*e1*e1*e2-2*e2*e2+24*e1*e3)*z4
    assert sp.cancel(cyc-sym)==0
    assert sp.simplify(pred.subs({a:1,b:1,c:1})-Om)==0
    euler=sp.diff(((-sp.Rational(1,2)+sp.Symbol('t')*(-L/2)+sp.Symbol('t')**2*z2/2+sp.Symbol('t')**3*z3/6+sp.Symbol('t')**4*z4/24)**2-(-sp.Rational(1,2)+2*sp.Symbol('t')*(-L/2)+(2*sp.Symbol('t'))**2*z2/2+(2*sp.Symbol('t'))**3*z3/6+(2*sp.Symbol('t'))**4*z4/24))/2,sp.Symbol('t'),4).subs(sp.Symbol('t'),0)
    assert sp.simplify(pred.subs({a:1,b:0,c:1})-euler)==0
    A,B,C,g,Z2,Z3,z1,Y1,Y2=sp.symbols('A B C g Z2 Z3 z1 Y1 Y2')
    mu2=g*g+Z2;mu3=g**3+3*g*Z2+2*Z3
    GA=1+g*A+mu2*A*A/2+mu3*A**3/6
    GB=1+g*B+mu2*B*B/2+mu3*B**3/6
    gc=1+g*C+(g*g-Z2)*C*C/2+(g**3-3*g*Z2+2*Z3)*C**3/6
    za=-sp.Rational(1,2)+z1*A+z2*A*A/2
    zb=-sp.Rational(1,2)+z1*B+z2*B*B/2
    ya=-sp.Rational(1,12)+Y1*A+Y2*A*A/2
    yb=-sp.Rational(1,12)+Y1*B+Y2*B*B/2
    X=GA*GB/(A+B+C-2)+GA*zb/(A+C-1)+GB*za/(B+C-1)
    X0=X.subs(C,0)
    Q0A=g+mu2*A/2+mu3*A*A/6
    Q0B=g+mu2*B/2+mu3*B*B/6
    E0=X0+g*za*zb-Q0A*yb-Q0B*ya
    E21=sp.diff(E0,A,2,B,1).subs({A:0,B:0})
    expected21=g*z1*z2-(mu2+2*g+2)*z1-(g+1)*z2-mu3*Y1/3-mu2*Y2/2
    expected21-=sp.Rational(3,8)+3*g/4+mu2/4+g*g/2+g*mu2/2
    assert sp.simplify(E21-expected21)==0
    qac=(g**3-Z3)/3
    E111=sp.diff(X,A,B,C).subs({A:0,B:0,C:0})+g*sp.diff(X,A,B).subs({A:0,B:0,C:0})
    E111+=(g*g-Z2)*z1*z1/2-2*qac*Y1
    expected111=-g**3/2-3*g*g/4-3*g/4-sp.Rational(3,8)-2*(g*g+2*g+2)*z1+(g*g-Z2)*z1*z1/2-2*(g**3-Z3)*Y1/3
    assert sp.simplify(E111-expected111)==0
    for n in range(1,31):
        qdim=sum(1 for i in range(n-2) for j in range(i+1) for k in [n-3-i-j] if k>=0) if n>=3 else 0
        vdim=(n-1)//2 if n>=3 else 0
        assert qdim+vdim==(n*n-1)//4
        if n>=3:
            symdim=sum(1 for i in range(n-2) for j in range((n-3-i)//2+1) if (n-3-i-2*j)%3==0)
            assert symdim==(n*n+3)//12
    u5=A*B*C*((A+B+C)**2-3*(A*B+B*C+C*A))
    assert sp.expand(u5.subs({A:sp.Symbol('t'),B:sp.Symbol('t'),C:sp.Symbol('t')}))==0
    assert u5.subs(B,0)==0
    assert u5.subs({A:1,B:2,C:3})!=0
    return {'quartic_ray_formula':True,'cyclic_identity':True,'diagonal_identity':True,'Euler_diagonal':True,'beta_elementary_part':True,'epsilon_elementary_part':True,'formal_dimension':3,'dimension_counts_through_order':30,'fifth_order_obstruction':True}

def gamma_alpha(ncut=32,order=20):
    L=mp.log(2*mp.pi)
    def rho(n):
        n=mp.mpf(n)
        return mp.loggamma(n+1)-(n+mp.mpf('.5'))*mp.log(n)+n-L/2-1/(12*n)
    m3=mp.fsum(mp.log(n)**3*rho(n) for n in range(1,ncut))
    m3-=mp.fsum(mp.bernpoly(2*j,0)/(2*j*(2*j-1))*mp.zeta(2*j-1,ncut,derivative=3) for j in range(2,order+1))
    al=-m3-mp.zeta(-1,derivative=4)-mp.zeta(0,derivative=4)/2-mp.zeta(-1,derivative=3)-mp.stieltjes(3)/12
    return al,m3

def integral_coordinates(K=45,N=105):
    g=mp.euler;Z2=mp.zeta(2);Z3=mp.zeta(3)
    z1=mp.zeta(0,derivative=1);z2=mp.zeta(0,derivative=2)
    y1=mp.zeta(-1,derivative=1);y2=mp.zeta(-1,derivative=2)
    mu2=g*g+Z2;mu3=g**3+3*g*Z2+2*Z3
    d1=[(-1)**k*mp.zeta(-k,derivative=1)/mp.factorial(k) for k in range(K+1)]
    d2=[(-1)**k*mp.zeta(-k,derivative=2)/mp.factorial(k) for k in range(K+1)]
    small21=mp.fsum(d1[k]*(mu2/(k-1)-2*g/(k-1)**2+mp.mpf(2)/(k-1)**3)+d2[k]*(g/(k-1)-mp.mpf(1)/(k-1)**2) for k in range(2,K+1))
    small21+=mp.fsum(d2[j]*d1[k]/(j+k) for j in range(K+1) for k in range(K+1) if j+k)
    large21=-mp.fsum(mp.e1(k)*mp.fsum(mp.log(m)**2*mp.log(k-m) for m in range(1,k)) for k in range(2,N+1))
    E21=g*z1*z2-(mu2+2*g+2)*z1-(g+1)*z2-mu3*y1/3-mu2*y2/2
    E21-=mp.mpf(3)/8+3*g/4+mu2/4+g*g/2+g*mu2/2
    beta=small21+large21+E21
    # Integral of (log x + gamma) times the subtracted F1^2 kernel.
    small11=2*mp.fsum(d1[k]*(g*g/(k-1)-2*g/(k-1)**2+mp.mpf(2)/(k-1)**3) for k in range(2,K+1))
    small11+=mp.fsum(d1[j]*d1[k]*(g/(j+k)-mp.mpf(1)/(j+k)**2) for j in range(K+1) for k in range(K+1) if j+k)
    large11=mp.fsum((mp.diff(lambda s:mp.gammainc(s,k,mp.inf)*mp.power(k,-s),0)+g*mp.e1(k))*mp.fsum(mp.log(m)*mp.log(k-m) for m in range(1,k)) for k in range(2,N+1))
    E111=-g**3/2-3*g*g/4-3*g/4-mp.mpf(3)/8-2*(g*g+2*g+2)*z1+(g*g-Z2)*z1*z1/2-2*(g**3-Z3)*y1/3
    epsilon=small11+large11+E111
    omega=24*(beta+epsilon)-8*mp.log(2*mp.pi)*mp.zeta(0,derivative=3)+12*z2*z2-16*mp.zeta(0,derivative=4)
    return beta,epsilon,omega,{'J21':small21+large21,'K11':small11+large11,'beta_elementary':E21,'epsilon_elementary':E111}

def prediction(a,b,c,omega,alpha,beta):
    a,b,c=map(mp.mpf,(a,b,c))
    L=mp.log(2*mp.pi);z2=mp.zeta(0,derivative=2);z3=mp.zeta(0,derivative=3);z4=mp.zeta(0,derivative=4);y4=mp.zeta(-1,derivative=4)
    pred=a*b*c*c*omega+4*c*(a+b)*(a*a-a*b+b*b-c*c)*alpha+12*a*b*c*(a+b-2*c)*beta
    pred-=2*(a*b*(a*a+b*b)-4*a*b*c*c+c**3*(a+b))*L*z3
    pred+=3*(2*a*a*b*b+c*c*(a*a+b*b-4*a*b))*z2*z2
    pred+=(-(a**4+b**4)/2-3*c*c*(a*a+b*b)+16*a*b*c*c-4*c**3*(a+b)-c**4)*z4
    pred+=(c**4-c*b**4/(a+c)-c*a**4/(b+c))*y4
    return pred

def fourth_ray(a,b,c,h=None):
    a,b,c=map(mp.mpf,(a,b,c))
    if h is None:h=mp.mpf('0.00005')
    nodes=list(range(-7,8))
    weights=sp.finite_diff_weights(4,nodes,0)[-1][-1]
    zero=mp.mpf(1)/4+c/12*(1/(a+c)+1/(b+c))
    vals=[]
    for n,w in zip(nodes,weights):
        if not w:continue
        v=zero if not n else tornheim(a*n*h,b*n*h,c*n*h)
        vals.append(mp.mpf(int(w.p))/int(w.q)*v)
    return mp.fsum(vals)/h**4

def main():
    start=time.time();mp.mp.dps=55
    out={'exact':exact_algebra(),'precision':mp.mp.dps,'qualification':'mpmath diagnostics, not interval certificates'}
    print(json.dumps(out),flush=True)
    alpha,m3=gamma_alpha()
    beta,eps,omega,parts=integral_coordinates()
    vals={'alpha':alpha,'beta':beta,'epsilon':eps,'omega4':omega,'M3':m3,**parts}
    out['coordinates']={k:mp.nstr(v,48) for k,v in vals.items()}
    print(json.dumps(out['coordinates']),flush=True)
    out['checks']=[]
    for slopes in [(1,1,1),(1,0,2),(1,2,2),(1,-2,3)]:
        direct=fourth_ray(*slopes)
        pred=prediction(*slopes,omega,alpha,beta)
        err=abs(direct-pred)
        row={'slopes':slopes,'direct_mellin':mp.nstr(direct,45),'prediction':mp.nstr(pred,45),'error':mp.nstr(err,6)}
        out['checks'].append(row)
        print(json.dumps(row),'seconds',round(time.time()-start,1),flush=True)
        assert err<mp.mpf('1e-24'), row
    out['seconds']=time.time()-start
    (Path(__file__).with_name('quartic_checks.json')).write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
