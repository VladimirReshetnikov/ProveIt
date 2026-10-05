#!/usr/bin/env python3
"""Exact all-fixed-order asymptotics for A181199, using only the standard library.

The recurrence is a theorem of the accompanying manuscript, not inferred here.
Run: python -B asymptotic_certificate.py --order 6 --bounds
Output is stdout only; this module never writes files.
All coefficient checks and error constants use fractions.Fraction.  Decimal
output (if requested in a consumer) is not part of the certificate.
"""
from fractions import Fraction as F
from math import comb, factorial
import argparse
import json


def require(ok, why):
    if not ok:
        raise ArithmeticError(why)


def trim(p):
    p = list(map(F, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [F(0)]


def add(*ps):
    out = [F(0)] * max(map(len, ps))
    for p in ps:
        for i, x in enumerate(p):
            out[i] += x
    return trim(out)


def scale(p, a):
    return trim([F(a)*x for x in p])


def mul(*ps):
    out = [F(1)]
    for p in ps:
        q = [F(0)]*(len(out)+len(p)-1)
        for i, a in enumerate(out):
            for j, b in enumerate(p):
                q[i+j] += a*b
        out = trim(q)
    return out


def power(p, k):
    out = [F(1)]
    for _ in range(k):
        out = mul(out, p)
    return out


def val(p, x):
    out = F(0)
    for a in reversed(p):
        out = out*x+a
    return out


def coefficient(p, j):
    return p[j] if j < len(p) else F(0)


def series_fraction(p, q, order):
    require(q[0] != 0, 'series denominator vanishes at zero')
    out = []
    for j in range(order+1):
        out.append((coefficient(p,j)-sum(q[i]*out[j-i]
                    for i in range(1,min(j,len(q)-1)+1)))/q[0])
    return out


def shifted_coefficient(p, j):
    # [t^j] p(t/(1+t)); constant term is unchanged.
    if j == 0:
        return coefficient(p,0)
    return sum(p[i]*(-1)**(j-i)*comb(j-1,i-1)
               for i in range(1,min(j,len(p)-1)+1))


def product_coefficient(a,b,j):
    return sum(coefficient(a,i)*coefficient(b,j-i) for i in range(j+1))


P = [-90,-939,-1522,7383,23832,11208,-14496,9888,25216]
D = [306,2445,-1331,-33803,-40103,103814,247584,105456,-61744,109376,241280,100864]
T = [F(0),F(1)]
ONE_T = [F(1),F(1)]
FIVE = mul(*[[5,j] for j in range(1,5)])
# Each pair is the numerator and denominator of a rational function in t=1/n.
RHO = (power(ONE_T,4), scale(FIVE,5))
NU = (scale(power(ONE_T,2),-1), scale(mul([3,1],[3,2]),3))
DELTA = ([F(x) for x in [28,50,29,5]],scale(mul([2,1],[3,1],[3,2]),6))
ALPHA = (scale(mul(T,power(ONE_T,2),list(reversed(P))),2),
         scale(mul([2,-1],[2,1],[3,1],[3,2],[4,-1],[4,1],[4,3],FIVE),15))
ETA = (scale(mul(T,list(reversed(D))),-1),
       scale(mul(power([2,-1],2),power([2,1],2),[3,1],[3,2],[4,-1],[4,3],FIVE),120))


def coefficients(order):
    require(order >= 0, 'order must be nonnegative')
    degree = order+10
    rs, ns, ds, aa, ee = [series_fraction(*r,degree)
                          for r in [RHO,NU,DELTA,ALPHA,ETA]]
    z, b = [], []
    for j in range(degree+1):
        z.append((product_coefficient(ns,z,j)+ds[j]-shifted_coefficient(z,j))/(1-ns[0]))
        b.append((product_coefficient(rs,b,j)+product_coefficient(aa,z,j)
                  +ee[j]-shifted_coefficient(b,j))/(1-rs[0]))
    require(b[:10] == [0]*10, 'the first ten coefficients must vanish')
    require(b[10] == F(9,32768), 'incorrect leading coefficient')
    return z[:order+10],b


def shift_numerator(p):
    d = len(p)-1
    return add(*[scale(mul([0]*j+[1],power(ONE_T,d-j)),a)
                 for j,a in enumerate(p)]),power(ONE_T,d)


def residual_certificate(q, terms, forcing, exponent):
    """q(t/(1+t)) - sum(r(t)*p(t)) - forcing(t).

    Return P,H such that the residual equals t**exponent * P/H.
    No numerical interpolation or finite sample test is used.
    """
    sn,sd = shift_numerator(q)
    terms = list(terms)+[(forcing,[F(1)])]
    den = mul(sd,*[r[1] for r,p in terms])
    num = mul(sn,*[r[1] for r,p in terms])
    for i,(r,p) in enumerate(terms):
        num = add(num,scale(mul(r[0],p,sd,
                     *[s[1] for j,(s,_) in enumerate(terms) if j != i]),-1))
    require(all(coefficient(num,j)==0 for j in range(exponent)),
            'formal residual does not vanish at the claimed order')
    num = trim(num[exponent:])
    if den[0] < 0:
        num,den = scale(num,-1),scale(den,-1)
    require(den[0] > 0, 'nonpositive denominator at zero')
    return num,den


def rational_bound(pair,N):
    p,h = pair
    x=F(1,N)
    lower=h[0]-sum(abs(h[i])*x**i for i in range(1,len(h)))
    if lower <= 0:
        return None
    return sum(abs(v)*x**i for i,v in enumerate(p))/lower


def exact_state(N):
    z,b=F(1,3),F(1,120)
    for n in range(1,N):
        t=F(1,n)
        r,nu,delta,alpha,eta=[val(a,t)/val(d,t)
                             for a,d in [RHO,NU,DELTA,ALPHA,ETA]]
        b,z=r*b+alpha*z+eta,nu*z+delta
    return z,b


def error_bounds(order,z,b):
    pz,pb=order+10,order+11
    rz=residual_certificate(z,[(NU,z)],DELTA,pz)
    rb=residual_certificate(b,[(RHO,b),(ALPHA,z)],ETA,pb)
    # ALPHA/t is analytic; its numerator has an exact factor t.
    require(ALPHA[0][0]==0,'coupling must vanish at zero')
    coupling=(ALPHA[0][1:],ALPHA[1])
    N=2
    while True:
        cz,cb,A=[rational_bound(r,N) for r in [rz,rb,coupling]]
        theta_z,theta_b=F(N,N+1)**pz,F(N,N+1)**pb
        if all(c is not None for c in [cz,cb,A]) and theta_z>F(1,6) and theta_b>F(1,100):
            break
        N*=2
    zn,bn=exact_state(N)
    Ez=max(N**pz*abs(zn-val(z,F(1,N))),cz/(theta_z-F(1,6)))
    Ez=Ez if Ez else F(1)
    Eb=max(N**pb*abs(bn-val(b,F(1,N))),(cb+A*Ez)/(theta_b-F(1,100)))
    Eb=Eb if Eb else F(1)
    return dict(N=N,p_Z=pz,p_b=pb,C_Z=cz,C_b=cb,A=A,E_Z=Ez,E_b=Eb,
                residual_Z_numerator=rz[0],residual_Z_denominator=rz[1],
                residual_b_numerator=rb[0],residual_b_denominator=rb[1])


def bernoulli(m):
    out=[F(1)]
    for n in range(1,m+1):
        out.append(-sum(F(comb(n+1,k))*out[k] for k in range(n))/F(n+1))
    return out


def formal_log(unit,order):
    require(unit[0]==1,'log needs constant coefficient 1')
    # If A=exp L, n a_n = sum_{j=1}^n j L_j a_{n-j}.
    out=[F(0)]
    for n in range(1,order+1):
        out.append(coefficient(unit,n)-sum(F(j,n)*out[j]*coefficient(unit,n-j)
                                           for j in range(1,n)))
    return out


def formal_exp(logarithm,order):
    require(logarithm[0]==0,'exp needs constant coefficient 0')
    out=[F(1)]
    for n in range(1,order+1):
        out.append(sum(F(j,n)*coefficient(logarithm,j)*out[n-j]
                       for j in range(1,n+1)))
    return out


def restored_coefficients(order,b):
    rel=[x/b[10] for x in b[10:]]
    ell=formal_log(rel,order)
    B=bernoulli(order+2)
    for j in range(1,order+1,2):
        ell[j]+=B[j+1]/F((j+1)*j)*(F(1,5**j)-5)
    return rel,formal_exp(ell,order),ell


def log_error_bounds(order,b,bounds):
    """Exact C and onset for |log a_n - Psi_K(n)| <= C n^(-K-1)."""
    E=bounds['E_b']; c0=b[10]; N=bounds['N']; p=order+1
    rel=[x/c0 for x in b[10:]]
    u=[F(0)]+rel[1:]
    while True:
        U=sum(abs(coefficient(u,j))*F(1,N)**(j-1) for j in range(1,order+1))
        if U/N<=F(1,4) and (E/c0)*F(1,N)**p<=F(1,4):
            break
        N*=2
    LK=[F(0)]
    for h in range(1,order+1):
        LK=add(LK,scale(power(u,h),F((-1)**(h+1),h)))
    V=sum(abs(LK[j])*F(1,N)**(j-p) for j in range(p,len(LK)))
    Cb=2*E/c0+V+F(4,3*p)*U**p
    # Terms j=1,3,...,2L-1 do not exceed order.
    L=(order+1)//2; q=2*L+1; B=bernoulli(2*L+2)
    CM=abs(B[2*L+2])/F((2*L+2)*(2*L+1))*(F(1,5**q)+5)*F(N)**(p-q)
    return dict(N_log=N,C_log=Cb+CM,C_log_b=Cb,C_log_M=CM)



def inverse_coefficients(ell, order):
    """s_j as polynomials in q=1/log(3125), exact over Q[q]."""
    zero = [F(0)]
    def series_add(*xs):
        return [add(*[x[j] if j < len(x) else zero for x in xs])
                for j in range(order+1)]
    def series_scale(x,a):
        return [scale(c,a) for c in x]
    def series_mul(x,y):
        out=[zero]*(order+1)
        for i in range(min(len(x),order+1)):
            for j in range(min(len(y),order+1-i)):
                out[i+j]=add(out[i+j],mul(x[i],y[j]))
        return out
    def nonlinear(delta):
        x=[zero]+delta[:order]
        powers=[[[F(1)]]+[zero]*order]
        for _ in range(order):
            powers.append(series_mul(powers[-1],x))
        out=[zero]*(order+1)
        for h in range(1,order+1):
            out=series_add(out,series_scale(powers[h],F(-12*(-1)**(h+1),h)))
        for j in range(1,order+1):
            for h in range(order+1):
                shifted=[zero]*j+powers[h][:order+1-j]
                out=series_add(out,series_scale(shifted,
                    ell[j]*(-1)**h*comb(j+h-1,h)))
        return out
    delta=[zero]
    for j in range(1,order+1):
        residual=nonlinear(delta)[j]
        delta.append([F(0)]+scale(residual,-1))
    residual=nonlinear(delta)
    for j in range(1,order+1):
        require(delta[j][0]==0,'inverse coefficient not divisible by q')
        require(add(delta[j][1:],residual[j])==[0],
                'inverse formal residual failed')
    return [trim(a) for a in delta]


def verify():
    """No writes; deterministic, exact, JSON-serializable audit receipt."""
    # Independently check the simplified forcing against 2*rho*u and -alpha*gamma.
    uu=(scale(mul(T,list(reversed(P))),8),
        mul([2,-1],[4,-1],*[[3,j] for j in range(1,4)],
            *[[4,j] for j in range(1,5)]))
    gg=(mul([4,1],list(reversed(D))),
        scale(mul(power(ONE_T,2),[2,-1],[2,1],list(reversed(P))),16))
    require(mul(ALPHA[0],RHO[1],uu[1])==scale(mul(RHO[0],uu[0],ALPHA[1]),2),
            'alpha does not equal 2*rho*u')
    require(mul(ETA[0],ALPHA[1],gg[1])==scale(mul(ALPHA[0],gg[0],ETA[1]),-1),
            'eta does not equal -alpha*gamma')
    z,b=coefficients(6)
    gamma=series_fraction(*gg,9)
    require([z[j]-gamma[j] for j in range(10)]==[0]*9+[F(189783,1613824)],
            'leading gamma cancellation failed')
    rel,d,ell=restored_coefficients(6,b)
    require(rel==[F(1),F(10),F(225,4),F(1819,8),F(22045,32),F(1353),F(-6103,16)],
            'relative normalized coefficients differ')
    require(d==[F(1),F(48,5),F(5233,100),F(1028391,5000),F(60248377,100000),
                F(273939939,250000),F(-2709616559,3125000)],
            'count coefficients differ')
    require(ell[:5]==[0,F(48,5),F(25,4),F(-8889,5000),F(-335,8)],
            'log coefficients differ')
    inv=inverse_coefficients(ell,6)
    require(inv[1]==[0,F(-48,5)] and inv[2]==[0,F(-25,4),F(-576,5)],
            'first inverse coefficients differ')
    expected=[1,1,16,985,141696,36372976,14083834704,7372392431849]
    for n,a in enumerate(expected,1):
        _,bn=exact_state(n)
        require(bn*F(factorial(5*n),factorial(n)**5)==a,'exact-state initial value failed')
    certificates={}
    for K in [0,6]:
        zz,bb=coefficients(K)
        cert=error_bounds(K,zz,bb)
        logs=log_error_bounds(K,bb,cert)
        for n in [cert['N'],cert['N']+1,2*cert['N']]:
            zn,bn=exact_state(n)
            require(abs(zn-val(zz,F(1,n)))<=cert['E_Z']*F(1,n)**(K+10),
                    'finite Z error sanity check failed')
            require(abs(bn-val(bb,F(1,n)))<=cert['E_b']*F(1,n)**(K+11),
                    'finite b error sanity check failed')
        if K==0:
            require(logs['N_log']==512 and logs['C_log']<202,
                    'coarsened order-zero logarithmic bound failed')
        if K==6:
            require(cert['N']==64 and cert['E_b']<18,
                    'coarsened order-six normalized bound failed')
            require(logs['N_log']==64 and logs['C_log']<6100000,
                    'coarsened order-six logarithmic bound failed')
        certificates[str(K)]={key:cert[key] for key in ['N','p_Z','p_b','C_Z','C_b','A','E_Z','E_b']}
        certificates[str(K)].update(logs)
        certificates[str(K)]['residual_orders_verified']=[K+10,K+11]
    return serial(dict(status='passed',method='exact rational formal coefficients and residual induction',
        order=6,normalized_relative_coefficients=rel,count_relative_coefficients=d,
        count_log_coefficients=ell,inverse_polynomials_in_reciprocal_lambda=inv,
        rational_error_certificates=certificates,
        finite_sanity_checks='initial n=1..8 and residual bounds at N,N+1,2N'))


def serial(obj):
    if isinstance(obj,F): return str(obj)
    if isinstance(obj,list): return [serial(x) for x in obj]
    if isinstance(obj,dict): return {k:serial(v) for k,v in obj.items()}
    return obj


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--order',type=int,default=6)
    ap.add_argument('--bounds',action='store_true')
    args=ap.parse_args()
    z,b=coefficients(args.order)
    rel,d,ell=restored_coefficients(args.order,b)
    require(rel[:min(6,len(rel))]==[F(1),F(10),F(225,4),F(1819,8),F(22045,32),F(1353)][:len(rel)],
            'disagreement with the earlier fixed-height expansion')
    out=dict(order=args.order,Z_coefficients=z,b_coefficients=b,
             normalized_relative_coefficients=rel,count_relative_coefficients=d,
             count_log_coefficients=ell,
             inverse_polynomials_in_reciprocal_lambda=inverse_coefficients(ell,args.order))
    if args.bounds:
        bounds=error_bounds(args.order,z,b)
        out['error_certificate']=bounds
        out['log_error_certificate']=log_error_bounds(args.order,b,bounds)
    payload=json.dumps(serial(out),indent=2)+'\n'
    print(payload,end='')
    print('Verified exact coefficient recursion through order',args.order)


if __name__=='__main__':
    main()
