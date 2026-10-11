#!/usr/bin/env python3
"""Independent floating-point diagnostics. These are NOT interval certificates."""
from __future__ import annotations
import itertools,json,pathlib,functools
import mpmath as mp
import sympy as sp
from reductions import N,m,H,u,z,generating,endpoint,maximum_mass
ROOT=pathlib.Path(__file__).resolve().parents[1]
mp.mp.dps=100
records=[]
def test(name,lhs,rhs,tol,scale=None):
    err=abs(lhs-rhs)
    den=abs(rhs) if scale is None else abs(scale)
    den=max(den,mp.mpf('1e-90'))
    rel=err/den
    if rel>mp.mpf(tol):
        raise AssertionError((name,mp.nstr(rel,20),tol))
    records.append({'name':name,'absolute_error':mp.nstr(err,12),'scaled_error':mp.nstr(rel,12),'tolerance':tol})

def rational_mp(v):
    v=sp.Rational(v)
    return mp.mpf(int(v.p))/int(v.q)

@functools.lru_cache(None)
def mass_sequence(r,length):
    """Direct summation of lower moments, not the rational cutoff formulas."""
    moments=[mp.mpf(0)]*(2*r-1)
    w=1/mp.factorial(2*r-1)
    out=[]
    for n in range(length):
        if r==1:
            val=w
        elif n<r-1:
            val=mp.mpf(0)
        else:
            mat=mp.matrix([[n*n*moments[i+j]-2*n*moments[i+j+1]+moments[i+j+2]
                            for j in range(r-1)] for i in range(r-1)])
            val=w*mp.det(mat)
        out.append(val)
        for k in range(2*r-1):
            moments[k]+=w*n**k
        w*=mp.mpf(n+1)/(n+2*r)
    return out

def li_depth2(p,zz,length=800):
    h=mp.mpf(0); power=zz; total=mp.mpf(0)
    for n in range(1,length+1):
        total+=power*h/n**p
        h+=mp.mpf(1)/n;power*=zz
    return total

def eval_generating(r,q,zz):
    expr=generating(r,q)
    syms=sorted(expr.free_symbols-{z},key=str)
    vals=[mp.polylog(int(str(sy)[1:]),zz) if str(sy)[0]=='L'
           else li_depth2(int(str(sy)[1:]),zz) for sy in syms]
    fun=sp.lambdify([z]+syms,expr,modules='mpmath')
    return fun(zz,*vals)

for r in range(1,5):
    seq=mass_sequence(r,650)
    for zz in [mp.mpf('.2'),mp.mpf('.5'),mp.mpf('-.4'),mp.mpc('.2','.3')]:
        lhs=mp.fsum(v*zz**(n+1) for n,v in enumerate(seq))
        test(f'G r={r} z={zz}',lhs,eval_generating(r,0,zz),'1e-70')
    for q in [1,3]:
        zz=mp.mpf('.35')
        lhs=mp.fsum(v*zz**(n+1)/(n+1)**q for n,v in enumerate(seq))
        test(f'Euler primitive r={r} q={q}',lhs,eval_generating(r,q,zz),'1e-70')

# Direct moment sums in the ordinary convergence region; a,c nonintegral.
for r in range(1,5):
    for a,c in [(mp.mpf('.7'),mp.mpf('1.3')),(mp.mpf('1.2'),mp.mpf('2.4'))]:
        b=a+c+2*r-2+mp.mpf('30.5');d=b-a-c
        mom=[mp.mpf(0)]*(2*r-1);w=mp.mpf(1)
        for n in range(1500):
            for k in range(2*r-1):
                mom[k]+=n**k*w
            w*=((n+a)*(n+c))/((n+b)*(n+1))
        lhs=mp.det(mp.matrix([[mom[i+j] for j in range(r)] for i in range(r)]))
        rhs=mp.fprod(mp.factorial(j)*mp.gamma(a+j)*mp.gamma(c+j)*mp.gamma(d-r+1-j)/(mp.gamma(b-a-j)*mp.gamma(b-c-j)) for j in range(r))*(mp.gamma(b)/(mp.gamma(a)*mp.gamma(c)))**r
        test(f'Gauss product r={r} a={a} c={c}',lhs,rhs,'1e-28')

# Endpoint diagnostics: exact rational maximum-mass formula, independently summed
# with a large head and a Hurwitz-zeta tail from the Euler--Maclaurin expansion.
def rational_series_in_inverse(expr,order):
    t=sp.symbols('t')
    num,den=sp.fraction(sp.cancel(expr.subs(m,1/t)))
    pn,pd=sp.Poly(num,t),sp.Poly(den,t)
    # cancel() clears negative powers; denominator has nonzero constant here.
    if pd.nth(0)==0:
        raise ValueError('Unexpected inverse-power pole.')
    arr=[]
    for k in range(order+1):
        arr.append(sp.cancel((pn.nth(k)-sum(pd.nth(j)*arr[k-j] for j in range(1,k+1)))/pd.nth(0)))
    return arr

@functools.lru_cache(None)
def tail_data(r,q,order):
    expr=maximum_mass(r)/m**q
    aa=rational_series_in_inverse(sp.diff(expr,H),order)
    bb=rational_series_in_inverse(expr.subs(H,0),order)
    cc=bb[:]
    for k in range(order+1):
        if k>=1:cc[k]+=aa[k-1]/2
        for j in range(1,k//2+1):
            cc[k]-=aa[k-2*j]*sp.bernoulli(2*j)/(2*j)
    return aa,cc

for r in range(1,5):
    for q in range(1,4):
        head=400; order=30
        seq=mass_sequence(r,head)
        lhs=mp.fsum(v/(n+1)**q for n,v in enumerate(seq))
        aa,cc=tail_data(r,q,order)
        for p in range(2,order+1):
            A=rational_mp(aa[p]);C=rational_mp(cc[p])
            if A or C:
                lhs+=(C+A*mp.euler)*mp.zeta(p,head+1)-A*mp.zeta(p,head+1,derivative=1)
        rhs=sp.lambdify([],endpoint(r,q),'mpmath')()
        test(f'endpoint r={r} q={q}',lhs,rhs,'1e-32')

# Power-series arithmetic for finite-cutoff spectral derivatives.
def mul(a,b,K):
    return [sum(a[j]*b[k-j] for j in range(k+1)) for k in range(K+1)]
def expseries(log,K):
    out=[mp.exp(log[0])]+[mp.mpf(0)]*K
    for n in range(1,K+1):out[n]=sum(j*log[j]*out[n-j] for j in range(1,n+1))/n
    return out
def gammaseries(a,sgn,K):
    return expseries([mp.mpf(0)]+[sgn*mp.polygamma(k-1,a)/mp.factorial(k) for k in range(1,K+1)],K)

def determinant_series(mat,K):
    r=len(mat);ans=[mp.mpf(0)]*(K+1)
    for perm in itertools.permutations(range(r)):
        inv=sum(perm[i]>perm[j] for i in range(r) for j in range(i+1,r))
        v=[mp.mpf(1)]+[mp.mpf(0)]*K
        for i in range(r):v=mul(v,mat[i][perm[i]],K)
        for k in range(K+1):ans[k]+=(-1)**inv*v[k]
    return ans

@functools.lru_cache(None)
def rising_coeffs(k):
    nn=sp.symbols('nn');rem=nn**k;out=[sp.Integer(0)]*(k+1)
    for j in range(k,-1,-1):
        c=sp.expand(rem).coeff(nn,j);out[j]=c
        rem=sp.expand(rem-c*sp.rf(nn+1,j))
    assert rem==0
    return out

def finite_partition_jet(r,top,K):
    b=2*r
    R0=gammaseries(b-1,-1,K+1);RN=gammaseries(top+b,-1,K+1)
    Ts=[]
    for j in range(2*r-1):
        c0=mp.factorial(j)/mp.factorial(b-2)
        cN=mp.fprod(1/(top+ell) for ell in range(j+2,b))
        numer=[c0*R0[k]-cN*RN[k] for k in range(K+2)]
        gap=b-j-2
        if gap==0:
            arr=numer[1:K+2]
        else:
            arr=[]
            for k in range(K+1):arr.append((numer[k]-(arr[k-1] if k else 0))/gap)
        Ts.append(arr)
    moments=[]
    for k in range(2*r-1):
        co=rising_coeffs(k)
        moments.append([sum(int(co[j])*Ts[j][ell] for j in range(k+1)) for ell in range(K+1)])
    raw=determinant_series([[moments[i+j] for j in range(r)] for i in range(r)],K)
    norm=expseries([mp.mpf(0)]+[r*mp.polygamma(k-1,b)/mp.factorial(k) for k in range(1,K+1)],K)
    return mul(raw,norm,K)

def amplitude_jet(r,K):
    A0=mp.fprod(mp.factorial(j)**3*mp.gamma(r-j)/mp.gamma(2*r-1-j)**2 for j in range(r-1))
    logs=[mp.mpf(0)]
    for k in range(1,K+1):
        val=r*mp.polygamma(k-1,2*r)+sum(mp.polygamma(k-1,r-j)-2*mp.polygamma(k-1,2*r-1-j) for j in range(r-1))
        logs.append(val/mp.factorial(k))
    return [A0*v for v in expseries(logs,K)]

K=4;top=mp.mpf(10)**40
for r in range(1,5):
    finite=finite_partition_jet(r,top,K)
    A=amplitude_jet(r,K)
    E=expseries([mp.mpf(0)]+[(2*mp.polygamma(k-1,1)-3*mp.polygamma(k-1,r))/mp.factorial(k) for k in range(1,K+2)],K+1)
    for alpha in [mp.mpf('.5'),mp.mpf('1.3')]:
        gam=[mp.stieltjes(k,alpha) for k in range(K+1)]
        X=top+alpha+1;logX=mp.log(X)
        partial=[]
        for k in range(K+1):
            v=(-1)**k*gam[k]/mp.factorial(k)-(-logX)**(k+1)/mp.factorial(k+1)-(-logX)**k/(2*X*mp.factorial(k))
            v-=((-logX)**k/mp.factorial(k)+( (-logX)**(k-1)/mp.factorial(k-1) if k else 0))/(12*X**2)
            partial.append(v)
        sub=mul(A,partial,K)
        predicted=mul(A,[E[k+1]-(-1)**k*gam[k]/mp.factorial(k) for k in range(K+1)],K)
        for k in range(K+1):
            test(f'Stieltjes jet r={r} k={k} alpha={alpha}',finite[k]-sub[k],predicted[k],'1e-27',scale=A[0])

# Explicit half-point dilogarithm evaluation, independently by the original masses.
seq=mass_sequence(2,650)
lhs=mp.fsum(v*mp.mpf('.5')**(n+1) for n,v in enumerate(seq))
rhs=mp.log(2)**2/2+7*mp.log(2)/2-mp.pi**2/24-mp.mpf(9)/4
test('two-particle half-point',lhs,rhs,'1e-70')

out={'status':'PASS','numerical_diagnostics':len(records),'working_decimal_digits':mp.mp.dps,
     'interval_certified':False,'mpmath_version':mp.__version__,
     'scope':'Independent finite sums, convergent polylog series, asymptotic endpoint diagnostics, and finite-cutoff spectral jets. Not interval proofs.',
     'records':records}
(ROOT/'results'/'numerical_checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
print('largest scaled error:',max(mp.mpf(v['scaled_error']) for v in records))
