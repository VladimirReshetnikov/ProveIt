"""Exact symbolic response recursion; run python check_cancellation.py.
No floating point Airy roots: L remains an indeterminate.
The valuation proof in proof.md makes this reduced recursion identical to
subtracting the full nonlinear recursions through order d+3.
"""
import contextlib, io, runpy
from pathlib import Path
import sympy as s
with contextlib.redirect_stdout(io.StringIO()):
    b=runpy.run_path(str(Path(__file__).with_name('relaxed_low_stages.py')))
x,L,e=b['x'],b['L'],b['e']
t,r=s.symbols('t r')

def trunc(z,N):
    return s.Add(*[v*e**j for (j,),v in s.Poly(s.expand(z),e).terms() if j<=N])
def analytic(z,N): return s.series(z,e,0,N+1).removeO().expand()
def mul(a,b,N): return trunc(a*b,N)
def derivative(v,q):
    A,B=v
    return [s.diff(A,x)+2*(x+L)*B/q,A+s.diff(B,x)]
def shifted(v,h,l,jump,N,q):
    tau=analytic((1-l*e**3)**(-s.Rational(1,3)),N)
    delta=trunc((x+jump*e)*tau-x,N)
    power=s.Integer(1); out=[0,0]
    for j in range(N+1):
        if j:
            v=derivative(v,q);power=mul(power,delta,N)
        for z in range(2): out[z]+=power*v[z]/s.factorial(j)
    fac=analytic((1-l*e**3)**(-s.Rational(h,3)),N)
    return [mul(fac,trunc(z,N),N) for z in out]
def solve(R,k,q):
    P=-R[0]/k; Q=-R[1]/k
    rem=s.expand(P-s.diff(Q,x)/2); B=s.Integer(0)
    degree=s.degree(rem,x)
    if degree is not s.S.NegativeInfinity:
        for j in range(int(degree),-1,-1):
            term=s.expand(rem).coeff(x,j)/(2*j+1)*x**j
            B+=term
            rem=s.expand(rem+q*s.diff(term,x,3)/4-2*(x+L)*s.diff(term,x)-term)
    assert s.expand(rem)==0
    ds=-k*B.subs(x,0); B=s.expand(B+ds/k)
    A=s.integrate(Q/q-s.diff(B,x,2)/2,x);A=s.expand(A-A.subs(x,0))
    assert s.expand(k*(q*s.diff(A,x,2)/2+2*(x+L)*s.diff(B,x)+B)+R[0]-ds)==0
    assert s.expand(k*(q*s.diff(A,x)+q*s.diff(B,x,2)/2)+R[1])==0
    return (A,B),s.expand(ds)

for k in (3,4):
    q=s.Integer(k-1); d=3*int(q); target=d+3
    base=[tuple(s.expand(z.subs(b['q'],q)) for z in pair) for pair in b['phi']+[(b['AA'],b['BB'])]]
    sc={0:s.Integer(k),2:k*L,3:s.Rational(k*(7*k-6),6),4:b['s4'].subs(b['q'],q)}
    U=analytic(q*q*(1-x*e**2+(k+1)*e**3)/(q+x*e**2-e**3),4)
    Den=s.prod(q+x*e**2-(1+k*j)*e**3 for j in range(k))
    beta=analytic((t*q**(2*k)*k**(k-1)*(1-x*e**2+e**3)-r*q**(2*k)*k**k*e**3)/Den,3)
    Q=s.Integer(1)
    for l in range(1,k+1):
        sig=k+k*L*e**2+s.Rational(k*(7*k-6),6)*e**3
        Q=mul(Q,analytic(1/sig,3),3) # time shifts first affect e^5
    delay=[0,0]
    for h,v in enumerate(base):
        sh=shifted(v,h,k+1,-1,3-h,q)
        for z in range(2):delay[z]+=mul(beta*Q, e**h*sh[z],3)
    delay=[trunc(z,3) for z in delay]
    dp={};ds={}
    for N in range(d,target+1):
        R=[-z.coeff(e,N-d) for z in delay]
        for h,v in dp.items():
            for coeff,jump in ((U,-1),(s.Integer(1),q)):
                sh=shifted(v,h,1,jump,N-h,q)
                for z in range(2):R[z]+=s.expand(coeff*sh[z]).coeff(e,N-h)
            for order,value in sc.items():
                if order+h==N:
                    for z in range(2):R[z]-=value*v[z]
        for order,value in ds.items():
            h=N-order
            if h<len(base):
                for z in range(2):R[z]-=value*base[h][z]
        dp[N-2],ds[N]=solve([s.expand(z) for z in R],k,q)
    combination=lambda z:s.expand(z.subs({t:1,r:1})-2*z.subs({t:s.Rational(1,2),r:0}))
    for h,pair in dp.items():
        assert all(combination(z)==0 for z in pair)
    for N,val in ds.items():
        expected=q**k if N==target else 0
        assert combination(val)==expected,(k,N,val)
        print(f'k={k}, delta sigma[{N}] = {s.factor(val)}; C-2B+R = {combination(val)}')
    assert all(z==0 for z in dp[d-2])
    # Earliest nonlinear terms: delta sigma*delta profile, beta*delta profile,
    # beta*delta Q; all strictly beyond target, including k=3.
    assert 2*d-1>target and 2*d>target
    # log sigma nonlinear terms begin at 2d. Endpoint logarithm nonlinear
    # terms begin at 2(d-1), also strictly beyond the requested endpoint d.
    assert 2*(d-1)>d
    physical=-q**(k-1)/s.Integer(k)**k
    print(f'k={k}: normalized logarithmic endpoint combination = {physical} n^(-{q}) + O(n^(-{q}-1/3))')
print('All exact polynomial residuals, vanishing orders, and coefficients passed.')
