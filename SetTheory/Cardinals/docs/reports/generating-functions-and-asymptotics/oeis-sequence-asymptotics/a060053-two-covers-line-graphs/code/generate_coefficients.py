#!/usr/bin/env python3
"""Exact finite-order Lambert coefficient generator, using rational arithmetic.

No infinite Stirling series is evaluated. Each target order fixes a finite
Stirling truncation and finite collision expansion. Formal symbols satisfy
h=exp(-r/2), n=r/(2h^2), x=1+h*y; the final coefficient of h^(2j)
is multiplied by (r/2)^j to give the coefficient of n^(-j).
"""
import argparse, json, pathlib
import sympy as S
r,h,t,x,y,z=S.symbols('r h t x y z')

def trunc(f,var,order):
    return S.series(f,var,0,order+1).removeO().expand()

def gaussian(f):
    p=S.Poly(S.expand(f),y)
    return S.factor(sum(c*S.factorial2(k-1)/(r+1)**(k//2) for (k,),c in p.terms() if k%2==0))

def common_exponent(J,collisions=True):
    N=2*J
    # Main Bell saddle phase, with its exact quadratic part removed.
    saddle=trunc(((r-(1+h*y))*S.log(1+h*y)+(1-r)*h*y)/h**2+(r+1)*y**2/2,h,N)
    stirling=0
    for k in range(1,J+2):
        power=4*k-2
        if power<=N:
            stirling-=S.bernoulli(2*k)*h**power*trunc((1+h*y)**(-(2*k-1)),h,N-power)/(2*k*(2*k-1))
    E=saddle-S.Rational(1,2)*trunc(S.log(1+h*y),h,N)+stirling
    if collisions:
        n=r/(2*t)
        D= -sum(r*t**(q-1)/(2*q*x**q) for q in range(1,J+2))
        # Faulhaber: sum j^p for 0 <= j < n.
        for p in range(1,J+2):
            Sp=(S.bernoulli(p+1,n)-S.bernoulli(p+1))/(p+1)
            D-=trunc(Sp*2**p*t**(2*p)*x**(-2*p)*(1-t/x)**(-p)/p,t,J)
        D=trunc(D,t,J)
        for (power,),coef in S.Poly(D,t).terms():
            E+=h**(2*power)*trunc(coef.subs(x,1+h*y),h,N-2*power)
        E+=r/2+r*r/4
    E=S.Poly(S.expand(E),h)
    return [S.expand(E.coeff_monomial(h**k)) for k in range(N+1)]

def exp_coefficients(e):
    if e[0] != 0:
        raise ArithmeticError("exponent constant must vanish")
    out=[S.Integer(1)]
    for n in range(1,len(e)):
        out.append(S.expand(sum(k*e[k]*out[n-k] for k in range(1,n+1))/n))
    return out

def multiplier(J, P):
    N=2*J
    cs=[trunc(S.exp(P),z,J).coeff(z,k) for k in range(J+1)]
    q=S.Integer(1)
    # Each k begins at h^(2k), so only k <= J is needed.
    for k in range(1,J+1):
        num=S.prod(r/2-i*t for i in range(k))
        den=S.prod(x*x/2-(x+r)*t/2+(i+1)*t*t for i in range(k))
        term=cs[k]*t**k*trunc(num/den,t,J-k)
        for (power,),coef in S.Poly(S.expand(term),t).terms():
            q+=h**(2*power)*trunc(coef.subs(x,1+h*y),h,N-2*power)
    q=S.Poly(S.expand(q),h)
    return [S.expand(q.coeff_monomial(h**k)) for k in range(N+1)]

def coefficients(J,P,collisions=True, e=None):
    if e is None:
        e=exp_coefficients(common_exponent(J,collisions))
    q=multiplier(J,P)
    vals=[]
    for j in range(J+1):
        vals.append(S.factor((r/2)**j*gaussian(sum(e[k]*q[2*j-k] for k in range(2*j+1)))))
    return vals

def quotient(a,b):
    out=[]
    for j in range(len(a)):
        out.append(S.factor(a[j]-sum(b[k]*out[j-k] for k in range(1,j+1))))
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--order',type=int,default=2);ap.add_argument('--out',default='coefficients.json');args=ap.parse_args()
    J=args.order
    if not 0 <= J <= 3:
        ap.error("supported symbolic order is 0 through 3")
    target=pathlib.Path(args.out)
    if target.exists():
        ap.error("output must not already exist")
    e=exp_coefficients(common_exponent(J))
    ps={'H':0,'V':-z/2,'U':z/2,'L':z/2-z**3/6-z**4/4-z**5/8-z**6/48}
    vals={name:coefficients(J,P,e=e) for name,P in ps.items()}
    vals['Bell']=coefficients(J,0,collisions=False)
    vals['V_over_Bell']=quotient(vals['V'],vals['Bell'])
    for name,seq in vals.items():
        print(name,flush=True)
        for j,val in enumerate(seq): print(' ',j,str(val),flush=True)
    data={name:[str(v) for v in seq] for name,seq in vals.items()}
    target.write_text(json.dumps({'order':J,'coefficients':data},indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
