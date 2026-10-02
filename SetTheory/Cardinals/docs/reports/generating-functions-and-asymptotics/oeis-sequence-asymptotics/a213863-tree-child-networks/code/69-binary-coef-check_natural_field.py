#!/usr/bin/env python3
"""Independent natural-coordinate recurrence in Q[B][y,t]."""
from pathlib import Path
import json
import sympy as s
import derive_coefficients as a

x,e=a.x,a.e
B=s.symbols('B')
a.c=s.Rational(1,3)
a.V=(x+B)/3

def residual(Fs,coeff,m):
    u=a.trunc(1-x*e**2/(3*(1+x*e**2/2-e**3/2)),m)
    ym=a.trunc((x-e)*(1-e**3/2)**(-s.Rational(1,3)),m)
    yp=a.trunc((x+e)*(1-e**3/2)**(-s.Rational(1,3)),m)
    rhs=a.ZERO
    for k,F in enumerate(Fs):
        inside=a.add(a.mul(u,a.shift(F,ym,m-k)),a.shift(F,yp,m-k))
        rhs=a.add(rhs,a.mul(e**k*a.trunc((1-e**3/2)**(-s.Rational(k,3)),m-k),inside))
    scalar=2+sum(v*e**j for j,v in coeff.items())
    lhs=a.mul(scalar,tuple(sum(e**k*F[i] for k,F in enumerate(Fs)) for i in (0,1)))
    return a.add(rhs,a.mul(-1,lhs))

n=7; Fs=[(s.S.One,s.S.Zero)];coeff={2:B/3}
for m in range(3,n+1):
    R,S=[s.expand(p).coeff(e,m) for p in residual(Fs,coeff,m)]
    P,Q=a.poly_solve(-R,-S)
    mu=s.factor(-a.c*Q.subs(x,0));Q=s.expand(Q+mu/a.c)
    G=(s.factor(P),s.factor(Q));coeff[m]=mu;Fs.append(G)
    assert G[1].subs(x,0)==0
    assert s.simplify(G[0].subs(x,0)+s.diff(G[1],x).subs(x,0))==0
    # Explicitly reject algebraic coefficients outside Q[B].
    for p in G: s.Poly(p,x,B,domain=s.QQ)
    s.Poly(mu,B,domain=s.QQ)
    print('order',m,'s_t=',s.factor(mu/2),'profile=',G,flush=True)
rr=residual(Fs,coeff,n)
assert all(s.expand(p).coeff(e,j)==0 for p in rr for j in range(n+1))

old=json.loads(Path(__file__).with_name('coefficients-order7.json').read_text())['nonautonomous']
checks={}
for k,oldstr in old['s_coefficients'].items():
    m=int(k)
    val=s.sympify(oldstr,locals={'ell':a.ell}).subs(a.ell,B*2**s.Rational(2,3)/3)/2**s.Rational(m,3)
    checks[k]=s.simplify(coeff[m]/2-val)==0
assert all(checks.values())

# Scalar antidifference at N/2=t^-3: previous t is t*(1-t^3/2)^(-1/3).
hh=s.symbols('h1:5');rho=-s.Rational(1,3)
lr=B/e*(1-(1-e**3/2)**s.Rational(1,3))-rho*s.log(1-e**3/2)
lr+=sum(h*e**j*(1-(1-e**3/2)**(-s.Rational(j,3))) for j,h in enumerate(hh,1))
target=a.trunc(s.log(1+sum(v/2*e**k for k,v in coeff.items())),n)
diff=a.trunc(lr-target,n)
sol=s.solve([diff.coeff(e,k) for k in range(4,n+1)],hh,dict=True)[0]
sol={k:s.factor(v) for k,v in sol.items()}
f=[s.S.Zero,s.S.One]
for j in range(2,10): f.append(s.expand((B*f[j-2]+(f[j-3] if j>=3 else 0))/(3*j*(j-1))))
F=sum(v*x**j for j,v in enumerate(f));Fp=s.diff(F,x)
end=a.trunc(sum(e**k*(P*F+Q*Fp).subs(x,e) for k,(P,Q) in enumerate(Fs))/e,4)
logend=a.trunc(s.log(end),4)
logs=[s.factor(sol[h]+logend.coeff(e,k)) for k,h in enumerate(hh,1)]
assert logs==[B**2/18,0,-s.Rational(1,9),-B**2/162]
print('natural logH:',sol)
print('natural endpoint/t:',end)
print('natural diagonal logarithmic corrections:',logs)
data={'coordinate':'t=(N/2)^(-1/3), y=(j+1)t',
      'airyequation':'Ftilde_second=(y+B)*Ftilde/3',
      's_coefficients':{str(k):str(s.factor(v/2)) for k,v in coeff.items()},
      'profiles':[[str(p),str(q)] for p,q in Fs],
      'all_profiles_in_Q_B_y':True,'residual_zero_through':n,
      'matches_rescaled_original_coefficients':checks,
      'logH':{str(k):str(v) for k,v in sol.items()},
      'endpoint_over_t':str(end),'diagonal_log_coefficients':list(map(str,logs))}
Path(__file__).with_name('natural-field.json').write_text(json.dumps(data,indent=2)+'\n')
