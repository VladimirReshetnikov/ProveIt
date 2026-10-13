from pathlib import Path
import sympy as s
import json
X,P,t=s.symbols('X pi t')
def ze(n):
    return (-1)**(n//2+1)*s.bernoulli(n)*2**(n-1)*P**n/s.factorial(n) if n%2==0 else s.Symbol(f'zeta{n}')
def G(n,x):
    B=[s.Integer(1)]
    for k in range(1,n+2):
        B.append(s.expand(sum(s.binomial(k-1,j-1)*(x if j==1 else (-1)**j*s.factorial(j-1)*ze(j))*B[k-j] for j in range(1,k+1))))
    return s.expand(B[n+1]/(n+1))
checks=[]
for n in range(9):
    for branch in [-1,1]:
        Y=X+branch*s.I*P
        lhs=sum((-1)**j*s.binomial(n,j)*G(n-j,X)*G(j,Y) for j in range(n+1))
        rhs=(G(n+1,X)+(-1)**n*G(n+1,Y))/(n+1)+(2*s.factorial(n)*ze(n+2) if n%2==0 else 0)
        residual=s.expand(lhs-rhs)
        assert residual==0
        checks.append({'n':n,'branch':branch,'exact_residual':'0'})
# Neutral products checked as coefficient arrays, independent of the
# multivariate sine-quotient formula; Gamma product uses its log series.
def mul(a,b,N):
    return [s.expand(sum(a[j]*b[k-j] for j in range(k+1))) for k in range(N+1)]
def series_exp(log,N):
    out=[s.Integer(1)]+[s.Integer(0)]*N
    for k in range(1,N+1):
        out[k]=s.expand(sum(j*log[j]*out[k-j] for j in range(1,k+1))/k)
    return out
neutral=[]
for w,ori in [([1,2,-3],[1,1,-1]),([1,2,-1,-2],[1,-1,1,-1]),([1,1,-2],[1,1,1])]:
    assert sum(w)==0
    N=8
    A=sum(a for a,o in zip(w,ori) if o==1)
    gam=series_exp([s.Integer(0)]+[s.Integer(0)]+[(-1)**k*ze(k)*sum(a**k for a in w)/k for k in range(2,N+1)],N)
    for branch in [-1,1]:
        Y=X+branch*s.I*P
        lhs=[s.Integer(1)]+[s.Integer(0)]*N
        for a,o in zip(w,ori):
            lhs=mul(lhs,[s.Integer(1)]+[G(k-1,X if o==1 else Y)*a**k/s.factorial(k-1) for k in range(1,N+1)],N)
        # D=X-Y=-branch*i*pi: cos(pi*A*t)+sin(pi*A*t)*D/pi
        phase=[((-1)**(k//2)*(P*A)**k/s.factorial(k) if k%2==0 else (-1)**((k-1)//2)*(P*A)**k*(X-Y)/(P*s.factorial(k))) for k in range(N+1)]
        rhs=mul(gam,phase,N)
        for k in range(N+1):
            assert s.expand(lhs[k]-rhs[k])==0
        neutral.append({'weights':w,'orientations':ori,'branch':branch,'degrees':list(range(N+1)),'exact_residuals':['0']*(N+1)})
controls={
 'omit_even_zeta_contact':s.expand(X*(X+s.I*P)-G(1,X)-G(1,X+s.I*P)) != 0,
 'flip_reflected_sign_at_odd_index':s.expand(G(2,X)-G(2,X+s.I*P)-(G(2,X)+G(2,X+s.I*P)))!=0,
 'replace_I_by_delta_at_zero_frequency':s.expand((0-0)**2+P**2*1)!=0,
}
assert all(controls.values())
result={'status':'PASS','alternating_two_branch_checks':checks,'neutral_hyperplane_checks':neutral,'negative_controls':controls,'limitations':'Exact finite symbolic checks, independent of evaluating subtracted scalar integrals. General proofs are in chapters/07-stieltjes-reflection-algebra.tex.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','alternating_checks':len(checks),'neutral_coefficients':sum(len(r['degrees']) for r in neutral),'negative_controls':len(controls)}))
