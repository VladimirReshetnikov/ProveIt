"""Independent rational recurrence obtained from the four-variable Euler equation."""
from functools import lru_cache
import sympy as s
X=s.symbols('k')
@lru_cache(None)
def source(b,n):
    return s.factor(sum(s.binomial(b,j)*3**j*s.binomial(n,l)/(X+n+2*j+2*l+1) for j in range(b+1) for l in range(n+1))/(s.factorial(b)*s.factorial(n)*24**b*48**n))
@lru_cache(None)
def base(b):
    if b<0 or b==1:return s.S.Zero
    if b==0:return -1/((X-1)*(X+1))
    n=b-1
    out= sum(s.binomial(n,j)*3**j/(X+2*j+3) for j in range(n+1))/(s.factorial(n)*24**n)
    out-= (n+1+(2*n-1)*(X+2))*base(n).subs(X,X+2)
    out-=s.Rational(n-2,4)*base(n-1).subs(X,X+4)
    return s.factor(out/(4*(n+1)*(X+1)*(X+2)))
@lru_cache(None)
def coef(b,c):
    if b<0 or c<0 or c==1:return s.S.Zero
    if c==0:return base(b)
    n=c-1;K=X+3
    def r(B,C,k):return coef(B,C).subs(X,k)
    V=(1-n)*r(b,n,K)
    V-=s.Rational(3*n+1,2)*(2*K*r(b,n,K)+s.Rational(1,2)*r(b-1,n,K+2))
    V+=(1-3*n)*(4*K*(K-1)*(b+1)*r(b+1,n,K-2)+(2*K+1)*b*r(b,n,K)+s.Rational(b-1,4)*r(b-1,n,K+2))
    V+=(5-3*n)*(2*K*(b+2)*(b+1)*r(b+2,n-1,K-1)+s.Rational(b*(b+1),2)*r(b+1,n-1,K+1))
    V-=s.Rational(3*(n-1)*(b+1),2)*r(b+1,n-1,K+1)
    V+=(3-n)*(b+3)*(b+2)*(b+1)*r(b+3,n-2,K)
    V-=source(b,n).subs(X,K)
    V=V/(n+1)-6*(X+3)**2*r(b-1,c,X+2)-s.Rational(3,2)*(X+4)*r(b-2,c,X+4)-s.Rational(1,8)*r(b-3,c,X+6)
    return s.factor(V/(8*(X+1)*(X+2)*(X+3)))
if __name__=='__main__':
    import time,json
    start=time.time();out={}
    for c in [0,2,3,4]:
      for b in range(5 if c in [0,2] else 3):
        v=coef(b,c);print((b,c),v,flush=True);out[f'{b},{c}']=str(v)
    print('seconds',time.time()-start)
    open(__import__('pathlib').Path(__file__).resolve().parents[1]/'data'/'selected_coefficients.json','w').write(json.dumps(out,indent=2))
