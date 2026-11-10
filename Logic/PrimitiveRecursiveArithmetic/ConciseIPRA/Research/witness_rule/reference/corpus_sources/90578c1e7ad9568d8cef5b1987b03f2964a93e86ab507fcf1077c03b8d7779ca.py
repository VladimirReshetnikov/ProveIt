"""Finite standard-N diagnostics for the explicit scalar arithmetic terms.

This evaluates the displayed construction, not an assumed predecessor.
It supplies examples, not proof of the whole-domain theorems. Functions
are memoized only for speed. Each J is the proved conjugation expression.
"""
from functools import cache
import json
from pathlib import Path

def R(n,a,h):
    state=a+1
    for _ in range(n):state=h(state)
    return state

def F(n,a,b):return R(n,a,lambda _:b)
@cache
def Z(n):return F(n,0,0)
@cache
def p(n):return R(n,0,Z)
@cache
def c(n):return F(p(n),1,0)
@cache
def b(n):return R(n,0,c)
@cache
def K(n):return Z(F(Z(Z(n)),0,Z(b(n))))
@cache
def a0(n):return F(n,0,n)
@cache
def h(n):return F(K(n),a0(n),0)
@cache
def sigma(n):return R(n,0,h)

def J(n,f):return sigma(R(n,0,lambda u:sigma(f(sigma(u)))))
@cache
def N(n):return J(n,Z)
@cache
def j(n):return F(n,0,F(Z(N(n)),1,0))
@cache
def M(n):return J(n,j)
@cache
def pi(n):return F(N(n),0,F(K(n),1,0))
@cache
def A(a,b):return R(b,a,lambda u:u+1)
@cache
def D(n):return J(n,lambda u:u+2)
@cache
def T(n):return J(n,lambda u:u+3)
@cache
def g(n):return F(M(n),n,F(Z(N(M(n))),n+1,0))
@cache
def V(n):return R(n,1,g)
@cache
def G(n):return V(n+1)
@cache
def B(n):return F(n,0,N(n))
@cache
def H(n):return F(B(n),V(n)+1,n)
@cache
def q(n):return J(n,lambda u:A(u,u))
@cache
def E(n):return q(n)+1
@cache
def L(x,y):return N(R(y,q(x),H))
@cache
def W(t,m):return J(t,lambda u:F(Z(L(u+1,m)),u,u))
@cache
def P(m):return J(m,lambda u:F(Z(L(u+2,m)),u,u))

def main():
    counts={};failures=[]
    def check(family,arguments,left,right):
        counts[family]=counts.get(family,0)+1
        if left!=right:failures.append(dict(family=family,arguments=arguments,left=left,right=right))
    for n in range(13):
        check('one_detector',[n],K(n),int(n==1))
        check('transposition',[n],sigma(n),1 if n==0 else 0 if n==1 else n)
        check('involution',[n],sigma(sigma(n)),n)
        check('zero_iteration',[n],J(n,lambda u:u+2),2*n)
        check('parity_positive_bridge',[n],N(n),Z(p(n)))
        check('parity',[n],N(n),n%2)
        check('mod_three',[n],M(n),n%3)
        check('finite_retraction_M',[n],pi(M(n)+1),M(n))
        check('finite_retraction_Z',[n],pi(Z(n)+1),Z(n))
        check('ramp_invariant',[n],M(G(n)),N(n))
        check('ramp_double',[n],G(D(n)),T(n))
        check('lifted_triple',[n],G(T(n))+1,F(N(n),T(G(n)),T(G(n))+2))
        check('factor_double',[n],H(D(n)),T(n))
        check('factor_triple',[n],H(T(n)),T(H(n)))
    for x in range(6):
        for y in range(6):
            check('comparator',[x,y],L(x,y),int(x<=y))
    for m in range(6):
        check('predecessor',[m],P(m),max(0,m-1))
        check('saturation_diagonal',[m],W(m,m),m)
        check('saturation_extra_step',[m],W(m+1,m),m)
    result=dict(check_count=sum(counts.values()),families=counts,failures=failures,predecessor_examples=[P(m) for m in range(6)],scope='Finite standard-natural-number calculations only; not a general, intuitionistic, or nonstandard-model proof.')
    output=Path(__file__).resolve().parent.parent/'evidence/implementation_arithmetic_diagnostics.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    if failures:raise SystemExit(1)
if __name__=='__main__':main()
