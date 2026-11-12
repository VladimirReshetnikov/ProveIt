"""Finite standard-natural checks of the explicit positive-seed construction.
All abbreviations are evaluated from R; R is the only recursion primitive.
Memoization preserves values. This is not a metatheorem formalization.
"""
from functools import cache
from time import perf_counter

calls = 0

def R(n, a, h):
    global calls
    calls += 1
    r = a + 1
    for _ in range(n):
        r = h(r)
    return r

@cache
def S(n): return R(0, n, lambda _: 0)
@cache
def F(n, a, b): return R(n, a, lambda _: b)
@cache
def Z(n): return F(n, 0, 0)
@cache
def p(n): return R(n, 0, Z)
@cache
def c(n): return F(p(n), 1, 0)
@cache
def pulse(n): return R(n, 0, c)
@cache
def K(n): return Z(F(Z(Z(n)), 0, Z(pulse(n))))
@cache
def a0(n): return F(n, 0, n)
@cache
def hs(n): return F(K(n), a0(n), 0)
@cache
def sigma(n): return R(n, 0, hs)

def J(n, h): return sigma(R(n, 0, lambda u: sigma(h(sigma(u)))))

@cache
def N(n): return J(n, Z)
@cache
def j(n): return F(n, 0, F(Z(N(n)), 1, 0))
@cache
def M(n): return J(n, j)
@cache
def pi(n): return F(N(n), 0, F(K(n), 1, 0))
@cache
def A(a,b): return R(b, a, S)
@cache
def D(n): return J(n, lambda u: S(S(u)))
@cache
def T(n): return J(n, lambda u: S(S(S(u))))
@cache
def g(u): return F(M(u), u, F(Z(N(M(u))), S(u), 0))
@cache
def V(n): return R(n, 1, g)
@cache
def G(n): return V(S(n))
@cache
def B(u): return F(u, 0, N(u))
@cache
def H(u): return F(B(u), S(V(u)), u)
@cache
def q(x): return J(x, lambda u: A(u,u))
@cache
def L(x,y): return N(R(y, q(x), H))
@cache
def step(u,m): return F(Z(L(S(u),m)), u,u)
@cache
def W(t,m): return J(t, lambda u: step(u,m))
@cache
def P(m): return J(m, lambda u: F(Z(L(S(S(u)),m)),u,u))
@cache
def C(n,a,b): return P(R(n,a,lambda u:S(b)))

def I(n,a,h): return P(R(n,a,lambda u:S(h(P(u)))))

if __name__ == '__main__':
    start=perf_counter()
    checks=0
    def check(actual, expected):
        global checks
        checks += 1
        assert actual == expected, (checks,actual,expected)
    for n in range(16):
        check(sigma(n), 1 if n==0 else 0 if n==1 else n)
        check(sigma(sigma(n)),n)
        check(K(n),int(n==1))
        check(N(n),n%2)
        check(M(n),n%3)
        check(D(n),2*n)
        check(T(n),3*n)
        check(G(n),(3*n)//2)
        check(H(n),n if n%2 else (3*n)//2)
        check(M(g(n)),Z(M(n)))
        check(pi(S(M(n))),M(n))
        check(S(G(T(n))),F(N(n),T(G(n)),S(S(T(G(n))))))
        check(H(D(n)),T(n))
        check(H(T(n)),T(H(n)))
    for x in range(5):
        for y in range(5):
            check(L(x,y),int(x<=y))
    for n in range(4):
        check(P(n),max(n-1,0))
        for m in range(4):
            check(W(n,m),min(n,m))
    for n in range(3):
        for a in range(3):
            for b in range(3):
                check(C(n,a,b),a if n==0 else b)
    for n in range(3):
        for a in range(2):
            check(I(n,a,S),n+a)
    print({'checks':checks, 'R_calls':calls, 'seconds':round(perf_counter()-start,3),
           'scope':'finite standard-model evaluation from primitive R, with memoization'})
