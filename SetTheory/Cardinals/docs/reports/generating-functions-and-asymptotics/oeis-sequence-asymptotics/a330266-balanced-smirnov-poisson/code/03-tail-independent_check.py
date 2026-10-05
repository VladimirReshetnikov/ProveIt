#!/usr/bin/env python3
"""Independent finite-PGF expansion: no H_s/Euler-operator construction.

Exact truncated h-polynomial arithmetic follows the recurrence
R (R^n)' = n R' R^n, then divides each coefficient by (N)_m
and takes the logarithm directly in v.  h=1/N and n=N/k.
"""
from math import factorial
from collections import Counter
import sympy as s

k, v = s.symbols('k v')
ORDER = 4
MAX_V = 12


def require(test, msg):
    if not test:
        raise ValueError(msg)


def zeros():
    return [s.S.Zero] * (ORDER + 1)


def add(a, b):
    return [s.expand(x + y) for x, y in zip(a, b)]


def mul(a, b):
    return [s.expand(sum(a[t] * b[j-t] for t in range(j+1)))
            for j in range(ORDER+1)]


def shift(a, j, scale):
    return [s.S.Zero if t < j else s.expand(scale*a[t-j])
            for t in range(ORDER+1)]


def finite_pgf_expansion():
    # C_m = h^m [z^m] R_k(z)^(1/(kh)).
    a = [s.prod(k-t for t in range(j))*s.prod(k-1-t for t in range(j))
         / factorial(j) for j in range(ORDER+2)]
    C = [[s.S.One] + [s.S.Zero]*ORDER]
    phi = [C[0]]
    logphi = [zeros()]
    for m in range(1, MAX_V+1):
        cm = zeros()
        for j in range(1, min(m, ORDER+1)+1):
            cm = add(cm, shift(C[m-j], j-1, a[j]*j/(k*m)))
            if j <= ORDER:
                cm = add(cm, shift(C[m-j], j, a[j]*(j-m)/m))
        C.append(cm)
        denom = [s.S.One]+[s.S.Zero]*ORDER
        for j in range(m):
            denom = mul(denom, [s.Integer(j)**r for r in range(ORDER+1)])
        phi.append(mul(cm, denom))
        qm = phi[m]
        for j in range(1, m):
            qm = add(qm, [-s.Rational(j,m)*x for x in mul(logphi[j], phi[m-j])])
        logphi.append(qm)
    # Explicit target formulas transcribed from the reviewed note. No
    # generated coefficient file or author's checker is imported.
    lam = k-1
    q_expected = [s.S.Zero,
        -lam**2*v**2/2,
        lam**2*v**2*(2*(k-2)*v-3)/6,
        -lam**2*v**2*((k*k-6*k+7)*v**2-4*(k-2)*v+2)/4,
        lam**2*v**2*(12*(k**3-14*k**2+41*k-34)*v**3
            -15*(7*k**2-38*k+43)*v**2+140*(k-2)*v-30)/60]
    for m in range(1, MAX_V+1):
        for j in range(ORDER+1):
            target = ((k-1) if m == 1 else 0) if j == 0 else s.expand(q_expected[j]).coeff(v,m)
            require(s.expand(logphi[m][j]-target)==0,
                    f'Direct finite-PGF disagreement at h^{j} v^{m}')
    print(f'Direct finite-PGF recurrence independently agrees through h^{ORDER}, v^{MAX_V}.')
    for j in range(1, ORDER+1):
        q = s.factor(sum(logphi[m][j]*v**m for m in range(1,MAX_V+1)))
        print(f'Direct Q_{j}(v) = {q}')
    # Re-exponentiate at v=-1 independently; the degree theorem in the
    # note ensures no v powers beyond MAX_V occur at these h orders.
    q = [0]+[sum(logphi[m][j]*(-1)**m for m in range(1,MAX_V+1))
              for j in range(1,ORDER+1)]
    p = [s.S.One]
    for j in range(1,ORDER+1):
        p.append(s.factor(sum(t*q[t]*p[j-t] for t in range(1,j+1))/j))
    expected_p4 = (k-1)**2*(15*k**6-330*k**5+2345*k**4-7212*k**3+13313*k**2-10122*k+2183)/5760
    require(s.expand(p[4]-expected_p4)==0, 'Fourth-order probability disagreement')
    print(f'Direct fourth probability coefficient: {p[4]}')


def brute_force_model():
    # Multiset rank words are equiprobable because each lifts to (k!)^n
    # labeled-card permutations. Enumeration is independent of rook counts.
    for n, K in [(1,2),(2,2),(3,2),(2,3),(3,3),(4,2)]:
        dist=Counter()
        left=[K]*n
        def visit(last, adj, length):
            if length==n*K:
                dist[adj]+=1
                return
            for rank in range(n):
                if left[rank]:
                    left[rank]-=1
                    visit(rank, adj+(rank==last),length+1)
                    left[rank]+=1
        visit(-1,0,0)
        total=sum(dist.values())
        require(total==factorial(n*K)//factorial(K)**n, 'Multiset count')
        R=[factorial(K)//factorial(K-j)*s.binomial(K-1,j) for j in range(K)]
        power=[1]
        for _ in range(n):
            new=[0]*(len(power)+len(R)-1)
            for i,x in enumerate(power):
                for j,y in enumerate(R):
                    new[i+j]+=x*y
            power=new
        for m,rm in enumerate(power):
            exact=sum(count*s.binomial(x,m) for x,count in dist.items())
            require(exact*factorial(n*K)==total*rm*factorial(n*K-m),
                    f'Combinatorial PGF n={n}, k={K}, m={m}')
        print(f'Brute-force rank-word PGF verified: n={n}, k={K}, {total} words.')


if __name__=='__main__':
    finite_pgf_expansion()
    brute_force_model()
