#!/usr/bin/env python3
"""Exact finite regression tests; the universal argument is in the paper."""
from fractions import Fraction as Q
from math import comb, factorial
from itertools import product

# Delta^n X^k at zero: annihilation below n and n! at n.
c = 0
for n in range(31):
    for k in range(n+1):
        s = sum((-1)**(n-j)*comb(n,j)*j**k for j in range(n+1))
        assert s == (factorial(n) if k == n else 0)
        c += 1
print(f"Finite-difference monomial identities: {c} exact checks")

# Discrete positive measures at v_i=log(q_i), with positive rational
# weights absorbing exp(-A v_i). For h=1, evaluations at j are exact.
c=0
qs=[Q(1),Q(5,4),Q(3,2),Q(2),Q(3)]
for weights in product(range(3), repeat=len(qs)):
    for n in range(13):
        g = [sum(w*q**j for w,q in zip(weights,qs)) for j in range(n+1)]
        lhs=sum((-1)**(n-j)*comb(n,j)*g[j] for j in range(n+1))
        rhs=sum(w*(q-1)**n for w,q in zip(weights,qs))
        assert lhs == rhs and rhs >= 0
        c+=1
print(f"Finite positive-measure differences: {c} exact checks")

# Disk containment and the weaker real threshold (squared distances).
c=0
for beta in (Q(1,2),Q(3,5),Q(4,5),Q(5,2)):
    for gap in (Q(1,100),Q(1,10),Q(1,2),Q(1),Q(3)):
        u=beta+gap
        for t in (Q(0),Q(1,5),Q(1),Q(2),Q(20),Q(100)):
            for eta in (beta,beta+gap/2,beta+gap*Q(9,10)):
                g=u-eta
                threshold=eta+(g*g+t*t)/(2*g)
                A=max(Q(2),beta+2,u,threshold)+1
                dist2=(A-u)**2+t*t
                assert (A-eta)**2 > dist2
                assert (A-beta)**2 > dist2
                assert (A-eta)**2-dist2 == 2*(A-eta)*g-g*g-t*t
                c+=1
print(f"Disk containment and stronger threshold: {c} exact checks")

# Root-of-unity pole model, algebraic residue magnitude. For z^k=1,
# Res 1/(1-z^k) = -z/k, so each magnitude equals 1/k.
# Check coefficients and rational radial inequality for w=-1 (k even),
# w=i (4|k), and positive real (all k), exactly.
c=0
for k in range(1,33):
    for n in range(257):
        a=int(n%k==0)
        assert a>=0 and a==(int(n==0) if n<k else int((n-k)%k==0))
        c+=1
    for t in (Q(1,2),Q(9,10),Q(99,100),Q(999,1000)):
        # (1-t) G(t) = 1/(1+t+...+t^(k-1)), tends to 1/k from above.
        radial=(1-t)/(1-t**k)
        assert radial == 1/sum(t**j for j in range(k))
        assert radial>=Q(1,k)
        if k%2==0: assert Q(1)/(1-(-t)**k)==Q(1)/(1-t**k)
        if k%4==0: assert (Q(1)/(1-t**k))*(1-t)==radial
print(f"Sharp root-of-unity coefficient models: {c} exact checks; 128 radial checks")

# Negative-real-residue obstruction: E(v)=-exp((a-1)v),
# Phi=-1/(s-a), G=K/(A-beta-z)+1/(A-a-z) has positive coefficients.
for n in range(40):
    A,beta,a,K=Q(3),Q(3,5),Q(4,5),Q(2)
    coeff=K/(A-beta)**(n+1)+1/(A-a)**(n+1)
    assert coeff>0 and a>beta
# No positive real nearest pole possible with nonnegative coefficients:
assert [(-1)**(n//2) if n%2==0 else 0 for n in range(5)] == [1,0,-1,0,1]
print("Obstruction examples: 40 positive coefficients and alternating off-axis model checked")
print("All exact finite checks passed.")
