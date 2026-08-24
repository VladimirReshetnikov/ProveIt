# Exact integer arithmetic only.
def qp(u,p):
    # u coprime to p, u an integer mod p^2
    return ((pow(u,p-1,p*p)-1)//p) % p

def check(p, verbose=True):
    p2=p*p
    units=[u for u in range(1,p2) if u%p!=0]
    assert len(units)==p*(p-1)
    q2=qp(2,p); q3=qp(3,p)
    # zero set of Delta
    Z=set()
    for M in units:
        qM=qp(M,p)
        for A in units:
            if (qM*q3 - qp(A,p)*q2) % p == 0:
                Z.add((M,A))
    # control-twist set: {(2^t u, 3^t w) mod p^2 : t in Z, u^{p-1}=1 mod p^2, w^{p-1}=1 mod p^2}
    K=[u for u in units if pow(u,p-1,p2)==1]
    C=set()
    for t in range(0, p*(p-1)):   # t over full range of Z mod ord, NOT assuming t mod p suffices
        for u in K:
            for w in K:
                C.add((pow(2,t,p2)*u % p2, pow(3,t,p2)*w % p2))
    # also compute the set using only t in 0..p-1 (as the claim's count assumes)
    Csmall=set()
    for t in range(0,p):
        for u in K:
            for w in K:
                Csmall.add((pow(2,t,p2)*u % p2, pow(3,t,p2)*w % p2))
    tot=(p*(p-1))**2
    from fractions import Fraction
    if verbose:
        print(f"p={p} q_p(2)={q2} q_p(3)={q3} |K|={len(K)}")
        print(f"  |Z|={len(Z)}  |C_full|={len(C)}  |C_t<p|={len(Csmall)}  total={tot}")
        print(f"  Z==C_full: {Z==C}   Z==C_small: {Z==Csmall}")
        print(f"  |Z|/tot = {Fraction(len(Z),tot)}   claimed 1/{p}")
        print(f"  |Z|/p^4 = {Fraction(len(Z),p**4)}  claimed (1-1/p)^2/p = {Fraction((p-1)**2,p**3)}")
    return len(Z),len(C),tot

for p in [5,7,11,13]:
    check(p)
