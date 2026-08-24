import random, math
from fractions import Fraction

# Steps 3 and 4 as PURE ALGEBRA: are they identities/valid inequalities?
# tails T_k = sum_{l>=k} c_l ; Delta_1 = M^{i_1}, Delta_k = M^{i_k}-M^{i_{k-1}}
def test(M,A,trials=200000):
    worst_ratio = Fraction(0)
    bal_fail = 0
    for _ in range(trials):
        nsl = random.randint(1,3)
        cells = {}
        for j in range(nsl):
            s = random.randint(1,4)
            idx = sorted(random.sample(range(0,7), s))
            for i in idx:
                cells[(i,j)] = random.randint(-6,6)
        P = 0; Nn = 0; Phi = 0; bal = 0
        for j in range(nsl):
            sl = sorted([i for (i,jj) in cells if jj==j])
            if not sl: continue
            prev = 0
            for k,i in enumerate(sl):
                T = sum(cells[(ii,j)] for ii in sl[k:])
                D = M**i - prev
                prev = M**i
                if T>0: P += T*D*A**j
                else:   Nn += (-T)*D*A**j
            for i in sl:
                c = cells[(i,j)]
                bal += c*M**i*A**j
                if c>0: Phi += c*M**i*A**j
        if P - Nn != bal: bal_fail += 1
        den = 2*P+2*Nn
        if den>0:
            r = Fraction(Phi, den)
            if r > worst_ratio: worst_ratio = r
    return bal_fail, float(worst_ratio)

for (M,A) in [(2,3),(5,11),(2**14+6,3**14+2)]:
    bf, wr = test(M,A, 40000)
    print(f"M={M} A={A}: P-N != balance failures = {bf};  worst Phi+/(2P+2N) = {wr:.4f}")
