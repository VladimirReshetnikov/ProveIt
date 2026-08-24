"""Fast counterexample hunt for THEOREM B: enumerate top-heavy vectors directly
(via nonnegative tail vectors T) and see whether any nonzero one is balanced."""
from itertools import product

def run(M, A, I, J, TB):
    """Enumerate all c with all slice tails in [0,TB]; check balance sum c_ij M^i A^j = 0."""
    # a slice with cells i=0..I-1 is determined by its tail vector (T_0,...,T_{I-1}) >= 0:
    #   c_i = T_i - T_{i+1},  T_I = 0.  Balance contribution = sum_k T_k (M^k - M^{k-1}), M^{-1}:=0
    slice_vals = []   # (balance weight of slice, T-vector)
    for T in product(range(0, TB+1), repeat=I):
        prev = 0; wt = 0
        for k in range(I):
            wt += T[k]*(M**k - prev); prev = M**k
        slice_vals.append((wt, T))
    tot = 0; hits = 0; ex = None
    for combo in product(slice_vals, repeat=J):
        b = sum(combo[j][0]*A**j for j in range(J))
        tot += 1
        if b == 0:
            if any(t != 0 for (_,T) in combo for t in T):
                hits += 1; ex = combo
    return tot, hits, ex

for (M,A,I,J,TB) in [(2,3,3,3,4),(3,2,3,3,4),(5,11,3,3,3),(2,3,4,3,3),(7,13,3,3,4)]:
    tot,hits,ex = run(M,A,I,J,TB)
    print(f"M={M} A={A} I={I} J={J} tails in [0,{TB}]: enumerated {tot} top-heavy patterns;"
          f" nonzero balanced ones = {hits}", ex if ex else "")
