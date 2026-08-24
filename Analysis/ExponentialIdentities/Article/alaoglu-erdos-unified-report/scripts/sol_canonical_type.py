"""Type of the canonical product on the solution monoid Sol = N_0 + N_0*beta.

Sol has counting function N(T) = T^2/(2 beta) + O(T) and ALL its points real positive.
Hadamard: sum 1/s^3 converges while sum_{s<=r} 1/s^2 diverges like (1/beta) log r, so the
genus equals the order (both 2) with divergent coefficient sum, and the canonical product --
of minimal growth among functions vanishing on Sol -- satisfies log M(r) ~ r^2 log r / beta.
Hence EVERY entire function vanishing on Sol has tau_2 = +infinity, infinitely above Pila's
threshold 1/(832 beta^2 log2 log3).  This script measures the two sums.
"""
import math

beta = 14 + math.sqrt(2) / 1000.0        # irrational, ~14 (a counterexample has beta >= 14)

def sums(T):
    s2 = s3 = 0.0
    cnt = 0
    k = 0
    while k * beta <= T:
        n = 0
        while n + k * beta <= T:
            s = n + k * beta
            if s > 0:
                s2 += 1.0 / (s * s)
                s3 += 1.0 / (s * s * s)
                cnt += 1
            n += 1
        k += 1
    return cnt, s2, s3

print(f"beta = {beta:.6f}   1/beta = {1/beta:.8f}")
print(f"{'T':>8} {'#Sol<=T':>10} {'T^2/(2b)':>12} {'sum 1/s^2':>12} {'increment':>10} {'sum 1/s^3':>11}")
prev = None
for T in (500, 1000, 2000, 4000, 8000):
    c, s2, s3 = sums(T)
    inc = '' if prev is None else f"{(s2 - prev)/math.log(2):10.5f}"
    print(f"{T:8} {c:10} {T*T/(2*beta):12.1f} {s2:12.5f} {inc:>10} {s3:11.6f}")
    prev = s2
print("\nincrement per doubling -> 1/beta confirms sum 1/s^2 ~ (1/beta) log r (divergent);")
print("sum 1/s^3 converges.  Genus = order = 2, divergent sum => tau_2 = +infinity.")
