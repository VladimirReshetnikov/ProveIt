"""Prime-starvation criterion for cross-slice rescue, exact and coefficient-free.

At slice j, index k, the annulus is  Ann = (A^{m+j} - M^{n+i_k}, A^{m+j} - M^{n+i_{k-1}}].
Its primes have v_p = T_k^{(j)} + (captures from slices j' > j).

KEY COUNTING FACT (coefficient-free): a level (i',j') can capture at most
   #{integers in (A^{m+j'} - M^{n+i'}, A^{m+j'}] having a prime factor of annulus size}
   <= M^{n+i'}
annulus primes -- each such integer has AT MOST ONE prime factor that large (two would
exceed the integer).  So if

   #primes(Ann)  >  sum_{j'>j, i'} M^{n+i'}                                    (*)

then some annulus prime is captured by NOTHING above, and integrality forces T_k >= 0.

SECOND FACT: for r >= 2 the Legendre term vanishes whenever p^2 > A^{m+j'}, i.e. whenever
   2(m+j) > (m+j')   <=>   j' < m + 2j,
so for all such slices the capture multiplicity is at most 1 -- no prime-power allowance.

This script evaluates (*) on admissible grids: for which (j,k) is rescue impossible
regardless of coefficients?
"""
import math

x = 14
ln2, ln3 = math.log(2), math.log(3)
lM, lA = x*ln2, x*ln3          # log M, log A

def logMi(n,i): return (n+i)*lM
def logAj(m,j): return (m+j)*lA
def admissible(n,m,i,j):
    th = logMi(n,i)/logAj(m,j)
    return 7.0/12.0 < th < 1.0

def report(n, m, D):
    cells = [(i,j) for i in range(D) for j in range(D) if admissible(n,m,i,j)]
    slices = {}
    for (i,j) in cells:
        slices.setdefault(j, []).append(i)
    for j in slices: slices[j].sort()
    print(f"[n={n} m={m} D={D}] slices: " +
          ", ".join(f"j={j}:i in {slices[j]}" for j in sorted(slices)))
    total_pairs = starved = 0
    for j in sorted(slices):
        above = [(i2,j2) for (i2,j2) in cells if j2 > j]
        # total capture capacity of everything above, in logs (log-sum-exp)
        if above:
            logs = [logMi(n,i2) for (i2,j2) in above]
            mx = max(logs)
            log_cap = mx + math.log(sum(math.exp(l-mx) for l in logs))
        else:
            log_cap = float('-inf')
        for k, i in enumerate(slices[j]):
            total_pairs += 1
            # annulus length = M^{n+i} - M^{n+i_{k-1}}  (k=0: full window)
            if k == 0:
                log_ann = logMi(n,i)
            else:
                lo = logMi(n, slices[j][k-1])
                log_ann = logMi(n,i) + math.log1p(-math.exp(lo - logMi(n,i)))
            log_primes = log_ann - math.log(logAj(m,j))   # PNT in the annulus
            free = log_primes > log_cap
            # no-prime-power range
            npp = all(j2 < m + 2*j for (i2,j2) in above) if above else True
            if free: starved += 1
            flag = "STARVED (rescue impossible)" if free else "rescuable"
            print(f"   slice j={j}, k={k} (i={i}): log10 #primes={log_primes/math.log(10):8.1f}"
                  f"  log10 capacity={(log_cap/math.log(10) if above else float('-inf')):8.1f}"
                  f"  -> {flag}" + ("  [no prime powers]" if npp else ""))
    print(f"   => {starved}/{total_pairs} (slice,index) pairs are rescue-proof by counting alone\n")

for (n,m,D) in [(6,4,4), (10,7,4), (3,2,5), (20,14,4)]:
    report(n,m,D)
