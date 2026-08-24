"""Two-dimensional terminal-prime transport: numeric exploration.

Object: G_{i,j} = (A^{m+j}) falling (M^{n+i}), M = 2^x, A = 3^x (only ratios matter;
we work in log space with x = 14).  Windows I_{i,j} = (A_j - M_i, A_j].

Part A: sup-kernel column sums (per-prime worst case, mirroring the 1D contraction).
Part B: counting kernel (fraction of window primes capturable by each positive level).

All bounds are upper bounds on capture; 'sup >= 1' localizes where the naive
contraction fails, 'coverage < 1' certifies that most window primes survive.
"""
import math

ln2, ln3 = math.log(2), math.log(3)
x = 14.0
lM, lA = x * ln2, x * ln3   # log M, log A

def logMi(n, i): return (n + i) * lM
def logAj(m, j): return (m + j) * lA

def admissible(n, m, i, j):
    return logMi(n, i) < logAj(m, j)

def huxley_ok(n, m, i, j):
    # window exponent theta = log M_i / log A_j must exceed 7/12 for Huxley
    return logMi(n, i) / logAj(m, j) > 7.0 / 12.0

def part_A(n, m, D):
    """Weighted sup-kernel column sums C(t) = sum_s W_s supV(s->t) / W_t."""
    cells = [(i, j) for i in range(D) for j in range(D) if admissible(n, m, i, j)]
    worst = []
    for (it, jt) in cells:
        logWt = it * lM + jt * lA
        total = 0.0
        contribs = []
        for (i, j) in cells:
            if (i, j) == (it, jt) or j > jt:
                continue
            if j == jt:
                supV = 1.0  # same top: sub-window primes are captured with V=1
            else:
                rho = math.exp(logMi(n, i) - logAj(m, j))  # window relative length
                # count bound M_{it}/(A_j (1-rho)) + 1, plus prime-power allowance
                cnt = math.exp(logMi(n, it) - logAj(m, j)) / max(1e-12, 1.0 - rho)
                powers = (m + jt) / (m + j)
                supV = cnt + 1.0 + max(0.0, powers - 1.0)
            logWs = i * lM + j * lA
            term = math.exp(min(700.0, logWs - logWt)) * supV
            total += term
            contribs.append((term, (i, j)))
        contribs.sort(reverse=True)
        worst.append((total, (it, jt), contribs[:3]))
    worst.sort(reverse=True)
    print(f"[A] n={n} m={m} D={D}: sup column sum = {worst[0][0]:.3e} at target {worst[0][1]}")
    for tot, t, cs in worst[:3]:
        top = ", ".join(f"{c[1]}:{c[0]:.2e}" for c in cs)
        print(f"    target {t}: C = {tot:.3e}; top sources: {top}")
    small = [w for w in worst if w[0] < 1.0]
    print(f"    targets with C < 1: {len(small)}/{len(worst)}")

def part_B(n, m, D):
    """For each source cell s, capture capacity of every level t (support-only bound),
    as a fraction of the window prime count of s."""
    cells = [(i, j) for i in range(D) for j in range(D)
             if admissible(n, m, i, j) and huxley_ok(n, m, i, j)]
    print(f"[B] n={n} m={m} D={D}: {len(cells)} admissible+Huxley cells")
    rows = []
    for (i, j) in cells:
        # window prime count ~ M_i / log(A_j)
        log_primes = logMi(n, i) - math.log(logAj(m, j))
        caps = []
        for (it, jt) in cells:
            if (it, jt) == (i, j) or jt < j:
                continue
            if jt == j:
                # same top: capture only sub-window primes ~ M_min / log A_j
                log_cap = min(logMi(n, i), logMi(n, it)) - math.log(logAj(m, j))
            else:
                # integer-incidence bound M_{it} (m+jt)/(m+j)
                log_cap = logMi(n, it) + math.log((m + jt) / (m + j))
            caps.append((log_cap - log_primes, (it, jt)))
        caps.sort(reverse=True)
        # how many levels can each fully cover the window? (fraction >= 1)
        full = [c for c in caps if c[0] >= 0.0]
        rows.append(((i, j), caps[0] if caps else None, len(full)))
    # summary: which cells are coverable by at least one level?
    cov = [r for r in rows if r[2] > 0]
    print(f"    cells coverable by >= 1 positive level: {len(cov)}/{len(rows)}")
    unc = [r for r in rows if r[2] == 0]
    if unc:
        print(f"    UNCOVERABLE cells (window survives any single level): "
              f"{[r[0] for r in unc][:8]}{'...' if len(unc) > 8 else ''}")
    # detail for a few boundary cells
    for r in rows[:4]:
        (i, j), best, nfull = r
        if best:
            print(f"    cell {(i,j)}: best log10 capture-fraction = "
                  f"{best[0]/math.log(10):+.1f} by {best[1]}; #covering levels = {nfull}")

for (n, m, D) in [(6, 4, 10), (10, 7, 12), (3, 2, 8)]:
    part_A(n, m, D)
    part_B(n, m, D)
    print()
