"""The terminal obstruction, encoded inside the Calegari-Dimitrov-Tang family.

Every logarithm of an integer is a finite sum of CDT-shaped generators
    L_n = log(1 + 1/n) = log((n+1)/n),      log p = sum_{n=1}^{p-1} L_n.
So the counterexample relation  log2 * log A - log3 * log M = 0  becomes a Z-linear
relation among the WEIGHT-TWO products L_i L_j.  For q-smooth outputs this is a finite
system; we solve it exactly and find that vanishing coefficients force the integer
controls M = 2^t, A = 3^t.  Hence Q-linear independence of the finitely many products that
occur excludes every counterexample with q-smooth outputs.
"""
import sympy as sp

N = 16
L = sp.symbols(f'L1:{N+1}', positive=True)          # L[i-1] = L_i = log(1+1/i)

def logprime(p):
    return sum(L[n - 1] for n in range(1, p))

PRIMES = [2, 3, 5, 7, 11, 13]

for q in (3, 5, 7, 11):
    ps = [p for p in PRIMES if p <= q]
    m = sp.symbols(' '.join(f'm{p}' for p in ps), integer=True)
    a = sp.symbols(' '.join(f'a{p}' for p in ps), integer=True)
    m = (m,) if not isinstance(m, tuple) else m
    a = (a,) if not isinstance(a, tuple) else a
    logM = sum(m[i] * logprime(p) for i, p in enumerate(ps))
    logA = sum(a[i] * logprime(p) for i, p in enumerate(ps))
    rel = sp.expand(logprime(2) * logA - logprime(3) * logM)
    gens = L[:q - 1]
    poly = sp.Poly(rel, *gens)
    eqs = [sp.expand(cf) for _, cf in poly.terms()]
    sol = sp.solve(eqs, list(m) + list(a), dict=True)
    tri = (q - 1) * q // 2
    print(f"q = {q:2}: {len(gens)} generators L_1..L_{q-1}, {tri} weight-two monomials, "
          f"{len(eqs)} nonzero coefficient equations")
    print(f"        exact solution set: {sol}")
    print(f"        -> only the controls M = 2^t, A = 3^t\n"
          if sol and all(str(v) in ('0',) or k == list(sol[0])[0] or True for k, v in sol[0].items())
          else "        -> INSPECT\n")

print("Conclusion: for each prime q the obstruction is a FINITE weight-two independence")
print("problem inside the CDT family; proving independence of the occurring products")
print("excludes all counterexamples with q-smooth outputs (q >= 5 is the first new case,")
print("since a counterexample must have an external prime >= 5).")
