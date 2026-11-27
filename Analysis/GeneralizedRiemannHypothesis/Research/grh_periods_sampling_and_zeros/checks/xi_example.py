"""Illustrative finite-precision Xi calculation. Dependency: mpmath 1.3.
Compute coefficients by the trapezoidal Cauchy integral of -t Xi'(t)/Xi(t)
on |t|=10. No zero coordinates are inputs. This is not interval arithmetic.
"""
from math import isqrt
from mpmath import mp


def log_derivative_samples(nodes, radius):
    w = mp.exp(2 * mp.pi * mp.j / nodes)
    # The logarithmic derivative times t is even with real Taylor coefficients.
    quarter = []
    for j in range(nodes // 4 + 1):
        t = radius * w ** j
        s = mp.mpf('0.5') + mp.j * t
        value = (1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2
                 + mp.zeta(s, derivative=1) / mp.zeta(s))
        quarter.append(-mp.j * t * value)
    half = quarter + [mp.conj(quarter[j]) for j in range(nodes//4-1, 0, -1)]
    return half + half


def taylor_coefficients(nodes, nmax):
    rad = mp.mpf(10)
    samples = log_derivative_samples(nodes, rad)
    assert nmax < nodes
    out = [mp.mpf(0)] * (nmax+1)
    for n in range(2, nmax+1, 2):
        w = mp.exp(-2 * mp.pi * mp.j * n / nodes)
        out[n] = mp.re(mp.fsum(z * w ** j for j, z in enumerate(samples))) / (nodes * rad**n)
    return out


def census(coeff, R, k):
    d = isqrt(k-1)+1
    H = mp.matrix(d)
    for i in range(d):
        for j in range(d):
            n = 2*k+i+j
            H[i,j] = coeff[n] * R**n
    ev = list(mp.eigsy(H, eigvals_only=True))
    return (sum(x > k for x in ev), sum(x < -k for x in ev)), ev


def main():
    mp.dps = 75
    results = []
    for nodes in (256, 384):
        coeff = taylor_coefficients(nodes, 110)
        results.append({(R,k): census(coeff,R,k)
                        for R in (12,18,24) for k in (16,25,36,49)})
    print("Xi(t) centered at 0; 75 decimal digits; integration radius 10.")
    print("R   k   # eigenvalues above k / below -k   smallest distance to either cutoff")
    max_change = 0
    for key, (counts, ev) in results[1].items():
        old_counts, old_ev = results[0][key]
        assert counts == old_counts
        max_change = max(max_change, max(abs(a-b) for a,b in zip(ev, old_ev)))
        R,k = key
        margin = min(abs(abs(x)-k) for x in ev)
        print(f"{R:2} {k:3}   {counts[0]} / {counts[1]}                         {mp.nstr(margin, 7)}")
    print("Maximum absolute eigenvalue change, 256 vs 384 nodes:", mp.nstr(max_change,5))
    print("Finite-precision illustration; agreement is not a certified quadrature bound.")


if __name__ == "__main__":
    main()
