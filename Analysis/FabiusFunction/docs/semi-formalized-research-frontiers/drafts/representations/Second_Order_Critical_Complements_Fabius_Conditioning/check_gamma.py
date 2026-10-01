"""High-precision diagnostics, not certified bounds or a proof.

Compare the derived expansion to exact clipped Gamma densities.
Run: python check_gamma.py
Requires mpmath. Writes gamma_checks.csv in the current directory.
"""
import csv
import mpmath as mp

mp.mp.dps = 70


def bisect(f, lo, hi, count=260):
    flo = f(lo)
    for _ in range(count):
        mid = (lo + hi) / 2
        fm = f(mid)
        if fm == 0:
            return mid
        if (fm > 0) == (flo > 0):
            lo, flo = mid, fm
        else:
            hi = mid
    return (lo + hi) / 2


def roots(z):
    f = lambda y: y - 1 - mp.log(y) - z
    lo = mp.exp(-z - 3)
    hi = 2 * (z + 2)
    while f(hi) < 0:
        hi *= 2
    return bisect(f, lo, mp.mpf(1)), bisect(f, mp.mpf(1), hi)


def gamma_profile(m, z, extra):
    shape = m + 1 + extra
    log_a = -mp.log(2 * mp.pi * m) / 2 - m * z
    log_g = lambda u: (shape - 1) * mp.log(u) - u - mp.loggamma(shape)
    mode = mp.mpf(shape - 1)
    f = lambda u: log_g(u) - log_a
    hi = 2 * mode + 2 * m * z + 10
    while f(hi) > 0:
        hi *= 2
    left = bisect(f, mp.exp(-m * (z + 5)), mode)
    right = bisect(f, mode, hi)
    tail = (mp.gammainc(shape, 0, left) + mp.gammainc(shape, right, mp.inf))
    tail *= mp.exp(-mp.loggamma(shape) - log_a)
    return right - left + tail


def coefficient(y, extra):
    s = 1 - 1 / y
    # H(s)=(1-s)^(-extra). Cases extra=0 and 1 are exact Gamma profiles.
    L = extra * mp.log(y)
    Ly = extra / y
    A = -mp.mpf(1) / 12 - mp.mpf(extra * (extra + 1)) / 2
    F = (L + 1) / s
    B = A / s + (L + 1) * Ly / s**2 - (L**2 / 2 + L + 1) / (y**2 * s**3)
    return F, B


rows = []
for extra in (0, 1):
    for z in map(mp.mpf, ("0.2", "0.5", "1", "2")):
        ym, yp = roots(z)
        fm, bm = coefficient(ym, extra)
        fp, bp = coefficient(yp, extra)
        for m in (20, 40, 80, 160, 320):
            exact = gamma_profile(m, z, extra)
            leading = m * (yp - ym)
            through_constant = leading + fp - fm
            through_inverse = through_constant + (bp - bm) / m
            rows.append({
                "extra_gamma_shape": extra,
                "z": mp.nstr(z, 10),
                "m": m,
                "exact_clipped_integral": mp.nstr(exact, 28),
                "constant_error": mp.nstr(exact - through_constant, 20),
                "inverse_error": mp.nstr(exact - through_inverse, 20),
                "m2_inverse_error": mp.nstr(m * m * (exact - through_inverse), 20),
            })

with open("gamma_checks.csv", "w", newline="") as file:
    writer = csv.DictWriter(file, fieldnames=rows[0])
    writer.writeheader()
    writer.writerows(rows)

for extra in (0, 1):
    for z in ("0.2", "0.5", "1.0", "2.0"):
        group = [r for r in rows if r["extra_gamma_shape"] == extra and mp.mpf(r["z"]) == mp.mpf(z)]
        print("extra=", extra, "z=", z, "m^2 residuals:",
              [(r["m"], r["m2_inverse_error"]) for r in group])
print("Wrote 40 high-precision diagnostic cases to gamma_checks.csv")
