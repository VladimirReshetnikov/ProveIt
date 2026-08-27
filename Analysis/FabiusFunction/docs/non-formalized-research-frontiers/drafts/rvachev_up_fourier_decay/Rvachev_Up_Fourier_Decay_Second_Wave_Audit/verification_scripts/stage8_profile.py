"""Stage 8: finite-level profile and direct shell-constant verification.

Reproduces, in float64 with integer-exact dyadic argument reduction, the
second wave's finite-level claims about the natural-gauge Cesaro profile

    P_n(y) = (1 + F_n(y-1)) / y,
    F_n(z) = (1/A_1^(n)) * int_0^z rho^(-n) W(u) prod_{j<n}|sin(pi 2^j u)| du,

with W(z) = (rho/pi) H(1+z) (1+z)^(kappa_1-1) exp(log^2(1+z)/(2 log 2)),
via 16-point Gauss-Legendre quadrature on each of the 2^n dyadic cells
(the scheme of Doc 7's pseudocode).  Verifies:

  * Doc 5 (n=13):  P(8/7)  = 0.9163240341,  P(1.150) = 0.9248812037,
                   P(10/7) = 1.1181043233,  P(1.425) = 1.1130801816;
    (n=17):        P(8/7) ~ 0.9162741,      P(10/7) ~ 1.1181341.
  * Doc 7 (n=18):  min 0.9162685832208 at y ~ 1.142840221249,
                   max 1.1181397445438 at y ~ 1.428632869969;
    (n=19 cell-boundary values):  0.9162686675 and 1.1181395810.
  * Doc 6 (level 18): the 16-point profile table.
  * Doc 7: A_1 direct at n=18 = 0.09126612413156757,
           A_1^log direct at n=18 = 0.09386063575678312;
    convergence of both through n = 13..20 against the stage-7 spectral
    values.

Reads rho_1/kappa_1 from constants.json (stage7).
"""

import json
import os
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
with open(os.path.join(HERE, "constants.json")) as f:
    C = json.load(f)

RHO = float(C["rho1"])
LOGA = np.log(2.0)
KAPPA1 = 0.5 + np.log(np.pi / RHO) / LOGA

# 16-point Gauss-Legendre on [0,1]
gl_x, gl_w = np.polynomial.legendre.leggauss(16)
gl_x = (gl_x + 1.0) / 2.0
gl_w = gl_w / 2.0


def log_H(y):
    """log prod_{m>=1} sinc(pi y / 2^m), vectorised, 1 <= y <= 2."""
    s = np.zeros_like(y)
    for m in range(1, 61):
        u = np.pi * y / 2.0 ** m
        s += np.log(np.sin(u) / u)
    return s


def log_W(z):
    y = 1.0 + z
    return (np.log(RHO / np.pi) + log_H(y) + (KAPPA1 - 1.0) * np.log(y)
            + np.log(y) ** 2 / (2.0 * LOGA))


def log_P(j0, off, n):
    """log prod_{j<n} |sin(pi 2^j z)| at z = (j0 + off)/2^n.

    j0 : int64 array of cell indices (0 <= j0 < 2^n); off : float offsets
    in [0,1).  frac(2^j z) is computed with integer-exact reduction of the
    dyadic part:  2^j z = (j0 * 2^j)/2^n + 2^j off/2^n, and
    (j0 * 2^j) mod 2^n is exact in int64 for n <= 31.
    """
    s = np.zeros(j0.shape, dtype=np.float64)
    scale = 2.0 ** (-n)
    for j in range(n):
        m1 = (j0 << j) & ((1 << n) - 1)          # exact dyadic part mod 2^n
        frac = (m1.astype(np.float64) + off * (1 << j)) * scale
        frac -= np.floor(frac)
        s += np.log(np.abs(np.sin(np.pi * frac)))
    return s


def cell_masses(n, chunk=1 << 14):
    """(mass, mass_log): per-cell integrals of the normalised shell density
    and of the same density weighted by 1/(1+z)."""
    ncells = 1 << n
    mass = np.zeros(ncells)
    mass_log = np.zeros(ncells)
    delta = 2.0 ** (-n)
    base = -n * np.log(RHO)
    for start in range(0, ncells, chunk):
        j0 = np.arange(start, min(start + chunk, ncells), dtype=np.int64)
        j0m = np.repeat(j0, 16)
        off = np.tile(gl_x, j0.size)
        z = (j0m.astype(np.float64) + off) * delta
        ld = base + log_W(z) + log_P(j0m, off, n)
        dens = np.exp(ld)
        w = np.tile(gl_w, j0.size)
        m = (dens * w).reshape(j0.size, 16).sum(axis=1) * delta
        ml = (dens / (1.0 + z) * w).reshape(j0.size, 16).sum(axis=1) * delta
        mass[start:start + j0.size] = m
        mass_log[start:start + j0.size] = ml
    return mass, mass_log


def partial_cell_mass(n, z_end):
    """Integral of the density over [j0*delta, z_end) inside one cell."""
    delta = 2.0 ** (-n)
    j0 = np.int64(np.floor(z_end / delta))
    a = j0 * delta
    width = z_end - a
    if width <= 0:
        return 0.0, j0
    off = gl_x * (width / delta)          # offsets within the cell, in [0,1)
    j0v = np.full(16, j0, dtype=np.int64)
    z = a + gl_x * width
    ld = -n * np.log(RHO) + log_W(z) + log_P(j0v, off, n)
    return float(np.sum(np.exp(ld) * gl_w) * width), j0


def profile_at(n, y, mass, A1n):
    """P_n(y) with exact partial-cell integration up to z = y-1."""
    z_end = y - 1.0
    pm, j0 = partial_cell_mass(n, z_end)
    F = (mass[:j0].sum() + pm) / A1n
    return (1.0 + F) / y


def main():
    A1_spec = float(C["A1_spectral"])
    A1log_spec = float(C["A1log_spectral"])

    print("=" * 72)
    print("Direct A_1 and A_1^log convergence (16-pt Gauss per dyadic cell)")
    print("=" * 72)
    print(f"spectral (stage 7): A_1     = {A1_spec:.17f}")
    print(f"                    A_1^log = {A1log_spec:.17f}")
    saved = {}
    for n in (13, 15, 17, 18, 19, 20):
        mass, mass_log = cell_masses(n)
        A1n = mass.sum()
        B1n = mass_log.sum()
        saved[n] = (mass, A1n)
        print(f"n={n:2d}: A_1^(n) = {A1n:.17f}   A_1^log(n) = "
              f"{B1n / LOGA:.17f}")
    print("Doc 7 direct n=18: A_1 = 0.09126612413156757, "
          "A_1^log = 0.09386063575678312")

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("Doc 5 profile features (n = 13 and 17)")
    print("=" * 72)
    claims13 = [(8.0 / 7.0, "8/7", 0.9163240341),
                (1.150, "1.150", 0.9248812037),
                (10.0 / 7.0, "10/7", 1.1181043233),
                (1.425, "1.425", 1.1130801816)]
    for n in (13, 17):
        mass, A1n = saved[n]
        print(f"-- n = {n}")
        for y, lbl, claim in claims13 if n == 13 else [
                (8.0 / 7.0, "8/7", 0.9162741), (10.0 / 7.0, "10/7", 1.1181341)]:
            v = profile_at(n, y, mass, A1n)
            print(f"   P_{n}({lbl:5s}) = {v:.10f}   (claimed {claim})")

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("Doc 7 refined range (n = 18, 19): cell-boundary scan")
    print("=" * 72)
    for n in (18, 19):
        mass, A1n = saved[n]
        Fb = np.concatenate([[0.0], np.cumsum(mass)]) / A1n
        yb = 1.0 + np.arange((1 << n) + 1) / float(1 << n)
        prof = (1.0 + Fb) / yb
        imin, imax = int(np.argmin(prof)), int(np.argmax(prof))
        print(f"n={n}: min {prof[imin]:.13f} at y = {yb[imin]:.12f}")
        print(f"       max {prof[imax]:.13f} at y = {yb[imax]:.12f}")
    print("Doc 7: n=18 min 0.9162685832208 at 1.142840221249,")
    print("            max 1.1181397445438 at 1.428632869969;")
    print("       n=19 boundary values 0.9162686675 and 1.1181395810.")
    print("Comparative audit's coarse-grid range was [0.9249, 1.1133].")

    # ------------------------------------------------------------------
    print()
    print("=" * 72)
    print("Doc 6 sixteenth-grid profile table (their level-18 values)")
    print("=" * 72)
    doc6 = [(1.0625, 0.945118496), (1.1250, 0.925107303),
            (1.1875, 0.961711083), (1.2500, 0.971580861),
            (1.3125, 0.995925058), (1.3750, 1.079490550),
            (1.4375, 1.114228254), (1.5000, 1.086316716),
            (1.5625, 1.058951765), (1.6250, 1.076832568),
            (1.6875, 1.108201849), (1.7500, 1.099910476),
            (1.8125, 1.079553278), (1.8750, 1.062385735),
            (1.9375, 1.032028829)]
    mass, A1n = saved[18]
    Fb = np.concatenate([[0.0], np.cumsum(mass)]) / A1n
    worst = 0.0
    for y, theirs in doc6:
        idx = int(round((y - 1.0) * (1 << 18)))
        mine = (1.0 + Fb[idx]) / y
        worst = max(worst, abs(mine - theirs))
        print(f"y={y:.4f}: mine {mine:.9f}   Doc 6 {theirs:.9f}   "
              f"diff {mine - theirs:+.2e}")
    print(f"max |diff| = {worst:.2e}")


if __name__ == "__main__":
    main()
