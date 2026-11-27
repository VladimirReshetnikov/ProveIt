"""Floating-point illustration for the first pole layer modulo 4.

Run with Python 3 and mpmath 1.3.0. The sign-change scan supplies samples.
No completeness, isolation, multiplicity or interval-arithmetic claim is made.
"""
from statistics import median

import mpmath as mp

mp.mp.dps = 42
CHI4 = [0, 1, 0, -1]
EPS = mp.mpf("1e-6")
PROBE = mp.mpf("1e-9")
PAIRS = 5


def beta(s):
    return mp.dirichlet(s, CHI4)


def zeta_hardy(t):
    return mp.siegelz(t)


def beta_hardy(t):
    s = mp.mpc("0.5", t)
    theta = mp.im(mp.loggamma((s + 1) / 2)) + t * mp.log(4 / mp.pi) / 2
    value = mp.expj(theta) * beta(s)
    assert abs(mp.im(value)) < mp.mpf("1e-32")
    return mp.re(value)


def sign_change_samples(hardy):
    samples = []
    left = mp.mpf(40)
    left_value = hardy(left)
    for step in range(1, 201):
        right = 40 + mp.mpf(step) / 5
        right_value = hardy(right)
        if left_value * right_value < 0:
            root = mp.findroot(hardy, (left, right), tol=mp.mpf("1e-34"))
            assert left < root < right and abs(hardy(root)) < mp.mpf("1e-32")
            samples.append(root)
            if len(samples) == PAIRS:
                return samples
        left, left_value = right, right_value
    raise ArithmeticError("The mesh yielded too few sign changes")


def first_layer_derivative(s, principal_coeff, beta_coeff):
    # Principal L modulo 4 is (1 - 2^(-s))*zeta(s).
    log_derivative_principal = (
        mp.zeta(s, derivative=1) / mp.zeta(s) + mp.log(2) / (2**s - 1)
    )
    log_derivative_beta = mp.dirichlet(s, CHI4, derivative=1) / beta(s)
    return principal_coeff * log_derivative_principal + beta_coeff * log_derivative_beta


def residue_probe(height, principal_coeff, beta_coeff):
    center = mp.mpc("0.5", height)
    right = first_layer_derivative(center + PROBE, principal_coeff, beta_coeff)
    left = first_layer_derivative(center - PROBE, principal_coeff, beta_coeff)
    return PROBE * (right - left) / 2


def format_complex(value):
    return f"{float(value.real):.9f}{float(value.imag):+.9f}i"


def main():
    f1, f3 = mp.mpc(2, 3), mp.mpc(-1, 1)
    principal_coeff, beta_coeff = (f1 + f3) / 2, (f1 - f3) / 2
    zeta_samples = sign_change_samples(zeta_hardy)
    beta_samples = sign_change_samples(beta_hardy)
    print("q=4, m=1; open search interval (40,80); mesh step 0.2; 42 decimal digits.")
    print("Five sign changes of each Hardy function; no certified completeness or simplicity.")
    print("pair   zeta ordinate          beta ordinate          corrupted")
    recovered = []
    cross_values, slopes, residuals, probe_errors, clean_errors = [], [], [], [], []
    for j, (z_height, b_height) in enumerate(zip(zeta_samples, beta_samples), start=1):
        z_point, b_point = mp.mpc("0.5", z_height), mp.mpc("0.5", b_height)
        cross_values.extend([abs(beta(z_point)), abs(mp.zeta(b_point))])
        slopes.extend([abs(mp.zeta(z_point, derivative=1)),
                       abs(mp.dirichlet(b_point, CHI4, derivative=1))])
        residuals.extend([abs(mp.zeta(z_point)), abs(beta(b_point))])
        z_res = residue_probe(z_height, principal_coeff, beta_coeff)
        b_res = residue_probe(b_height, principal_coeff, beta_coeff)
        probe_errors.extend([abs(z_res-principal_coeff), abs(b_res-beta_coeff)])
        # Reproducible complex perturbations, both of modulus at most EPS/2.
        z_res += EPS * mp.mpc((-1)**j * j, 5-j) / 10
        b_res += EPS * mp.mpc(5-j, (-1)**(j+1) * j) / 10
        corrupt = j in (2, 4)
        if corrupt:
            z_res += mp.mpc(4*j, -3*j)
            b_res += mp.mpc(-j, 2*j)
        else:
            clean_errors.extend([abs(z_res-principal_coeff), abs(b_res-beta_coeff)])
        recovered.append((z_res+b_res, z_res-b_res))
        print(f"{j:>2}     {float(z_height):.12f}        {float(b_height):.12f}        "
              f"{'yes' if corrupt else 'no'}")
    results = []
    for column in zip(*recovered):
        results.append(mp.mpc(median([w.real for w in column]),
                              median([w.imag for w in column])))
    error = max(abs(results[0]-f1), abs(results[1]-f3))
    print("maximum |own L at sampled ordinate| =", mp.nstr(max(residuals), 8))
    print("minimum |other primitive L| =", mp.nstr(min(cross_values), 9))
    print("minimum |own primitive L derivative| =", mp.nstr(min(slopes), 9))
    print("maximum two-sided probe error relative to specified coefficient =",
          mp.nstr(max(probe_errors), 8))
    print("maximum clean residue error including added noise =", mp.nstr(max(clean_errors), 8))
    print("coordinatewise complex medians f(1), f(3) =",
          ", ".join(format_complex(w) for w in results))
    print("maximum complex recovery error =", mp.nstr(error, 8))
    print("deterministic tolerance at clean residue error <= 1e-6:",
          mp.nstr(2*mp.sqrt(2)*EPS, 8))
    assert min(cross_values) > mp.mpf("1e-5") and min(slopes) > mp.mpf("1e-5")
    assert max(probe_errors) < mp.mpf("1e-13") and max(clean_errors) <= EPS
    assert error <= 2 * mp.sqrt(2) * EPS


if __name__ == "__main__":
    main()
