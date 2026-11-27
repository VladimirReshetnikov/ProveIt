#!/usr/bin/env python3
"""Reproduce the small signed zero example using mpmath 1.3.0.

Run: python signed_zeros_mod5.py > signed_zeros_mod5.json
A sign-change scan plus high-precision refinement illustrates the theorem.
It does not certify a zero count or enclose the roots by interval arithmetic.
"""
import json
from mpmath import mp

mp.dps = 45
HEIGHT = 10
STEP = mp.mpf("0.25")

# Reference values displayed by the LMFDB; rounded to 14 decimal places.
REFERENCES = {
    "5.2": ["-9.44293112972851", "-4.13290370521285", "6.18357819545085", "8.45722917442323"],
    "5.3": ["-8.45722917442323", "-6.18357819545085", "4.13290370521285", "9.44293112972851"],
}


def scan(label, chi2):
    coefficients = [0, 1, chi2, -chi2, -1]
    gauss = mp.fsum(coefficients[a] * mp.expj(2 * mp.pi * a / 5) for a in range(5))
    epsilon = gauss / (mp.j * mp.sqrt(5))  # both characters are odd
    half_argument = mp.arg(epsilon) / 2

    def l_value(t):
        return mp.dirichlet(mp.mpc(mp.mpf("0.5"), t), coefficients)

    def hardy(t):
        gamma_phase = mp.im(mp.loggamma(mp.mpc(mp.mpf("0.75"), t / 2)))
        theta = (t / 2) * mp.log(5 / mp.pi) + gamma_phase - half_argument
        value = mp.expj(theta) * l_value(t)
        if abs(mp.im(value)) > mp.mpf("1e-35"):
            raise ArithmeticError("Hardy value has an anomalous imaginary part")
        return mp.re(value)

    roots = []
    left = mp.mpf(-HEIGHT)
    previous = hardy(left)
    while left < HEIGHT:
        right = left + STEP
        current = hardy(right)
        if current == 0:
            roots.append(right)
        elif current * previous < 0:
            root = mp.findroot(hardy, (left, right), tol=mp.mpf("1e-38"))
            if not left < root < right:
                raise ArithmeticError("Iteration escaped its sign-change bracket")
            roots.append(root)
        left, previous = right, current

    reference = list(map(mp.mpf, REFERENCES[label]))
    errors = [abs(root - ref) for root, ref in zip(roots, reference)]
    if len(roots) != len(reference) or max(errors) > mp.mpf("5.1e-15"):
        raise ArithmeticError("Scan disagrees with tabulated reference values")

    return roots, {
        "LMFDB": "https://www.lmfdb.org/L/1/5/" + label + "/r1/0/0",
        "chi_at_2": "+i" if chi2 == mp.j else "-i",
        "signed_ordinates_in_scan": [mp.nstr(root, 25) for root in roots],
        "max_L_residual": mp.nstr(max(abs(l_value(root)) for root in roots), 4),
    }


def main():
    plus, plus_summary = scan("5.2", mp.j)
    minus, minus_summary = scan("5.3", -mp.j)
    mismatch = max(abs(a + b) for a, b in zip(plus, reversed(minus)))
    if mismatch > mp.mpf("1e-35"):
        raise ArithmeticError("The independently computed spectra fail reflection")
    print(json.dumps({
        "precision_decimal_digits": mp.dps,
        "height": HEIGHT,
        "scan_step": str(STEP),
        "character_5.2": plus_summary,
        "character_5.3": minus_summary,
        "reflection_check_absolute_error_below": "1e-35",
        "verification": "Numerical sign changes and LMFDB agreement. No interval certification.",
    }, indent=2))


if __name__ == "__main__":
    main()
