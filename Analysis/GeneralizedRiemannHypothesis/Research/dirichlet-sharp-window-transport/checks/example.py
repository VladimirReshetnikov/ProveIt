#!/usr/bin/env python3
"""Numerical illustration of sharp-window transport for the completed zeta function.

Tested with Python 3.12 and mpmath 1.3.0 (pip install mpmath==1.3.0).
Run: python example.py > example.json
This is floating-point numerical evidence. No rigorous enclosures are computed.
"""
import json

import mpmath as mp


def arch_derivative(t):
    """Derivative of log |s(s-1) Gamma(s/2)|, s = 1/2 + it."""
    return 2*t/(t*t + mp.mpf("0.25")) - mp.im(mp.digamma(mp.mpc("0.25", t/2)))/2


def g(t):
    return mp.siegelz(t, derivative=1)/mp.siegelz(t) + arch_derivative(t)


def shifted_root(left, right, shift):
    # The pole-free equation is Z' + (arch_derivative + shift) Z = 0.
    def eq(t):
        return mp.siegelz(t, derivative=1) + (arch_derivative(t) + shift)*mp.siegelz(t)

    assert eq(left)*eq(right) < 0
    root = mp.findroot(eq, (left, right), solver="illinois", tol=mp.mpf("1e-24"),
                       maxsteps=100)
    assert left < root < right
    assert abs(g(root) + shift) < mp.mpf("1e-20")
    return root


def model(t):
    scale = mp.log(t/(2*mp.pi))/2
    drift = -mp.pi/4
    return (mp.atan((1+drift)/scale) - mp.atan(drift/scale))/mp.pi


def display(x):
    return mp.nstr(x, 15)


def main():
    mp.mp.dps = 34
    block_limits = [1, 8, 16, 24]
    zeros = {k: mp.im(mp.zetazero(k)) for k in range(1, max(block_limits)+1)}
    rows = []
    lengths = {}
    for k in range(1, max(block_limits)):
        left, right = zeros[k], zeros[k+1]
        old = shifted_root(left, right, 0)
        new = shifted_root(left, right, 1)
        assert left < old < new < right
        assert -1 < g((old+new)/2) < 0
        lengths[k] = new-old
        rows.append({"k": k, "left_zeta_zero": display(left),
                     "right_zeta_zero": display(right), "g_eq_0": display(old),
                     "g_eq_minus_1": display(new), "occupation": display(new-old)})

    windows = []
    for start, end in zip(block_limits, block_limits[1:]):
        exact_model = mp.quad(model, [zeros[start], zeros[end]])
        observed = mp.fsum(lengths[k] for k in range(start, end))
        # Independent check against the complex log derivative of the completion.
        t = (zeros[start] + zeros[start+1])/2
        s = mp.mpc("0.5", t)
        complex_g = mp.j*(1/s + 1/(s-1) - mp.log(mp.pi)/2 + mp.digamma(s/2)/2
                            + mp.zeta(s, derivative=1)/mp.zeta(s))
        assert abs(complex_g-g(t)) < mp.mpf("1e-25")
        windows.append({"zero_indices": [start, end], "T_min": display(zeros[start]),
                        "T_max": display(zeros[end]), "observed": display(observed),
                        "integrated_model": display(exact_model),
                        "observed_minus_model": display(observed-exact_model)})

    print(json.dumps({"method": "Floating-point illustration using consecutive positive "
                      "zeta-zero gaps, scalar A=0, B=1; no interval certification.",
                      "decimal_working_precision": mp.mp.dps, "mpmath": mp.__version__,
                      "windows": windows, "gaps": rows}, indent=2))


if __name__ == "__main__":
    main()
