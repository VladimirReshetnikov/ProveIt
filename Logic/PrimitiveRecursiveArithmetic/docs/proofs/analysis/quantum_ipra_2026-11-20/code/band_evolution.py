#!/usr/bin/env python3
"""Certified vacuum return probability for an infinite band Hamiltonian.

H e_j = (j+1/2)^2 e_j + g(e_{j+1} + e_{j-1}), with e_{-1}=0.
Only Python's standard library is needed. All computed enclosures are rational.
"""

from argparse import ArgumentParser
from fractions import Fraction as Q
from math import ceil


def choose_order(scale, tolerance, prefactor, geometric):
    """Bound a factorial tail with a finite search and exact comparisons.

    In geometric mode the first omitted term must have index at least
    2*scale; all following terms then have consecutive ratio at most 1/2.
    """
    k = tolerance.denominator.bit_length()
    end = 4 * ceil(scale) + k + prefactor.numerator.bit_length() + 3
    term = Q(1)
    for order in range(1, end + 1):
        term *= scale / order
        if (not geometric or order >= 2 * scale) and prefactor * term <= tolerance:
            return order, prefactor * term
    raise AssertionError("finite budget from the exponential tail estimate")


def return_probability(bits=14, time=Q(1, 2), coupling=Q(1, 4)):
    """Return a closed rational interval for |<e_0, exp(-itH)e_0>|^2."""
    if bits < 0:
        raise ValueError("bits must be nonnegative")
    time, coupling = Q(time), Q(coupling)
    budget = Q(1, 2 ** (bits + 4))
    perturbation = 2 * abs(coupling)
    order, cutoff_error = choose_order(
        abs(time) * perturbation, budget, Q(2), geometric=False
    )
    size = 1 + order
    diagonal = [(Q(j) + Q(1, 2)) ** 2 for j in range(size)]
    norm_bound = diagonal[-1] + perturbation
    first_omitted, series_error = choose_order(
        abs(time) * norm_bound, budget, Q(2), geometric=True
    )

    # All powers H^r e_0 are real. Collect the four phases (-i)^r
    # separately and include the factor t^r/r! in the vector recurrence.
    term = [Q(1)] + [Q(0)] * (size - 1)
    real, imag = Q(1), Q(0)
    for r in range(1, first_omitted):
        next_term = []
        for j, energy in enumerate(diagonal):
            value = energy * term[j]
            if j:
                value += coupling * term[j - 1]
            if j + 1 < size:
                value += coupling * term[j + 1]
            next_term.append(value * time / r)
        term = next_term
        phase = r % 4
        if phase == 0:
            real += term[0]
        elif phase == 1:
            imag -= term[0]
        elif phase == 2:
            real -= term[0]
        else:
            imag += term[0]

    eta = cutoff_error + series_error
    center = real * real + imag * imag
    # The exact amplitude has modulus at most 1 by unitarity.
    radius = eta * (2 + eta)
    low, high = max(Q(0), center - radius), min(Q(1), center + radius)
    assert 0 <= low <= high <= 1 and high - low <= Q(1, 2 ** bits)
    return low, high, size, first_omitted


def outward_decimal(value, digits, upward):
    """Render a rational with an outward-rounded terminating decimal."""
    scale = 10 ** digits
    numerator = value.numerator * scale
    integer = -(-numerator // value.denominator) if upward else numerator // value.denominator
    return f"{integer // scale}.{integer % scale:0{digits}d}"


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--bits", type=int, default=14)
    parser.add_argument("--time", type=Q, default=Q(1, 2))
    parser.add_argument("--coupling", type=Q, default=Q(1, 4))
    args = parser.parse_args()
    lo, hi, size, first_omitted = return_probability(args.bits, args.time, args.coupling)
    digits = args.bits + 3
    print(f"Vacuum return probability at t={args.time}, g={args.coupling}")
    print(f"[{outward_decimal(lo, digits, False)}, {outward_decimal(hi, digits, True)}]")
    print(f"{size} energy levels, Taylor degree {first_omitted - 1}")
