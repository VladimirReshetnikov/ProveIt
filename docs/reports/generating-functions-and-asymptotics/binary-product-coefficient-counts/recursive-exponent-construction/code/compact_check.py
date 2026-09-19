#!/usr/bin/env python3
"""Inspectably small, independent exact check of the first 20 factors."""

if not __debug__:
    raise RuntimeError("Run without -O: this verifier uses assertions.")

def check(blocks=10):
    if not 1 <= blocks <= 15:
        raise ValueError("choose 1..15 blocks for this dense checker")
    a0, a1 = 2, 1
    main_total = 0
    polynomial = [1]
    observed = [1]
    predicted = [1]

    for n in range(1, blocks + 1):
        a = a1
        b = main_total + 2**n - 1 + a
        assert b > 0
        for exponent in (2**(n - 1), b):
            next_polynomial = [0] * (len(polynomial) + exponent)
            for j, coefficient in enumerate(polynomial):
                next_polynomial[j] += coefficient
                next_polynomial[j + exponent] += coefficient
            polynomial = next_polynomial
            observed.append(polynomial.count(1))

        predicted.extend((2 if n == 1 else 4,
                          4 if n == 1 else 4 + 4 * (a > 0)))
        main_total += b
        a0, a1 = a1, a1 - 2*a0

    assert observed == predicted
    return observed

if __name__ == "__main__":
    print(check())
