#!/usr/bin/env python3
"""Fresh scalar half-binomial arithmetic; no saved program or DAG is read."""
from math import comb
from pathlib import Path
import hashlib
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    q, R, prime, power = 27, 1223, 3, 12
    r = (R - 1) // 2
    X = 1 << R
    # Exact integers: a direct binomial sum, with no modular recurrence.
    numerator = sum(comb(2 * r, r + j) * pow(X, j) for j in range(r + 1))
    need(numerator % 2 == 0, 'half numerator integral')
    Y = numerator // 2
    quotient = Y
    valuation = 0
    while quotient % prime == 0:
        quotient //= prime
        valuation += 1
    need(valuation == 9, 'exact ternary valuation')
    need(q >= 16 and 3 * q + 1 <= R < q ** 4 and R % 4 == 3, 'kernel range')
    need(Y % (q ** 3) == 0 and Y // (q ** 3) > 0, 'retained scale')
    need(X % q != 0, 'missing X divisibility')

    # Independent prime-adic binomial recurrence. Unit denominators only
    # are inverted. No exact binomial coefficient from above is reused.
    modulus = prime ** power
    xmod = pow(2, R, modulus)
    unit, exponent, accumulated = 1, 0, 1
    for j in range(1, r + 1):
        top, bottom = 2 * r - j + 1, j
        while top % prime == 0:
            top //= prime
            exponent += 1
        while bottom % prime == 0:
            bottom //= prime
            exponent -= 1
        need(exponent >= 0, 'binomial valuation nonnegative')
        unit = unit * top * pow(bottom, -1, modulus) % modulus
        coefficient = unit * pow(prime, exponent, modulus) % modulus
        accumulated = (accumulated * xmod + coefficient) % modulus
    ymod = accumulated * pow(2, -1, modulus) % modulus
    need(ymod == Y % modulus and ymod % (prime ** 10) != 0, 'independent residue')
    pins = {}
    for name in ('pell_kernel_half_binomial42.md', 'complete83_bounded_marker_complement_obstruction.md'):
        p = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue') / name
        pins[name] = hashlib.sha256(p.read_bytes()).hexdigest()
    out = {
        'status': 'PASS', 'q': q, 'R': R, 'r': r,
        'valuation_3_Y': valuation, 'Y_bits': Y.bit_length(),
        'Y_hex_sha256': hashlib.sha256(format(Y, 'x').encode()).hexdigest(),
        'modulus': modulus, 'Y_modulus': ymod, 'X_mod_q': X % q,
        'scale_quotient_bits': (Y // (q ** 3)).bit_length(),
        'dependency_sha256': pins,
        'helper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'scope': 'Scalar kernel counterexample only; no compiler masks, outer rows or full Pell tuple materialized.',
        'saved_program_or_source_array_execution': False,
    }
    data = (json.dumps(out, indent=2, sort_keys=True) + '\n').encode()
    p = Path('/tmp/unscaled_x_odd_kernel_root_checks.json')
    if p.exists():
        need(p.read_bytes() == data, 'receipt reproduction')
    else:
        p.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()
