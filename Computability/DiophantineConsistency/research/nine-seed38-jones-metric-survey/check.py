#!/usr/bin/env python3
"""Source-pinned external degree-arithmetic proposal; no Lean or large constants.

The named degree recurrence below is manually transcribed from the pinned
Jones sources. This script checks its arithmetic, not the transcription.
"""
import hashlib
import json
import math
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE = Path(__file__).resolve().parent
D = HERE.parent.parent
PINS = {
    'Lean/DiophantineConsistency/ExecutableJonesCore.lean': '89832bbdcfcde58747c535a12a37d9ad76d3ca3298a30c00c9b9cfe7eaff1ec4',
    'Lean/DiophantineConsistency/JonesSyntaxCore.lean': 'f79661e08bf9bc1a15a88f6c6e433542e9f7808c4dc88066b7fdac424b211384',
    'Lean/DiophantineConsistency/Representation.lean': '1b1a20d42422b0fffe2fb25ad4423c4914a0fcd1a0ccafcd1abdfcf863da92b7',
    'Lean/DiophantineConsistency/QuarticSyntaxCore.lean': 'e7b4e5256523bec1dea0f9fd4ca670d403b24df419d568fb4ba07136b5eb80f9',
    'Lean/DiophantineConsistency/SyntaxCoefficients.lean': 'cad2c498522aca13bc656b25c5cfe466fea8c750a9626c8be17ca9e87e769dbb',
    'research/nine-sharing-seed38-weighted-retry/src/DiophantineConsistency/SharingSeed38Syntax.lean': '9bde9c1eeaeda37dd59c097bcec2eb90df76ba07aa5a7e349ebe3eeae4b2e445',
    'research/nine-sharing-norm38-ipra-endpoint-check/src/DiophantineConsistency/Norm38IPRAEndpoint.lean': 'fe84dc25c6d4bb7c7ebfa06d1ff28d622f607c58dc1a4338214e0a40314a7f0c',
}
for name, expected in PINS.items():
    actual = hashlib.sha256((D / name).read_bytes()).hexdigest()
    if actual != expected:
        raise RuntimeError(('source changed', name, actual, expected))


class Deg:
    """Upper bound on total degree; zero is conservative for any constant."""
    def __init__(self, n):
        if type(n) is not int or n < 0:
            raise ValueError(n)
        self.n = n
    def __add__(self, other):
        return Deg(max(self.n, bound(other)))
    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__
    def __mul__(self, other):
        return Deg(self.n + bound(other))
    __rmul__ = __mul__
    def __pow__(self, exponent):
        if type(exponent) is not int or exponent < 0:
            raise ValueError(exponent)
        return Deg(self.n * exponent)


def bound(value):
    if isinstance(value, Deg):
        return value.n
    if type(value) is int:
        return 0
    raise TypeError(type(value))


def propagate(nu):
    if nu < 1:
        raise ValueError('this recurrence uses the nonempty lExpression case')
    L = 5 ** (nu + 1)
    variable = Deg(1)
    # removeInput makes x the constant 1. All nine surviving variables are
    # bounded by degree 1; z, y and all seed-derived coefficients are constants.
    x, z, y = 1, 1, 1
    b = x * y + 1 + variable
    B = b ** 5
    q = B ** L
    N = q ** 16
    # For every natural exponent vector, L - expo(k) <= L. The nonempty
    # prefix list for l has maximal exponent 5^nu. Lambda ends at 4L-1.
    e = Deg(B.n * L)
    ell = Deg(B.n * (5 ** nu))
    lam = Deg(B.n * (4 * L - 1))
    g = variable + 1
    theta = B - 2 * z
    R = (g + e * q ** 3 + ell * q ** 5 +
         (2 * (e - z * lam) * (1 + x * B + g) ** 4 + lam * B +
          lam * B * q ** 4) * q ** 7) * (N ** 2 - N) + \
        (q ** 3 - b * ell + ell + theta * lam * q ** 3 +
         (B - 2) * q ** 8) * (N ** 2 - 1)
    G = 32 * b * B ** (5 ** nu)
    h = variable + 1
    s = variable + 1
    w = variable + 1
    phi = variable
    i = variable + 1
    j = variable + 1
    t = variable
    U = N ** 2 * w
    Y = N ** 2 * s
    M = R * Y
    P = 2 * M ** 2 * U
    K = R + 1 + h * (P - 1)
    A = M * (U + 1)
    Bprime = 2 * R + 1
    W = b * w
    C = Bprime + W + phi
    J = 4 * A - 5
    Q = 3 * W * C - 2 * (W ** 2 - 1)
    D0 = (A ** 2 - 1) * C ** 2 + 1
    E = i * J * D0 * C ** 2
    F = (A ** 2 - 1) * E ** 2 + 1
    Gp = A + F * (C * D0 + 1 - A)
    H = Bprime + j * C
    I = (Gp ** 2 - 1) * H ** 2 + 1
    A0 = (P ** 2 - 1) * K ** 2 + 1
    A1 = D0 * F * I
    V0 = A0 ** 2 + 2
    V1 = A1 ** 2 + 2
    divisor = (J * F) ** 2
    dividend = (Q * F + J * (H - C)) ** 2
    margin = K ** 2 * G - 4 * (C - K * Y) ** 2 * G - 8 * g * K ** 2
    Kc = divisor * (2 * margin - 1)
    T = divisor * t + dividend - Kc * (dividend + V0 * V1)
    result = (T ** 2 + Kc ** 2 * A0 - Kc ** 2 * V0 ** 2 * A1) ** 2 - \
        4 * T ** 2 * Kc ** 2 * A0
    return L, {key: value.n for key, value in locals().copy().items()
               if isinstance(value, Deg)}


# Small parameter controls check the derived closed form; they are not
# tests of the source-to-recurrence transcription or of exact degree.
for nu in range(1, 9):
    L, degree = propagate(nu)
    if degree['result'] != 291404 * L + 860:
        raise RuntimeError(('unexpected recurrence', nu, degree['result']))
L, degrees = propagate(38)
print(json.dumps({
    'status': 'CANDIDATE_EXTERNAL_UPPER_BOUND_PENDING_INDEPENDENT_TRANSCRIPTION_REVIEW',
    'scope': 'Manually transcribed degree upper-bound recurrence over pinned sources; no Lean theorem, coefficient expansion, exact degree, operation count, or literal graph binding.',
    'nu': 38,
    'L': str(L),
    'candidate_bound_formula': '291404 * 5^39 + 860',
    'candidate_bound': str(degrees['result']),
    'degree_bounds': {key: str(val) for key, val in sorted(degrees.items())},
    'star_enumeration_vectors': str(5 ** 40),
    'star_vectors_with_coordinate_sum_4': math.comb(43, 4),
    'lambda_range_terms': str(4 * L),
    'source_sha256': PINS,
    'controls': 'recurrence checked for nu=1,...,8 against its stated closed form',
}, indent=2, sort_keys=True))
