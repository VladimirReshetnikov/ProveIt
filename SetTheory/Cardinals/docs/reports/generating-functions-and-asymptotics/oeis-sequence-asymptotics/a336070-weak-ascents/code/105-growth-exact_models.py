"""Exact finite models for report105 (Python standard library only).

These finite checks detect algebra/data errors. They are not proofs of the
asymptotic theorems, uniform estimates, or transcendental inequalities.
All mathematical arithmetic in this module uses integers or Fraction.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, factorial
import json

SCHEMA = "report105-exact-certificate-v1"
MAX_N = 500
POLYNOMIAL_N = 16
BRUTE_N = 7
FIXED_D = (0, 1, 2, 5)
MATRIX_M = (1, 2, 3, 5, 8)
MATRIX_R = ("1/2", "2/3", "1", "3/2", "2")
POWER_B = (0, 1, 2, 4)
SHIFT_D = (0, 1, 2, 5, 30)
POISSON_M = (1, 2, 3, 5, 8, 16)
POISSON_R = ("1/5", "1/2", "2/3", "9/10", "99/100")
OEIS_INITIAL = (1, 1, 2, 6, 23, 106, 567, 3440, 23286, 173704,
    1414102, 12465119, 118205428, 1199306902, 12958274048,
    148502304614, 1798680392716, 22953847041950, 307774885768354,
    4325220458515307, 63563589415836532, 974883257009308933,
    15575374626562632462, 258780875395778033769, 4464364292401926006220)

class CheckFailure(Exception):
    """A failed exact identity, data comparison, or certificate validation."""


def require(condition, message):
    if not condition:
        raise CheckFailure(message)


def rational_text(value):
    value = F(value)
    if value.denominator == 1:
        return str(value.numerator)
    return str(value.numerator) + "/" + str(value.denominator)


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode("ascii")


def inventory():
    return {
        "positive_recurrence_lengths": list(range(MAX_N + 1)),
        "children_identity_lengths": list(range(1, MAX_N)),
        "polynomial_lengths": list(range(POLYNOMIAL_N + 1)),
        "fixed_d": list(FIXED_D),
        "brute_force_lengths": list(range(BRUTE_N + 1)),
        "fixed_d_children_lengths": list(range(1, BRUTE_N)),
        "frozen_cases": [{"M": M, "r": r} for M in MATRIX_M for r in MATRIX_R],
        "matrix_power_exponents": list(POWER_B),
        "shift_parameters": list(SHIFT_D),
        "poisson_cases": [{"M": M, "r": r} for M in POISSON_M for r in POISSON_R],
    }


def polynomial_recurrence(n_max=POLYNOMIAL_N):
    """Compute g_n = sum_j u^(j+1)(1-u)^(j-1) g_(n-j)^(j)/j!.

    Coefficients of the divided derivative are binomial(t,j)*g[t],
    so division introduces no floating arithmetic and no CAS is needed.
    """
    polynomials = [[0, 1]]
    for n in range(1, n_max + 1):
        result = [0] * (n + 2)
        for j in range(1, n + 1):
            source = polynomials[n - j]
            for t in range(j, len(source)):
                derivative_coefficient = source[t] * comb(t, j)
                for k in range(j):
                    degree = t + 1 + k
                    require(degree < len(result), "polynomial degree bound")
                    result[degree] += derivative_coefficient * comb(j - 1, k) * (-1) ** k
        require(all(x >= 0 for x in result), "negative formal coefficient")
        polynomials.append(result)
    return polynomials


def state_recurrence(d, n_max=BRUTE_N):
    """Independent explicit state transitions for general fixed d."""
    layers = [{}, {(0, 0): 1}]
    for n in range(1, n_max):
        new = {}
        for (K, L), count in layers[n].items():
            for j in range(K + 2):
                nxt = (K + int(j > L - d), j)
                require(0 <= nxt[1] <= nxt[0] <= n, "fixed-d support")
                new[nxt] = new.get(nxt, 0) + count
        layers.append(new)
    return layers


def brute_force(d, n):
    """Filter ALL inversion sequences, recomputing each prefix statistic.

    This deliberately avoids using the generating-tree transition recurrence.
    """
    if n == 0:
        return {}
    result = {}
    for sequence in product(*(range(i) for i in range(1, n + 1))):
        valid = True
        for i in range(1, n):
            previous_ascents = sum(sequence[t + 1] > sequence[t] - d for t in range(i - 1))
            if sequence[i] > 1 + previous_ascents:
                valid = False
                break
        if valid:
            K = sum(sequence[t + 1] > sequence[t] - d for t in range(n - 1))
            state = (K, sequence[-1])
            result[state] = result.get(state, 0) + 1
    return result


def encode_states(states):
    return [[K, L, count] for (K, L), count in sorted(states.items())]


def matrix_case(M, r_text):
    r = F(r_text)
    v = r ** (-M)
    lam = F(M) if r == 1 else (v - 1) / (1 - r)
    return {"M": M, "r": r_text, "v": rational_text(v),
        "lambda": rational_text(lam), "f": [rational_text(r ** l) for l in range(M)]}


def poisson_case(M, r_text):
    """Rational forms of b/q, c/q, h/q for q=-M log(r)>0.

    No numerical logarithm is evaluated. The constant q cancels from every
    identity recorded here. The displayed h value at l=M is a seam value,
    not an extra Markov-chain state.
    """
    r = F(r_text)
    require(0 < r < 1, "Poisson r must lie strictly between zero and one")
    B = r / (1 - r)
    D = 1 - r ** M
    b = [(F(l) + B - (M + B) * r ** (M - l)) / (M * D) for l in range(M)]
    c = (F(M * (M - 1), 2) + M * B - (M + B) * B * D) / (M * M * D)
    h = [(c / B + 1 / (2 * M * D * B)) * l - F(l * l) / (2 * M * D * B)
         for l in range(M + 1)]
    return {"M": M, "r": r_text, "b_over_q": list(map(rational_text, b)),
        "c_over_q": rational_text(c), "h_over_q": list(map(rational_text, h)),
        "mean_W": rational_text(B/M - r**M/D),
        "wrap_losses": [rational_text(F(k*(k-1), 2*M*M)) for k in range(M)]}


def expected_certificate(terms_bytes):
    fixed = []
    for d in FIXED_D:
        layers = state_recurrence(d)
        fixed.append({"d": d,
            "counts": [1] + [sum(layer.values()) for layer in layers[1:]],
            "state_layers": [encode_states(layer) for layer in layers]})
    return {"schema": SCHEMA,
        "scope": "Finite exact checks only; not an analytic asymptotic proof.",
        "inventory": inventory(),
        "terms": {"file": "weak_ascent_terms.txt", "sha256": sha256(terms_bytes).hexdigest(),
                  "first_n": 0, "last_n": MAX_N, "line_count": MAX_N + 1},
        "initial_terms": list(OEIS_INITIAL),
        "polynomials": polynomial_recurrence(),
        "fixed_d_cases": fixed,
        "frozen_cases": [matrix_case(M, r) for M in MATRIX_M for r in MATRIX_R],
        "poisson_cases": [poisson_case(M, r) for M in POISSON_M for r in POISSON_R]}
