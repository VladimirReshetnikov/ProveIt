#!/usr/bin/env python3
"""Exact algebra companion to Report145; Python standard library only.

This program checks algebraic identities, not the analytic asymptotic proof.
No assertions are used: all validations remain active under python -O.
"""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import sys
from fractions import Fraction as F


class CheckError(Exception):
    """Invalid fixture, failed exact identity, or unsafe output destination."""


def require(condition, message):
    if not condition:
        raise CheckError(message)


def object_keys(value, keys, where):
    require(type(value) is dict, where + ": expected an object")
    require(set(value) == set(keys), where + ": unknown or missing keys")


def integer(value, where):
    require(type(value) is int, where + ": expected an integer, not bool/float")
    return value


def fraction(value, where):
    object_keys(value, ("numerator", "denominator"), where)
    n = integer(value["numerator"], where + ".numerator")
    d = integer(value["denominator"], where + ".denominator")
    require(d > 0, where + ": denominator must be positive")
    require(math.gcd(n, d) == 1, where + ": fraction is not canonical")
    return F(n, d)


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def reject_number(text):
    raise CheckError("JSON floats and nonfinite numbers are forbidden: " + text)


COVARIANCE_KEYS = ("int_v2", "int_complement2", "int_product", "covariance", "normalized_covariance")
COEFFICIENT_KEYS = ("p", "d", "q", "s", "eLog", "zLog", "hLog", "first", "logarithmic")
IDENTITY_KEYS = ("cubic_telescope", "weighted_telescope", "quartic_telescope", "constant_forcing", "linear_forcing", "reciprocal_forcing", "operator_h", "operator_h_previous", "operator_tail")
SECOND_KEYS = ("Asecond", "Isecond", "bsecond", "Hsecond", "aSecond", "Dfirst", "normalizationShift", "inverseKshift")
ANALYTIC_KEYS = ("TlogConstant", "TgConstant", "Treciprocal")
AFFINE_KEYS = ("rational", "gamma", "Sa", "Sy", "K", "Q")
RATIO_KEYS = ("first", "second", "difference")
FRACTION_SECTIONS = (("covariance", COVARIANCE_KEYS), ("coefficients", COEFFICIENT_KEYS),
                     ("identities", IDENTITY_KEYS), ("second_coefficients", SECOND_KEYS),
                     ("analytic_inputs", ANALYTIC_KEYS), ("h_constant", AFFINE_KEYS),
                     ("b2_affine", AFFINE_KEYS), ("ratio", RATIO_KEYS))


def load_fixture(path):
    try:
        raw = Path(path).read_bytes()
        require(len(raw) <= 65536, "fixture exceeds 65536 bytes")
        data = json.loads(raw.decode("utf-8"), object_pairs_hook=no_duplicates,
                          parse_float=reject_number, parse_constant=reject_number)
    except (OSError, UnicodeError, ValueError, RecursionError) as exc:
        raise CheckError("cannot read valid UTF-8 JSON fixture: " + str(exc)) from exc
    object_keys(data, ("schema", "inverse_residual") + tuple(name for name, keys in FRACTION_SECTIONS), "fixture")
    require(type(data["schema"]) is str and data["schema"] == "report145-exact-v2", "unsupported fixture schema")
    parsed = {}
    for section, keys in FRACTION_SECTIONS:
        object_keys(data[section], keys, section)
        parsed[section] = {key: fraction(data[section][key], section + "." + key) for key in keys}
    inverse = data["inverse_residual"]
    object_keys(inverse, ("order", "terms"), "inverse_residual")
    require(integer(inverse["order"], "inverse_residual.order") == 4, "inverse residual order must be 4")
    require(type(inverse["terms"]) is list, "inverse_residual.terms must be an array")
    require(len(inverse["terms"]) <= 32, "too many inverse residual terms")
    terms = {}
    previous = None
    for index, term in enumerate(inverse["terms"]):
        where = "inverse_residual.terms[" + str(index) + "]"
        object_keys(term, ("t", "log", "lambda_inverse", "k", "coefficient"), where)
        key = tuple(integer(term[name], where + "." + name) for name in ("t", "log", "lambda_inverse", "k"))
        require(1 <= key[0] <= 4 and all(0 <= exponent <= 4 for exponent in key[1:]), where + ": exponent out of range")
        require(previous is None or previous < key, where + ": terms must be unique and lexicographically sorted")
        coefficient = fraction(term["coefficient"], where + ".coefficient")
        require(coefficient != 0, where + ": zero terms must be omitted")
        terms[key] = coefficient
        previous = key
    parsed["inverse_residual"] = terms
    canonical = json.dumps(data, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")
    return parsed, hashlib.sha256(canonical).hexdigest()


# Univariate rational polynomials, coefficients in increasing degree order.
def poly(values):
    result = [F(v) for v in values]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return tuple(result or [F(0)])


def padd(a, b):
    return poly((a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b))))


def pneg(a):
    return poly(-v for v in a)


def pmul(a, b):
    result = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return poly(result)


def integral(a):
    return sum((v / (i + 1) for i, v in enumerate(a)), F(0))


class Rational:
    """Formal rational functions in n; equality uses cross multiplication."""

    def __init__(self, numerator, denominator=(1,)):
        self.n = poly(numerator)
        self.d = poly(denominator)
        require(self.d != (F(0),), "zero polynomial denominator")

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Rational) else Rational((F(value),))

    def __add__(self, other):
        other = self.coerce(other)
        return Rational(padd(pmul(self.n, other.d), pmul(other.n, self.d)), pmul(self.d, other.d))

    __radd__ = __add__

    def __neg__(self):
        return Rational(pneg(self.n), self.d)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        other = self.coerce(other)
        return Rational(pmul(self.n, other.n), pmul(self.d, other.d))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.coerce(other)
        return Rational(pmul(self.n, other.d), pmul(self.d, other.n))

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def equals(self, other):
        other = self.coerce(other)
        return pmul(self.n, other.d) == pmul(other.n, self.d)


def rational_checks():
    n = Rational((0, 1))
    den = (n + 1) * (n + 2) * (n + 3)
    cubic_tail = 1 / (2 * (n + 1) * (n + 2))
    cubic_tail_next = 1 / (2 * (n + 2) * (n + 3))
    quartic_tail = 1 / (3 * (n + 1) * (n + 2) * (n + 3))
    quartic_tail_next = 1 / (3 * (n + 2) * (n + 3) * (n + 4))
    # For h_k = 1, k+1, 1/(k+4), respectively, the telescopes give exact T h.
    # Every entry below is an identity residual, identically zero in n.
    return {
        "cubic_telescope": cubic_tail - cubic_tail_next - 1 / den,
        "weighted_telescope": 1 / (n + 2) - 1 / (n + 3) - (n + 1) / den,
        "quartic_telescope": quartic_tail - quartic_tail_next - 1 / (den * (n + 4)),
        "constant_forcing": 1 / (n + 2) - 2 * (n + 1) * cubic_tail,
        "linear_forcing": n / (n + 2) - 2 * (n + 1) / (n + 2) + 1,
        "reciprocal_forcing": 1 / ((n + 3) * (n + 2)) - 2 * (n + 1) * quartic_tail - 1 / (3 * (n + 2) * (n + 3)),
        # Substitute S_{n+1}=S_n-h_n/den into T. These three independent
        # coefficients check (n+1)y_{n+1}-(n+2)y_n=h_n-h_{n-1}.
        "operator_h": (n + 1) / (n + 3) + 2 * (n + 1) * (n + 2) / den - 1,
        "operator_h_previous": -(n + 2) / (n + 2) + 1,
        "operator_tail": -2 * (n + 1) * (n + 2) + 2 * (n + 2) * (n + 1),
    }


# Truncated formal polynomials in t=1/x, ell=log x, u=1/lambda, and k.
# Keys give the four degrees in that order. No numerical logarithms.
ORDER = 4


def sadd(*series):
    result = {}
    for item in series:
        for key, value in item.items():
            result[key] = result.get(key, F(0)) + value
    return {key: value for key, value in result.items() if value}


def scale(series, coefficient):
    return {key: value * coefficient for key, value in series.items() if value * coefficient}


def smul(a, b):
    result = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(x + y for x, y in zip(ka, kb))
            if key[0] <= ORDER:
                result[key] = result.get(key, F(0)) + va * vb
    return {key: value for key, value in result.items() if value}


def monomial(t=0, ell=0, u=0, k=0, coefficient=F(1)):
    return {(t, ell, u, k): F(coefficient)} if coefficient else {}


def inverse_one_plus(z):
    require(all(key[0] >= 1 for key in z), "formal reciprocal requires positive t-order")
    result, power = monomial(), monomial()
    for k in range(1, ORDER + 1):
        power = smul(power, z)
        result = sadd(result, scale(power, F((-1) ** k)))
    return result


def log_one_plus(z):
    require(all(key[0] >= 1 for key in z), "formal logarithm requires positive t-order")
    result, power = {}, monomial()
    for k in range(1, ORDER + 1):
        power = smul(power, z)
        result = sadd(result, scale(power, F((-1) ** (k + 1), k)))
    return result


def inverse_residual(b, c):
    t, ell, u = monomial(t=1), monomial(ell=1), monomial(u=1)
    logarithmic_plus_constant = sadd(scale(ell, c), monomial(k=1))
    h = sadd(scale(t, b), smul(logarithmic_plus_constant, smul(t, t)))
    # Delta=(b/x+(c log(x)+k)/x^2)/(lambda-1/(2x)).
    delta = smul(smul(h, u), inverse_one_plus(scale(smul(u, t), F(-1, 2))))
    z = smul(delta, t)
    log_shift = log_one_plus(z)
    new_inverse_x = smul(t, inverse_one_plus(z))
    new_log_x = sadd(ell, log_shift)
    new_h = sadd(scale(new_inverse_x, b), smul(sadd(scale(new_log_x, c), monomial(k=1)), smul(new_inverse_x, new_inverse_x)))
    lambda_delta = {(kt, kl, ku - 1, kk): value for (kt, kl, ku, kk), value in delta.items()}
    return sadd(lambda_delta, scale(log_shift, F(-1, 2)), scale(new_h, F(-1)))


def ratio_coefficients(b, c):
    # Here k is an arbitrary second constant B2. Work only to degree two;
    # these calculations make no claim about differences of analytic errors.
    one, t, ell = monomial(), monomial(t=1), monomial(ell=1)
    t_next = smul(t, inverse_one_plus(t))
    ell_next = sadd(ell, log_one_plus(t))
    bracket = sadd(one, scale(t, b), smul(sadd(scale(ell, c), monomial(k=1)), smul(t, t)))
    bracket_next = sadd(one, scale(t_next, b), smul(sadd(scale(ell_next, c), monomial(k=1)), smul(t_next, t_next)))
    square_root = sadd(one, scale(t, F(1, 2)), scale(smul(t, t), F(-1, 8)))
    quotient = smul(square_root, smul(bracket_next, inverse_one_plus(sadd(bracket, scale(one, F(-1))))))
    low = {key: value for key, value in quotient.items() if key[0] <= 2}
    first = low.get((1, 0, 0, 0), F(0))
    second = low.get((2, 0, 0, 0), F(0))
    require(low == sadd(one, scale(t, first), scale(smul(t, t), second)), "unexpected symbolic term in ratio")
    difference = sadd(scale(sadd(t_next, scale(t, F(-1))), first),
                      scale(sadd(smul(t_next, t_next), scale(smul(t, t), F(-1))), second))
    low_difference = {key: value for key, value in difference.items() if key[0] <= 2}
    difference_second = low_difference.get((2, 0, 0, 0), F(0))
    require(low_difference == scale(smul(t, t), difference_second), "unexpected symbolic term in ratio difference")
    return {"first": first, "second": second, "difference": difference_second}


def verify(path):
    expected, digest = load_fixture(path)
    v2 = poly((0, 0, 1))
    complement2 = poly((1, -2, 1))
    product = integral(pmul(v2, complement2))
    covariance = product - integral(v2) * integral(complement2)
    cov = {
        "int_v2": integral(v2),
        "int_complement2": integral(complement2),
        "int_product": product,
        "covariance": covariance,
        "normalized_covariance": covariance / 4,
    }
    require(cov == expected["covariance"], "covariance fixture disagrees with exact integrals")
    # Endpoint and common-factor first coefficients from their Taylor inputs.
    p = F(1, 2) - F(1, 12) - F(1, 6)
    q = -F(1) + F(1, 12) + F(1, 2)
    d = -p
    s = p * p + p * q + cov["normalized_covariance"]
    e_log = 4 * p * d + 2 * q * d + 2 * s
    z_log = 2 * d * d
    h_log = e_log + z_log
    coeff = {"p": p, "d": d, "q": q, "s": s, "eLog": e_log,
             "zLog": z_log, "hLog": h_log, "first": d + F(1, 2), "logarithmic": h_log / 3}
    require(coeff == expected["coefficients"], "correction coefficient fixture disagrees with exact arithmetic")
    a_first, i_first = F(1, 2) - F(1, 12), -F(1, 6)
    a_second = -F(1, 8) + F(1, 288) - F(1, 24)
    i_second = integral(poly((0, 0, 0, F(1, 3), F(1, 8))))
    b_second = a_second + i_second + a_first * i_first
    h_second = F(2, 3) + q * q / 2
    a_sequence_second = b_second + p * d
    d_first = -F(1, 2) * (a_first * cov["int_complement2"] - cov["int_product"] / 2)
    second = {"Asecond": a_second, "Isecond": i_second, "bsecond": b_second,
              "Hsecond": h_second, "aSecond": a_sequence_second, "Dfirst": d_first,
              "normalizationShift": d / 2 - F(1, 8), "inverseKshift": -coeff["first"] ** 2 / 2}
    require(second == expected["second_coefficients"], "second-order coefficient fixture disagrees with exact arithmetic")
    # Analytic inputs from the proved inverse asymptotics. Their rational
    # assembly is checked here, but the estimates themselves are NOT certified.
    analytic = {"TlogConstant": -F(1) + F(1) + F(1, 6),
                "TgConstant": -2 * F(1, 9), "Treciprocal": 1 - 2 * F(1, 3)}
    require(analytic == expected["analytic_inputs"], "declared analytic-input arithmetic mismatch")
    h_constant = {"rational": p - 2 * a_sequence_second + q + h_second,
                  "gamma": h_log, "Sa": 2 * d, "Sy": 2 * p + 2 * q + 2 * d,
                  "K": 2 * s, "Q": F(2)}
    require(h_constant == expected["h_constant"], "affine forcing constant mismatch")
    b2 = {name: value * analytic["Treciprocal"] for name, value in h_constant.items()}
    b2["rational"] += (2 * p * (analytic["TlogConstant"] - analytic["Treciprocal"])
                       + h_log * analytic["TgConstant"] + second["normalizationShift"])
    require(b2 == expected["b2_affine"], "affine B2 coefficient mismatch")
    ratio = ratio_coefficients(coeff["first"], coeff["logarithmic"])
    require(ratio == expected["ratio"], "formal ratio coefficient mismatch")
    identities = rational_checks()
    for name in IDENTITY_KEYS:
        require(identities[name].equals(0), "failed rational identity: " + name)
        require(identities[name].equals(expected["identities"][name]), "rational-identity fixture mismatch: " + name)
    residual = inverse_residual(coeff["first"], coeff["logarithmic"])
    require(residual == expected["inverse_residual"], "inverse formal residual fixture mismatch")
    return {
        "schema": "report145-exact-receipt-v2",
        "status": "passed",
        "scope": "Exact algebra with declared analytic inputs; no analytic asymptotic, effective-error, or decimal certification",
        "fixture_sha256": digest,
        "checks": {"covariance_values": len(cov), "correction_coefficients": len(coeff),
                   "rational_identities": len(identities), "inverse_residual_nonzero_terms": len(residual),
                   "inverse_residual_order": ORDER, "second_order_coefficients": len(second),
                   "declared_analytic_inputs": len(analytic), "forcing_affine_coefficients": len(h_constant),
                   "B2_affine_coefficients": len(b2), "formal_ratio_coefficients": len(ratio)},
        "first_correction": str(coeff["first"]),
        "logarithmic_correction": str(coeff["logarithmic"]),
        "B2_rational_part": str(b2["rational"]),
        "ratio_second_coefficient": str(ratio["second"]),
        "ratio_difference_leading_coefficient": str(ratio["difference"]),
    }


def write_new_file(path, contents):
    """Create only a new file, refusing existing targets and symlink parents.

    Traverse parents by directory descriptors and O_NOFOLLOW; this avoids a
    check-then-open symlink race on supported POSIX systems. Fail closed when
    the required OS primitives are unavailable.
    """
    require(isinstance(path, (str, os.PathLike)), "receipt path must be a path")
    path = os.fspath(path)
    require(type(path) is str and path != "", "receipt path must be nonempty text")
    require("\x00" not in path, "receipt path contains NUL")
    parts = path.split(os.sep)
    require(".." not in parts, "receipt path must not contain '..'")
    require(parts[-1] not in ("", "."), "receipt path must name a file")
    require(hasattr(os, "O_NOFOLLOW") and hasattr(os, "O_DIRECTORY") and os.open in os.supports_dir_fd,
            "safe receipt creation requires POSIX directory-descriptor support")
    parent_fd = None
    file_fd = None
    try:
        directory_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
        parent_fd = os.open(os.sep if os.path.isabs(path) else ".", directory_flags)
        for part in parts[:-1]:
            if part in ("", "."):
                continue
            next_fd = os.open(part, directory_flags, dir_fd=parent_fd)
            os.close(parent_fd)
            parent_fd = next_fd
        file_fd = os.open(parts[-1], os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o600, dir_fd=parent_fd)
        with os.fdopen(file_fd, "w", encoding="utf-8", newline="\n") as output:
            file_fd = None
            output.write(contents)
            output.flush()
            os.fsync(output.fileno())
    except OSError as exc:
        raise CheckError("refusing or unable to create receipt: " + exc.strerror) from exc
    finally:
        if file_fd is not None:
            os.close(file_fd)
        if parent_fd is not None:
            os.close(parent_fd)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=Path(__file__).with_name("fixture.json"))
    parser.add_argument("--receipt", help="Create a new receipt file; never overwrite or follow symlinks")
    args = parser.parse_args(argv)
    try:
        receipt = verify(args.fixture)
        rendered = json.dumps(receipt, sort_keys=True, indent=2) + "\n"
        if args.receipt is not None:
            write_new_file(args.receipt, rendered)
        sys.stdout.write(rendered)
    except CheckError as exc:
        sys.stderr.write("CHECK FAILED: " + str(exc) + "\n")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
