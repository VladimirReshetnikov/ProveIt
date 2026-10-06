#!/usr/bin/env python3
"""Exact, isolated Report144 placement-rate verifier; Python standard library only."""
import sys

# Check before any filesystem-resolved imports. -I ignores PYTHONPATH, disables the
# user site, and excludes the current directory and script directory from sys.path.
if not sys.flags.isolated:
    raise SystemExit("Refusing non-isolated startup. Run: python -I verify_certificate.py")

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import re
from fractions import Fraction

SCHEMA = "report144-placement-rate-certificate-v1"
LAST_INDEX = 100
TERM_COUNT = LAST_INDEX + 1
SCALE = 10 ** 12
LOWER = Fraction(527, 1000)
UPPER = Fraction(79, 125)
EXPECTED_VECTOR_SHA256 = "f6910ee2606f2272b4293f20e2d923961d6245e64743e112bc23c8cdc777c2f7"
PREFIX = (Fraction(1), Fraction(1), Fraction(3, 4), Fraction(83, 162),
          Fraction(55537, 165888), Fraction(11049709, 51840000))
HERE = Path(__file__).resolve().parent
DEFAULT_FIXTURE = HERE / "fixtures" / "rate_certificate.json"
OUTPUT_FILENAME = "verified_certificate.json"
SERIALIZATION = "reduced nonnegative numerator/positive denominator, lowercase hexadecimal without 0x or leading zeros; one rational per LF line, including final LF"
HEX_RATIONAL = re.compile(r"(?:0|[1-9a-f][0-9a-f]*)/[1-9a-f][0-9a-f]*\Z")
HEX_DIGEST = re.compile(r"[0-9a-f]{64}\Z")
MAX_FIXTURE_BYTES = 4000000


class VerificationError(Exception):
    """A mandatory check failed; these checks survive optimization."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def encode_rational(value):
    require(type(value) is Fraction and value >= 0, "Cannot encode a nonnegative rational")
    return format(value.numerator, "x") + "/" + format(value.denominator, "x")


def decode_rational(value, name):
    require(type(value) is str and HEX_RATIONAL.fullmatch(value) is not None,
            name + ": invalid canonical hexadecimal rational")
    numerator, denominator = (int(part, 16) for part in value.split("/"))
    require(math.gcd(numerator, denominator) == 1,
            name + ": rational is not reduced")
    answer = Fraction(numerator, denominator)
    require(encode_rational(answer) == value, name + ": noncanonical rational")
    return answer


def vector_digest(encoded_values):
    return hashlib.sha256(("\n".join(encoded_values) + "\n").encode("ascii")).hexdigest()


def binomial_tail_numerator(n, k, a):
    """n**n times I_(a/n)(k,n-k+1), using an integer binomial tail."""
    return sum(math.comb(n, j) * a ** j * (n - a) ** (n - j)
               for j in range(k, n + 1))


def binomial_weight(n, k):
    # Q_(n,k)/n; no alternating antiderivative and no symmetry reduction.
    numerator = (binomial_tail_numerator(n, k, k)
                 - binomial_tail_numerator(n, k, k - 1))
    result = Fraction(numerator, n ** (n + 1))
    require(result > 0, "Binomial-tail weight must be positive")
    return result


def polynomial_weight(n, k):
    """Independent alternating polynomial antiderivative for Q_(n,k)/n."""
    lo, hi = Fraction(k - 1, n), Fraction(k, n)
    integral = sum((Fraction((-1) ** j * math.comb(n - k, j), k + j)
                    * (hi ** (k + j) - lo ** (k + j))
                    for j in range(n - k + 1)), Fraction())
    result = math.comb(n - 1, k - 1) * integral
    require(result > 0, "Polynomial-integral weight must be positive")
    return result


def regenerate():
    """Independently compute both full vectors and check all distinct weights."""
    tails = [Fraction(1)]
    integrals = [Fraction(1)]
    checked_weights = 0
    for n in range(1, LAST_INDEX + 1):
        tail_weights = [binomial_weight(n, k) for k in range(1, n + 1)]
        tail_value = sum((tails[k - 1] * tails[n - k] * tail_weights[k - 1]
                          for k in range(1, n + 1)), Fraction())
        integral_value = Fraction()
        for k in range(1, (n + 1) // 2 + 1):
            weight = polynomial_weight(n, k)
            require(weight == tail_weights[k - 1],
                    "Independent weights disagree at n=%d, k=%d" % (n, k))
            require(weight == tail_weights[n - k],
                    "Reflected binomial weight disagrees at n=%d, k=%d" % (n, k))
            multiplicity = 1 if 2 * k == n + 1 else 2
            integral_value += (multiplicity * integrals[k - 1]
                               * integrals[n - k] * weight)
            checked_weights += 1
        require(tail_value == integral_value,
                "Independent probabilities disagree at n=%d" % n)
        require(0 < tail_value <= 1, "Probability outside (0,1]")
        tails.append(tail_value)
        integrals.append(integral_value)
    require(tuple(tails[:len(PREFIX)]) == PREFIX, "Known exact prefix disagrees")
    require(tails == integrals, "Full independently generated vectors disagree")
    return tails, checked_weights


def generate_certificate():
    values, checked_weights = regenerate()
    encoded = [encode_rational(value) for value in values]
    digest = vector_digest(encoded)
    require(digest == EXPECTED_VECTOR_SHA256, "Historical independent vector digest disagrees")
    floors = [math.isqrt((n + 1) * SCALE * SCALE) for n in range(TERM_COUNT)]
    require(all(type(s) is int and s > 0
                and s * s <= (n + 1) * SCALE * SCALE < (s + 1) * (s + 1)
                for n, s in enumerate(floors)), "Integer square-root floor check failed")
    lower_rhs = 16 * TERM_COUNT ** 2 * LOWER ** TERM_COUNT
    require(values[-1] > lower_rhs, "Strict lower certificate failed")
    x = 1 / UPPER
    upper_polynomial = Fraction()
    for n in range(LAST_INDEX, -1, -1):
        upper_polynomial = x * upper_polynomial + values[n] * SCALE / floors[n]
    upper_lhs = 4 * x * upper_polynomial
    auxiliary_upper_bound = Fraction(95111, 1000)
    require(upper_lhs < auxiliary_upper_bound < TERM_COUNT,
            "Strict upper certificate or auxiliary comparison failed")
    return {
        "schema": SCHEMA,
        "last_probability_index": LAST_INDEX,
        "number_of_probabilities": TERM_COUNT,
        "parameters": {
            "m": TERM_COUNT, "N": TERM_COUNT,
            "kernel_upper_bound": encode_rational(Fraction(1)),
            "strict_lower_bound": encode_rational(LOWER),
            "strict_upper_bound": encode_rational(UPPER),
            "square_root_lower_scale": SCALE,
        },
        "probabilities": encoded,
        "prefix": encoded[:len(PREFIX)],
        "vector_serialization": SERIALIZATION,
        "vector_sha256": digest,
        "square_root_floors": floors,
        "certificate_values": {
            "lower_left_hand_side": encoded[-1],
            "lower_right_hand_side": encode_rational(lower_rhs),
            "upper_left_hand_side": encode_rational(upper_lhs),
            "upper_auxiliary_bound": encode_rational(auxiliary_upper_bound),
            "upper_right_hand_side": encode_rational(Fraction(TERM_COUNT)),
        },
        "checks": {
            "all_probabilities_in_open_closed_unit_interval": True,
            "all_101_independent_probabilities_match": True,
            "polynomial_weights_checked_with_reflections": checked_weights,
            "known_prefix_matches": True,
            "all_square_root_floors_exact": True,
            "strict_lower_certificate_passed": True,
            "strict_upper_certificate_passed": True,
            "strict_auxiliary_upper_bound_passed": True,
        },
    }


def exact_keys(value, names, where):
    require(type(value) is dict, where + ": expected an object")
    require(set(value) == set(names), where + ": unknown or missing fields")


def integer(value, where):
    require(type(value) is int, where + ": expected an integer (not bool)")
    require(value >= 0, where + ": expected a nonnegative integer")


def validate_shape(data):
    exact_keys(data, ["schema", "last_probability_index", "number_of_probabilities",
                     "parameters", "probabilities", "prefix", "vector_serialization",
                     "vector_sha256", "square_root_floors", "certificate_values", "checks"],
               "certificate")
    for name in ("schema", "vector_serialization"):
        require(type(data[name]) is str, name + ": expected a string")
    for name in ("last_probability_index", "number_of_probabilities"):
        integer(data[name], name)
    require(type(data["vector_sha256"]) is str
            and HEX_DIGEST.fullmatch(data["vector_sha256"]) is not None,
            "vector_sha256: expected 64 lowercase hexadecimal digits")
    parameters = data["parameters"]
    exact_keys(parameters, ["m", "N", "kernel_upper_bound", "strict_lower_bound",
                           "strict_upper_bound", "square_root_lower_scale"], "parameters")
    for name in ("m", "N", "square_root_lower_scale"):
        integer(parameters[name], "parameters." + name)
    for name in ("kernel_upper_bound", "strict_lower_bound", "strict_upper_bound"):
        decode_rational(parameters[name], "parameters." + name)
    for name, count in (("probabilities", TERM_COUNT), ("prefix", len(PREFIX))):
        require(type(data[name]) is list and len(data[name]) == count,
                name + ": wrong array type or length")
        for n, rational in enumerate(data[name]):
            decode_rational(rational, name + "[%d]" % n)
    require(type(data["square_root_floors"]) is list
            and len(data["square_root_floors"]) == TERM_COUNT,
            "square_root_floors: wrong array type or length")
    for n, value in enumerate(data["square_root_floors"]):
        integer(value, "square_root_floors[%d]" % n)
    certificate_values = data["certificate_values"]
    exact_keys(certificate_values, ["lower_left_hand_side", "lower_right_hand_side",
                                   "upper_left_hand_side", "upper_auxiliary_bound",
                                   "upper_right_hand_side"], "certificate_values")
    for name, value in certificate_values.items():
        decode_rational(value, "certificate_values." + name)
    checks = data["checks"]
    exact_keys(checks, ["all_probabilities_in_open_closed_unit_interval",
                       "all_101_independent_probabilities_match",
                       "polynomial_weights_checked_with_reflections", "known_prefix_matches",
                       "all_square_root_floors_exact", "strict_lower_certificate_passed",
                       "strict_upper_certificate_passed", "strict_auxiliary_upper_bound_passed"],
               "checks")
    for name, value in checks.items():
        if name == "polynomial_weights_checked_with_reflections":
            integer(value, "checks." + name)
        else:
            require(type(value) is bool, "checks." + name + ": expected a boolean")


def reject_number(value):
    raise VerificationError("Noninteger JSON number is forbidden: " + value)


def reject_duplicate_fields(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON field: " + key)
        result[key] = value
    return result


def parse_fixture(raw):
    require(type(raw) is bytes and len(raw) <= MAX_FIXTURE_BYTES,
            "Fixture is not bytes or exceeds size limit")
    try:
        data = json.loads(raw.decode("utf-8"), object_pairs_hook=reject_duplicate_fields,
                          parse_float=reject_number, parse_constant=reject_number)
    except (UnicodeError, ValueError) as exc:
        raise VerificationError("Invalid UTF-8 JSON fixture: " + str(exc)) from exc
    validate_shape(data)
    return data


def validate_fixture(data, expected):
    validate_shape(data)
    require(vector_digest(data["probabilities"]) == data["vector_sha256"],
            "Fixture vector digest does not match its rational vector")
    require(data["probabilities"] == expected["probabilities"],
            "Fixture probabilities disagree with independently recomputed recurrence")
    # Shapes were checked before equality, so bool/int equality cannot bypass types.
    require(data == expected, "Fixture contains a semantic mismatch")


def canonical_json_bytes(data):
    return (json.dumps(data, indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("ascii")


def load_fixture(path):
    with path.open("rb") as stream:
        raw = stream.read(MAX_FIXTURE_BYTES + 1)
    return parse_fixture(raw), raw


def open_output_directory(directory):
    """Open an explicit existing directory without following any symlink component.

    Uses descriptor-relative no-follow traversal. If the platform cannot provide
    it, secure file output fails closed; verification and stdout remain portable.
    """
    require(type(directory) is str and directory != "", "An explicit output directory is required")
    supplied = Path(directory).expanduser()
    require(".." not in supplied.parts, "Output directory cannot contain '..'")
    absolute = supplied if supplied.is_absolute() else Path.cwd() / supplied
    require(absolute.is_dir(), "Output directory must already exist")
    for component in (absolute,) + tuple(absolute.parents):
        require(not component.is_symlink(), "Symlink output-directory component is forbidden")
    resolved = absolute.resolve(strict=True)
    require(resolved == absolute, "Output directory does not have a canonical resolved path")
    require(resolved != HERE and HERE not in resolved.parents,
            "Output may not be written into the companion source or fixture tree")
    require(os.open in os.supports_dir_fd and hasattr(os, "O_DIRECTORY")
            and hasattr(os, "O_NOFOLLOW"),
            "This platform cannot provide secure descriptor-relative output; use stdout")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    descriptor = os.open(resolved.anchor, flags)
    try:
        for part in resolved.parts[1:]:
            child = os.open(part, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return descriptor, resolved
    except BaseException:
        os.close(descriptor)
        raise


def write_output(directory, data):
    descriptor, resolved = open_output_directory(directory)
    try:
        # Fixed basename plus O_EXCL forbids source/fixture overwrite, existing
        # files, hard links, symlinks, and caller-selected path traversal.
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW
        output = os.open(OUTPUT_FILENAME, flags, 0o600, dir_fd=descriptor)
        with os.fdopen(output, "wb") as stream:
            stream.write(canonical_json_bytes(data))
    finally:
        os.close(descriptor)
    return resolved / OUTPUT_FILENAME


def summary(data, fixture_raw):
    return {
        "schema": "report144-placement-rate-verification-summary-v1",
        "fixture_sha256": hashlib.sha256(fixture_raw).hexdigest(),
        "vector_sha256": data["vector_sha256"],
        "number_of_probabilities": TERM_COUNT,
        "last_probability_index": LAST_INDEX,
        "strict_lower_bound": "527/1000",
        "strict_upper_bound": "79/125",
        "square_root_lower_scale": SCALE,
        "polynomial_weights_checked_with_reflections": data["checks"]["polynomial_weights_checked_with_reflections"],
        "all_mandatory_checks_passed": True,
        "arithmetic": "exact integers and rational numbers only",
        "scope": "finite certificate conditional on the separately proved analytic rate and kernel theorems",
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE,
                        help="Read a closed-schema fixture (default: bundled fixture)")
    parser.add_argument("--write-output", metavar="EXISTING_DIRECTORY",
                        help="Write verified_certificate.json exclusively in this existing resolved directory")
    args = parser.parse_args(argv)
    try:
        data, raw = load_fixture(args.fixture)
        expected = generate_certificate()
        validate_fixture(data, expected)
        if args.write_output is not None:
            write_output(args.write_output, expected)
        print(canonical_json_bytes(summary(expected, raw)).decode("ascii"), end="")
    except (VerificationError, OSError) as exc:
        print("Verification failed: " + str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
