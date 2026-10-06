#!/usr/bin/env python3
"""Report 165: bounded exact checks, with separately marked binary64 illustrations.

Python 3.10+, standard library only. No import-time writes or computations.
Run with --help. Never use this program as an asymptotic error certificate.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import sys

MAX_N = 512
CAPS = (None, 1, 2, 3, 5)
SIGNS = (-1, 1)
MAX_ORDER = 6
MAX_TARGET = 10**24
BETAS = (F(-1, 4), F(0), F(3, 4))
TARGETS = (0, 1, 2, 10, 100, 1000, 100000, 100000000, MAX_TARGET)
SCHEMA = "report165-exact-companion-v1"


class CheckFailure(RuntimeError):
    """A mathematical consistency check failed (active even under python -O)."""


class ThresholdNotFound(ValueError):
    """No first crossing was found within the declared finite scan."""


def _require(condition, message):
    if not condition:
        raise CheckFailure(message)


def _integer(value, label, minimum, maximum):
    # In particular bool, float, Decimal and coercible strings are not integers.
    if type(value) is not int:
        raise TypeError(f"{label} must have exact type int (bool is rejected)")
    if not minimum <= value <= maximum:
        raise ValueError(f"{label} must be between {minimum} and {maximum}")
    return value


def _family(sigma, cap):
    _integer(sigma, "sigma", -1, 1)
    if sigma not in SIGNS:
        raise ValueError("sigma must be -1 or +1")
    if cap is not None:
        _integer(cap, "cap", 1, 5)
        if cap not in CAPS:
            raise ValueError("cap must be None, 1, 2, 3 or 5")


def _beta(beta):
    if type(beta) is not F:
        raise TypeError("beta must have exact type Fraction")
    if beta not in BETAS:
        raise ValueError("beta must be -1/4, 0 or 3/4")


def product_counts(sigma, cap=None, n_max=MAX_N):
    """Exact product, multiplying each sparse part factor into a fresh array."""
    _family(sigma, cap)
    _integer(n_max, "n_max", 0, MAX_N)
    coefficients = [1] + [0] * n_max
    for part in range(1, n_max + 1):
        sign = -1 if part.bit_count() % 2 else 1
        if sign != sigma:
            continue
        old = coefficients
        coefficients = [0] * (n_max + 1)
        limit = n_max // part if cap is None else min(cap, n_max // part)
        for multiplicity in range(limit + 1):
            shift = multiplicity * part
            for degree in range(n_max - shift + 1):
                coefficients[degree + shift] += old[degree]
    return coefficients


def euler_counts(sigma, cap=None, n_max=MAX_N):
    """Independent divisor-pair logarithmic-derivative recurrence.

    Classification uses binary recursion instead of product_counts' bit_count.
    Let s(j) = sum_{d|j, allowed} d. Then b(j)=s(j) in the unrestricted
    case and b(j)=s(j)-(m+1)s(j/(m+1)) when m+1 divides j, otherwise s(j).
    n f(n)=sum_{j=1}^n b(j) f(n-j).
    """
    _family(sigma, cap)
    _integer(n_max, "n_max", 0, MAX_N)
    signs = [1] * (n_max + 1)
    for n in range(1, n_max + 1):
        signs[n] = signs[n // 2] * (-1 if n % 2 else 1)
    divisor_sums = [0] * (n_max + 1)
    for n in range(1, n_max + 1):
        for divisor in range(1, math.isqrt(n) + 1):
            if n % divisor:
                continue
            other = n // divisor
            if signs[divisor] == sigma:
                divisor_sums[n] += divisor
            if other != divisor and signs[other] == sigma:
                divisor_sums[n] += other
    logarithmic_derivative = divisor_sums.copy()
    if cap is not None:
        r = cap + 1
        for n in range(r, n_max + 1, r):
            logarithmic_derivative[n] -= r * divisor_sums[n // r]
    coefficients = [1]
    for n in range(1, n_max + 1):
        numerator = sum(logarithmic_derivative[j] * coefficients[n - j]
                        for j in range(1, n + 1))
        quotient, remainder = divmod(numerator, n)
        _require(remainder == 0, f"Euler division is nonintegral at n={n}")
        _require(quotient >= 0, f"Euler coefficient is negative at n={n}")
        coefficients.append(quotient)
    return coefficients


def _first_crossing(counts, target):
    for n, count in enumerate(counts):
        if count >= target:
            return n
    raise ThresholdNotFound(
        f"No crossing through n={len(counts)-1}; the threshold beyond this "
        "bound is unresolved, not infinite")


def exact_threshold(sigma, cap, target):
    """Return T(y)=min{n>=0:p(n)>=y}, if found by the fixed scan 0..512.

    The minimum is global: every smaller nonnegative index was examined.
    No monotonicity is presumed. Never rounds a float or uses a tail-only min.
    """
    _family(sigma, cap)
    _integer(target, "target", 0, MAX_TARGET)
    return _first_crossing(product_counts(sigma, cap), target)


def bessel_coefficients(beta, order=MAX_ORDER):
    """Exact r_j with B_j(beta,a)=r_j*a^(-j/2), j=0..order."""
    _beta(beta)
    _integer(order, "order", 0, MAX_ORDER)
    result = []
    for j in range(order + 1):
        numerator = F((-1)**j)
        for r in range(1, j + 1):
            numerator *= 4 * (beta + 1)**2 - (2*r - 1)**2
        result.append(numerator / (math.factorial(j) * 16**j))
    return result


def _ode_bessel(beta):
    # Substitute I_nu(x)=e^x*x^(-1/2)*H(x) in the modified Bessel ODE.
    # H''+2H'+(1/4-nu^2)x^(-2)H=0. r_j is the x^-j coefficient / 2^j.
    nu_squared = (beta + 1)**2
    r = [F(1)]
    for j in range(1, MAX_ORDER + 1):
        r.append(r[-1] * (F(2*j-1, 2)**2 - nu_squared) / (4*j))
    return r


def _poly_add(left, right):
    out = dict(left)
    for degree, coefficient in right.items():
        out[degree] = out.get(degree, F(0)) + coefficient
    return {degree: coefficient for degree, coefficient in out.items() if coefficient}


def _poly_multiply(left, right):
    out = {}
    for j, x in left.items():
        for k, y in right.items():
            out[j+k] = out.get(j+k, F(0)) + x*y
    return {degree: coefficient for degree, coefficient in out.items() if coefficient}


def _gaussian_bessel(beta):
    # Direct Gaussian saddle at a=1. q=sqrt(t), w=t(1-i*q*u).
    # Factor i^d out of each q^d coefficient, leaving rational u-polynomials.
    # The exponent after 2/t-u^2 is sum_{d>=1} -i^d q^d u^(d+2).
    degree = 2 * MAX_ORDER
    h = [{}] + [{d+2: F(-1)} for d in range(1, degree+1)]
    exp_h = [{0: F(1)}]
    for d in range(1, degree+1):
        total = {}
        for k in range(1, d+1):
            term = _poly_multiply(h[k], exp_h[d-k])
            total = _poly_add(total, {u: coefficient*k/d for u, coefficient in term.items()})
        exp_h.append(total)
    amplitude = []
    binomial = F(1)
    for d in range(degree+1):
        amplitude.append({d: (-1)**d * binomial})
        binomial *= (beta-d) / (d+1)
    moments = {0: F(1)}
    for d in range(2, 3*degree+1, 2):
        moments[d] = moments[d-2] * F(d-1, 2)
    result, odd = [], []
    for d in range(degree+1):
        polynomial = {}
        for k in range(d+1):
            polynomial = _poly_add(polynomial, _poly_multiply(amplitude[k], exp_h[d-k]))
        integral = sum((coefficient*moments[u] for u, coefficient in polynomial.items()
                        if u % 2 == 0), F(0))
        if d % 2:
            _require(integral == 0, f"odd Gaussian power did not vanish: {d}")
            odd.append(integral)
        else:
            result.append((-1)**(d//2) * integral)
    return result, odd


# Fixed-size Fraction series ring Q[u]/(u^7). No public precision parameter.
def _zero():
    return [F(0)] * (MAX_ORDER + 1)


def _one():
    return [F(1)] + [F(0)] * MAX_ORDER


def _add(a, b):
    return [x+y for x, y in zip(a, b)]


def _scale(a, k):
    return [x*k for x in a]


def _mul(a, b):
    return [sum((a[j]*b[n-j] for j in range(n+1)), F(0))
            for n in range(MAX_ORDER+1)]


def _power(a, k):
    result = _one()
    for _ in range(k):
        result = _mul(result, a)
    return result


def _log1p(a):
    _require(a[0] == 0, "formal log requires zero constant term")
    result = _zero()
    term = _one()
    for k in range(1, MAX_ORDER+1):
        term = _mul(term, a)
        result = _add(result, _scale(term, F((-1)**(k+1), k)))
    return result


def _binomial1p(a, exponent):
    _require(a[0] == 0, "formal binomial requires zero constant term")
    result, term, binomial = _one(), _one(), F(1)
    for k in range(1, MAX_ORDER+1):
        term = _mul(term, a)
        binomial *= (exponent-k+1)/k
        result = _add(result, _scale(term, binomial))
    return result


def _exp(a):
    _require(a[0] == 0, "formal exponential requires zero constant term")
    result, term = _one(), _one()
    for k in range(1, MAX_ORDER+1):
        term = _mul(term, a)
        result = _add(result, _scale(term, F(1, math.factorial(k))))
    return result


def _inverse_residual(delta, r, p):
    u = _zero()
    u[1] = F(1)
    ud = _mul(u, delta)
    inverse_z = _mul(u, _binomial1p(ud, F(-1)))
    correction = _zero()
    for j in range(MAX_ORDER+1):
        correction = _add(correction, _scale(_power(inverse_z, j), r[j]))
    correction[0] -= 1
    return _add(_add(_scale(delta, F(2)), _scale(_log1p(ud), -2*p)), _log1p(correction))


def inverse_coefficients(beta):
    """Exact d_1..d_6 for z=z0+sum d_j*z0^-j, z=sqrt(a*(x+lambda)).

    z0 solves the leading equation 2z0-2p log z0+log(K*a^p)=log(y).
    Returned coefficients do not locate or round any numerical threshold.
    """
    _beta(beta)
    r = bessel_coefficients(beta)
    p = beta/2 + F(3, 4)
    delta = _zero()
    for j in range(1, MAX_ORDER+1):
        residual = _inverse_residual(delta, r, p)
        delta[j] = -residual[j]/2
    _require(_inverse_residual(delta, r, p) == _zero(), "formal inverse log residual")
    # Independent multiplicative check, avoiding logarithmic-series evaluation:
    # exp(2 delta)*(1+u delta)^(-2p)*sum r_j*[u/(1+u delta)]^j = 1.
    u = _zero()
    u[1] = F(1)
    ud = _mul(u, delta)
    invz = _mul(u, _binomial1p(ud, F(-1)))
    correction = _zero()
    for j in range(MAX_ORDER+1):
        correction = _add(correction, _scale(_power(invz, j), r[j]))
    residual = _mul(_mul(_exp(_scale(delta, F(2))), _binomial1p(ud, -2*p)), correction)
    _require(residual == _one(), "formal inverse multiplicative residual")
    return delta[1:]


def _rational(value):
    return f"{value.numerator}/{value.denominator}"


def _family_key(sigma, cap):
    return ("odious" if sigma == -1 else "evil") + ("_unrestricted" if cap is None else f"_cap_{cap}")


def _load_prefixes():
    path = Path(__file__).with_name("oeis_prefixes.json")
    raw = path.read_bytes()
    _require(len(raw) < 20000, "unexpectedly large prefix fixture")
    fixture = json.loads(raw)
    _require(fixture["schema"] == "report165-oeis-prefixes-v1", "prefix schema mismatch")
    _require(len(fixture["sequences"]) == 4, "expected four OEIS prefixes")
    for row in fixture["sequences"]:
        _family(row["sigma"], row["cap"])
        _require(1 <= len(row["terms"]) <= 100, "prefix length out of bounds")
        for term in row["terms"]:
            _integer(term, "OEIS term", 0, MAX_TARGET)
    return fixture, hashlib.sha256(raw).hexdigest()


def exact_results():
    """Run the entire fixed bounded suite. No arbitrary workload input."""
    families = {}
    for cap in CAPS:
        for sigma in SIGNS:
            counts = product_counts(sigma, cap)
            recurrence = euler_counts(sigma, cap)
            _require(counts == recurrence, f"coefficient mismatch: {sigma}, {cap}")
            thresholds = []
            for target in TARGETS:
                try:
                    n = _first_crossing(counts, target)
                except ThresholdNotFound:
                    thresholds.append({"target": str(target), "status": "not_found_through_bound",
                                       "n": None, "global_threshold": "unresolved"})
                else:
                    _require(all(value < target for value in counts[:n]), "nonminimal threshold")
                    thresholds.append({"target": str(target), "status": "exact_global_minimum",
                                       "n": n, "count_at_n": str(counts[n]),
                                       "max_count_before_n": str(max(counts[:n])) if n else None})
            families[_family_key(sigma, cap)] = {
                "sigma": sigma, "cap": cap, "product_equals_euler_through": MAX_N,
                "counts_n_0_through_bound": [str(x) for x in counts],
                "thresholds": thresholds,
                "finite_nonstrict_adjacent_indices": [n for n in range(MAX_N) if counts[n+1] <= counts[n]],
            }
    fixture, fixture_digest = _load_prefixes()
    prefix_checks = []
    for row in fixture["sequences"]:
        actual = families[_family_key(row["sigma"], row["cap"])]["counts_n_0_through_bound"]
        _require([int(x) for x in actual[:len(row["terms"])]] == row["terms"], f"{row['id']} prefix mismatch")
        prefix_checks.append({"id": row["id"], "terms_matched": len(row["terms"]),
                              "source_url": row["source_url"], "record_revision": row["record_revision"]})
    algebra = []
    for beta in BETAS:
        r = bessel_coefficients(beta)
        gaussian, odd = _gaussian_bessel(beta)
        _require(r == _ode_bessel(beta) == gaussian, f"Bessel checks failed for beta={beta}")
        d = inverse_coefficients(beta)
        # x=z0^2/a-lambda+(sum c_j*z0^-j)/a. Only c_0..c_5
        # are justified by d_1..d_6; the next coefficient would require d_7.
        delta = [F(0)] + d
        square = _mul(delta, delta)
        c = [2*delta[j+1] + square[j] for j in range(MAX_ORDER)]
        _require(c[0] == -r[1], "inverse constant mismatch")
        algebra.append({"beta": _rational(beta), "p": _rational(beta/2+F(3,4)),
                        "r_j_j0_through_j6": [_rational(x) for x in r],
                        "coefficient_checks": ["direct_product", "modified_Bessel_ODE", "Gaussian_saddle"],
                        "vanishing_odd_Gaussian_powers_q1_q3_through_q11": [_rational(x) for x in odd],
                        "d_j_j1_through_j6": [_rational(x) for x in d],
                        "x_correction_c_j_j0_through_j5": [_rational(x) for x in c],
                        "logarithmic_inverse_residual_through_u6": "0",
                        "multiplicative_inverse_residual_through_u6": "0"})
    # a=A*m/(m+1); lambda=m/48. These are rational specifications of a/pi^2.
    parameters = []
    for cap in CAPS:
        for sigma in SIGNS:
            beta = F(1,4)+F(sigma,2) if cap is None else F(0)
            a_over_pi_squared = F(1,12) if cap is None else F(cap, 12*(cap+1))
            lam = F(-1,48) if cap is None else F(cap,48)
            r1 = bessel_coefficients(beta, 1)[1]
            parameters.append({"family": _family_key(sigma, cap), "beta": _rational(beta),
                               "a_over_pi_squared": _rational(a_over_pi_squared),
                               "lambda": _rational(lam),
                               "inverse_constant_rational_part": _rational(-lam),
                               "inverse_constant_coefficient_of_pi_to_minus_2": _rational(-r1/a_over_pi_squared)})
    return {"schema": SCHEMA, "report": 165, "arithmetic": "exact integers and rational Fractions",
            "bounds": {"n_max": MAX_N, "caps": list(CAPS), "bessel_order_max": MAX_ORDER,
                       "formal_inverse_order": MAX_ORDER, "target_max": str(MAX_TARGET)},
            "threshold_definition": "min{n>=0:p(n)>=y}; a found finite scan hit is the global minimum",
            "unresolved_threshold_policy": "No hit through 512 means unresolved; no monotonicity or infinity claim",
            "limits": ["No finite check proves an asymptotic theorem or an eventual onset",
                       "No numerical or interval error certificate is provided",
                       "No uniformity in a growing cap or optimal truncation is tested",
                       "Finite adjacent-count observations are not an eventual monotonicity certificate"],
            "oeis_fixture_sha256": fixture_digest, "oeis_prefix_checks": prefix_checks,
            "families": families, "bessel_and_inverse_algebra": algebra, "exact_parameters": parameters}


def _illustration(n, sigma, cap, order):
    # Deliberate binary64 arithmetic lives only in this numerical illustration.
    # d is an input approximation from the audit, not a recomputed enclosure.
    d_approx = float("-0.487450622521547444544502539868139328198173892")
    a = math.pi**2 / 12
    source_beta = F(1,4)+F(sigma,2)
    if cap is None:
        beta = source_beta
        lam = -1/48
        c = (2*math.pi)**(-0.25) * math.exp(sigma*d_approx/2)
    else:
        a *= cap/(cap+1)
        beta = F(0)
        lam = cap/48
        c = (cap+1)**(-float(source_beta))
    shifted_n = n+lam
    k = c*a**(float(beta)/2+0.25)/(2*math.sqrt(math.pi))
    z = math.sqrt(a*shifted_n)
    r = bessel_coefficients(beta, order)
    correction = sum(float(r[j])*z**(-j) for j in range(order+1))
    return k*shifted_n**(-float(beta)/2-0.75)*math.exp(2*z)*correction


def numerical_illustrations(exact):
    rows = []
    for cap in CAPS:
        for sigma in SIGNS:
            key = _family_key(sigma, cap)
            for n in (64, 128, 256, 512):
                count = int(exact["families"][key]["counts_n_0_through_bound"][n])
                rows.append({"family": key, "n": n, "exact_count": str(count),
                             "leading_relative_difference": format(_illustration(n,sigma,cap,0)/float(count)-1, ".12e"),
                             "seven_term_relative_difference": format(_illustration(n,sigma,cap,6)/float(count)-1, ".12e")})
    ratios = []
    for cap in CAPS[1:]:
        for n in (64, 128, 256, 512):
            od = int(exact["families"][_family_key(-1, cap)]["counts_n_0_through_bound"][n])
            ev = int(exact["families"][_family_key(1, cap)]["counts_n_0_through_bound"][n])
            residual = F(od-(cap+1)*ev, ev)
            ratios.append({"cap": cap, "n": n, "exact_ratio_residual": _rational(residual),
                           "binary64_ratio_residual": format(float(residual), ".12e")})
    return {"schema": "report165-numerical-illustrations-v1", "interval_certified": False,
            "onset_certified": False, "error_bound_certified": False,
            "arithmetic": "Python binary64 floats; displayed values rounded explicitly to 13 significant decimal digits",
            "constant_input": "d=-0.487450622521547444544502539868139328198173892, audit decimal approximation; not exact or certified",
            "warning": "Illustrations only. Seven terms need not be closer than one at finite n. No threshold rounding is performed.",
            "relative_difference_definition": "truncated asymptotic/count - 1",
            "rows": rows, "capped_ratio_residuals": ratios}


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False)+"\n").encode("ascii")


def _open_trusted_parent(parent):
    """Pin an existing owned non-group/world-writable directory, no symlink paths."""
    if type(parent) is not str or not parent.startswith("/"):
        raise ValueError("output parent must be an absolute path string")
    if parent == "/" or parent.endswith("/"):
        raise ValueError("output parent must name a non-root directory without trailing slash")
    components = parent.split("/")[1:]
    if any(part in ("", ".", "..") for part in components):
        raise ValueError("output parent must have normalized path components")
    if not hasattr(os, "O_NOFOLLOW") or not hasattr(os, "O_DIRECTORY"):
        raise OSError("secure output requires POSIX O_NOFOLLOW and O_DIRECTORY")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
    fd = os.open("/", flags)
    try:
        for part in components:
            next_fd = os.open(part, flags, dir_fd=fd)
            os.close(fd)
            fd = next_fd
        metadata = os.fstat(fd)
        if metadata.st_uid != os.geteuid() or metadata.st_mode & 0o022:
            raise PermissionError("output parent must be owned by this user and not group/world writable")
        return fd
    except BaseException:
        os.close(fd)
        raise


def write_run(parent, name):
    """Exclusively create one output directory and fixed files, never overwrite.

    Existing destinations (including dangling symlinks) fail. All filesystem
    writes are relative to pinned directory descriptors. A failed write may
    leave an incomplete private directory; it is never removed or reused.
    """
    if type(name) is not str or re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_-]{0,63}", name) is None:
        raise ValueError("output name must be a single safe 1..64 character component")
    parent_fd = _open_trusted_parent(parent)
    output_fd = None
    try:
        os.mkdir(name, mode=0o700, dir_fd=parent_fd)  # fails if anything already exists
        output_fd = os.open(name, os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW, dir_fd=parent_fd)
        metadata = os.fstat(output_fd)
        _require(stat.S_ISDIR(metadata.st_mode) and metadata.st_uid == os.geteuid()
                 and not metadata.st_mode & 0o077, "new output directory is not private")
        exact = exact_results()
        payloads = {"exact_results.json": json_bytes(exact),
                    "numerical_illustrations.json": json_bytes(numerical_illustrations(exact))}
        checksums = "".join(hashlib.sha256(payloads[filename]).hexdigest()+"  "+filename+"\n"
                            for filename in sorted(payloads))
        payloads["SHA256SUMS"] = checksums.encode("ascii")
        # Completion record last: its existence means previous writes were fsynced.
        payloads["COMPLETE.json"] = json_bytes({"schema": SCHEMA, "complete": True,
                                                "files": sorted(payloads)})
        for filename, payload in payloads.items():
            file_fd = os.open(filename, os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,
                              0o600, dir_fd=output_fd)
            with os.fdopen(file_fd, "wb") as handle:
                handle.write(payload)
                handle.flush()
                os.fsync(handle.fileno())
        os.fsync(output_fd)
        os.fsync(parent_fd)
    finally:
        if output_fd is not None:
            os.close(output_fd)
        os.close(parent_fd)
    return os.path.join(parent, name)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-parent", required=True, help="existing absolute owned directory, no symlinks")
    parser.add_argument("--output-name", required=True, help="new child directory name; no overwrite")
    args = parser.parse_args(argv)
    try:
        output = write_run(args.output_parent, args.output_name)
    except (OSError, ValueError, TypeError, CheckFailure) as error:
        parser.exit(2, f"companion: {error}\n")
    print(f"Exact checks passed; output exclusively created at {output}")
    print("Numerical illustrations are not interval, onset, or error certificates.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
