#!/usr/bin/env python3
"""Bounded exact diagnostics for Report 278; finite checks are not proofs.

Only integers and fractions.Fraction are used. No Fourier floating-point
calculation, theorem-scale partition, or phase-correlation premise is certified.
The CLI emits deterministic sorted JSON, identically under normal Python and -O.
Public numerical helpers reject booleans, floats, unbounded iterables and inputs
outside explicit caps; runtime checks never depend on Python assertions.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import gcd, isqrt
import re
import sys

Q = Fraction
MAX_NMAX = 12
MAX_MODULUS = 64
MAX_MOMENT_MODULUS = 24
MAX_ARITHMETIC_MODULUS = 10**6
MAX_LENGTH = 10**6
MAX_INTEGER = 2**128 - 1
MAX_FRACTION_PART = 2**64 - 1
MAX_PRIME = 23
DIGIT_CAP = 64


class CheckFailure(RuntimeError):
    """A failed diagnostic, including when Python optimization is enabled."""


def _ensure(condition, message):
    if not condition:
        raise CheckFailure(message)


def _integer(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in [{low}, {high}]")
    return value


def _fraction(value, name):
    if type(value) not in (int, Q):
        raise ValueError(f"{name} must be an integer or Fraction")
    value = Q(value)
    _integer(value.numerator, name + " numerator", -MAX_FRACTION_PART, MAX_FRACTION_PART)
    _integer(value.denominator, name + " denominator", 1, MAX_FRACTION_PART)
    return value


def _vector(values, n, name, low, high):
    if type(values) not in (tuple, list) or len(values) != n:
        raise ValueError(f"{name} must be a list or tuple of exactly {n} entries")
    result = tuple(_fraction(x, name + " entry") for x in values)
    if any(not low <= x <= high for x in result):
        raise ValueError(f"{name} entries must lie in [{low}, {high}]")
    return result


def _probability(values, n):
    result = _vector(values, n, "probability", 0, 1)
    if sum(result) != 1:
        raise ValueError("probability entries must sum to one")
    return result


def _subset(n, values):
    if type(values) not in (set, frozenset, tuple, list) or len(values) > n:
        raise ValueError("subset must be a bounded collection, not an iterator")
    for value in values:
        _integer(value, "residue", 0, n - 1)
    if len(set(values)) != len(values):
        raise ValueError("subset contains duplicates")
    return frozenset(values)


def _parse(value, name, low, high):
    if type(value) is not str or not 1 <= len(value) <= DIGIT_CAP:
        raise ValueError(f"{name} accepts at most 64 ASCII decimal digits")
    if re.fullmatch(r"[0-9]+", value) is None:
        raise ValueError(f"{name} requires an ASCII decimal integer")
    canonical = value.lstrip("0") or "0"
    if len(canonical) > len(str(high)):
        raise ValueError(f"{name} exceeds its diagnostic cap")
    return _integer(int(canonical), name, low, high)


def _jsonable(value):
    if type(value) is Q:
        return str(value)
    if isinstance(value, dict):
        return {key: _jsonable(child) for key, child in value.items()}
    if isinstance(value, (tuple, list)):
        return [_jsonable(child) for child in value]
    return value


def _proper(n, length, step):
    return n//gcd(n, step) >= length


def _parameters(n, length):
    m = 1
    for divisor in range(1, isqrt(n) + 1):
        if n % divisor == 0:
            for candidate in (divisor, n//divisor):
                if candidate < length:
                    m = max(m, candidate)
    q = n//m
    D = (n - 1)//(length - 1)
    return {"N": n, "L": length, "m": m, "q": q, "D": D,
            "arithmetic_coefficient": Q(max(q - length, 0), q - 1),
            "geometric_coefficient": Q(max(D + 1 - length, 0), D)}


def arithmetic_parameters(n, length):
    """Return m,q,D and clamped gain coefficients for 2<=L<=N<=10**6.

    The density increment is coefficient*(1-delta)/L. This bounded helper
    calculates the theorem's parameters; it does not prove the theorem.
    """
    _integer(n, "modulus", 2, MAX_ARITHMETIC_MODULUS)
    _integer(length, "length", 2, n)
    return _parameters(n, length)


def proper_support(n, length, support):
    """Test all nonzero differences of a subset of Z/NZ, with N<=64."""
    _integer(n, "modulus", 2, MAX_MODULUS)
    _integer(length, "length", 2, n)
    support = _subset(n, support)
    return all(_proper(n, length, x - y) for x in support for y in support if x != y)


def _window_masks(n, length, steps):
    return tuple(sorted({sum(1 << ((a + j*d) % n) for j in range(length))
                         for d in steps for a in range(n)}))


def maximum_density(n, selected, length):
    """Enumerate the maximum proper progression density for N<=64, L>=2."""
    _integer(n, "modulus", 2, MAX_MODULUS)
    _integer(length, "length", 2, n)
    selected = _subset(n, selected)
    mask = sum(1 << a for a in selected)
    windows = _window_masks(n, length, (d for d in range(1, n) if _proper(n, length, d)))
    return Q(max((mask & window).bit_count() for window in windows), length)


def exhaustive_theorem(nmax=8):
    """Check every nonempty proper A and 2<=L<=N<=nmax<=12 exactly.

    Integer cross multiplication checks the arithmetic and geometric bounds,
    including the restriction to their respective supported step ensembles.
    """
    _integer(nmax, "nmax", 2, MAX_NMAX)
    triples = parameter_pairs = 0
    for n in range(2, nmax + 1):
        for length in range(2, n + 1):
            p = _parameters(n, length)
            q, D = p["q"], p["D"]
            arith_steps = sorted({d % n for d in range(1 - q, q) if d})
            geo_steps = sorted({d % n for d in range(-D, D + 1) if d})
            _ensure(all(_proper(n, length, d) for d in arith_steps), "arithmetic properness")
            _ensure(all(_proper(n, length, d) for d in geo_steps), "geometric properness")
            _ensure(p["arithmetic_coefficient"] >= p["geometric_coefficient"],
                    "arithmetic coefficient dominates geometric coefficient")
            arith_windows = _window_masks(n, length, arith_steps)
            geo_windows = _window_masks(n, length, geo_steps)
            for mask in range(1, (1 << n) - 1):
                size = mask.bit_count()
                ma = max((mask & window).bit_count() for window in arith_windows)
                mg = max((mask & window).bit_count() for window in geo_windows)
                _ensure(ma*n*(q - 1) >= size*length*(q - 1) + (n - size)*max(q - length, 0),
                        "arithmetic density increment")
                _ensure(mg*n*D >= size*length*D + (n - size)*max(D + 1 - length, 0),
                        "geometric density increment")
                triples += 1
            parameter_pairs += 1
    return {"nmax": nmax, "nontrivial_subset_length_triples": triples,
            "parameter_pairs": parameter_pairs, "supported_step_bounds_checked": True}


def maximal_support_diagnostics(nmax=8):
    """Exhaust all B for 2<=L<=N<=nmax<=10; compare maximum |B| with q."""
    _integer(nmax, "support nmax", 2, 10)
    candidates = pairs = admissible = 0
    for n in range(2, nmax + 1):
        for length in range(2, n + 1):
            q = _parameters(n, length)["q"]
            bad = tuple(sum(1 << y for y in range(n)
                            if x != y and not _proper(n, length, x - y)) for x in range(n))
            largest = 0
            for mask in range(1 << n):
                candidates += 1
                if all(not (mask & bad[x]) for x in range(n) if mask & (1 << x)):
                    admissible += 1
                    largest = max(largest, mask.bit_count())
            _ensure(largest == q, "maximum proper-difference support equals q")
            _ensure(proper_support(n, length, list(range(q))), "canonical support is admissible")
            pairs += 1
    return {"nmax": nmax, "candidate_supports": candidates, "admissible_supports": admissible,
            "parameter_pairs": pairs}


def difference_law(n, probabilities):
    """Return the exact iid difference probability law on Z/NZ, N<=24."""
    _integer(n, "modulus", 2, MAX_MOMENT_MODULUS)
    p = _probability(probabilities, n)
    return tuple(sum((p[x]*p[(x - d) % n] for x in range(n)), Q(0)) for d in range(n))


def square_covariance(n, values, probabilities, h):
    """Check the iid square identity for real rational values in [-1,1].

    N<=24 and |h|<=4N; h may be zero, negative or a nonunit modulo N.
    """
    _integer(n, "modulus", 2, MAX_MOMENT_MODULUS)
    _integer(h, "index difference", -4*n, 4*n)
    f = _vector(values, n, "values", -1, 1)
    p = _probability(probabilities, n)
    return _square_covariance(n, f, p, h)


def _square_covariance(n, f, p, h):
    law = difference_law(n, p)
    direct = sum((law[d]*f[a]*f[(a + h*d) % n] for a in range(n) for d in range(n)), Q(0))/n
    square = sum((sum((p[s]*f[(z + h*s) % n] for s in range(n)), Q(0))**2
                  for z in range(n)), Q(0))/n
    _ensure(direct == square >= 0, "square covariance identity")
    return {"direct": direct, "square": square, "h": h}


def _window_moments(n, length, values, law):
    mean = sum(values)/n
    sigma2 = sum((value - mean)**2 for value in values)/n
    windows = tuple(tuple(sum((values[(a + j*d) % n] for j in range(length)), Q(0))/length
                          for a in range(n)) for d in range(n))
    for row in windows:
        _ensure(sum(row)/n == mean, "all conditional means equal the mean")
    variance = sum((law[d]*sum((y - mean)**2 for y in windows[d])/n for d in range(n)), Q(0))
    eta = law[0]
    maximum = max(y for d in range(1, n) if law[d] for y in windows[d])
    gain = maximum - mean
    nonzero_variance = (variance - eta*sigma2)/(1 - eta)
    lower = (sigma2/mean)*(Q(1, length) - eta)/(1 - eta)
    _ensure(variance >= sigma2/length, "variance lower bound")
    _ensure(nonzero_variance <= mean*gain, "one-sided range variance bound")
    _ensure(gain >= max(lower, 0), "bounded-function diagonal-removal gain")
    return {"mean": mean, "function_variance": sigma2, "window_variance": variance,
            "zero_mass": eta, "nonzero_variance": nonzero_variance,
            "maximum_supported_gain": gain, "raw_gain_lower_bound": lower,
            "clamped_gain_lower_bound": max(lower, Q(0))}


def function_diagnostic(n, length, values, probabilities):
    """Check iid covariance/variance/gain and collision bounds for g in [0,1].

    N<=24, positive mean, and at least two positive probabilities are required.
    Their support must have proper nonzero differences. Constant g is allowed.
    """
    _integer(n, "modulus", 2, MAX_MOMENT_MODULUS)
    _integer(length, "length", 2, n)
    g = _vector(values, n, "function", 0, 1)
    p = _probability(probabilities, n)
    support = tuple(i for i in range(n) if p[i])
    if len(support) < 2 or not proper_support(n, length, support):
        raise ValueError("probabilities need at least two points with proper differences")
    mean = sum(g)/n
    if mean == 0:
        raise ValueError("function must have positive mean")
    law = difference_law(n, p)
    q = _parameters(n, length)["q"]
    collision = sum(value*value for value in p)
    _ensure(law[0] == collision >= Q(1, len(support)) >= Q(1, q), "iid collision lower bounds")
    centered = tuple(value - mean for value in g)
    covariances = tuple(_square_covariance(n, centered, p, h)["square"] for h in range(length))
    result = _window_moments(n, length, g, law)
    expanded = (length*covariances[0] + 2*sum((length - h)*covariances[h]
                                              for h in range(1, length)))/(length*length)
    _ensure(result["window_variance"] == expanded, "covariance expansion of window variance")
    return {**result, "support_size": len(support), "q": q,
            "collision_probability": collision, "covariance_cases": length,
            "iid_support_bound_attained": collision == Q(1, q)}


def positive_definite_mixture(n, length, values, probability_vectors, mixing):
    """Exact diagnostics for a convex mixture of at most four autocorrelations.

    Each component has proper difference support and at least two support
    points; all have N<=24. Its positive definiteness follows from its supplied
    autocorrelation representation and the written square identity. Finite
    tests do not certify arbitrary weights as positive definite.
    """
    _integer(n, "modulus", 2, MAX_MOMENT_MODULUS)
    _integer(length, "length", 2, n)
    g = _vector(values, n, "function", 0, 1)
    if sum(g) == 0:
        raise ValueError("function must have positive mean")
    if type(probability_vectors) not in (tuple, list) or not 1 <= len(probability_vectors) <= 4:
        raise ValueError("provide one to four bounded probability vectors")
    coefficients = _probability(mixing, len(probability_vectors))
    vectors = tuple(_probability(p, n) for p in probability_vectors)
    for p in vectors:
        support = tuple(i for i in range(n) if p[i])
        if len(support) < 2 or not proper_support(n, length, support):
            raise ValueError("every component needs at least two proper-difference support points")
    laws = tuple(difference_law(n, p) for p in vectors)
    law = tuple(sum((c*w[d] for c, w in zip(coefficients, laws)), Q(0)) for d in range(n))
    q = _parameters(n, length)["q"]
    _ensure(sum(law) == 1 and law[0] >= Q(1, q), "positive-definite zero-mass bound")
    _ensure(all(not law[d] or _proper(n, length, d) for d in range(1, n)), "mixture proper support")
    mean = sum(g)/n
    f = tuple(value - mean for value in g)
    for h in range(length):
        direct = sum((law[d]*f[a]*f[(a + h*d) % n] for a in range(n) for d in range(n)), Q(0))/n
        represented = sum((c*_square_covariance(n, f, p, h)["square"]
                           for c, p in zip(coefficients, vectors)), Q(0))
        _ensure(direct == represented >= 0, "mixture covariance as exact sum of squares")
    result = _window_moments(n, length, g, law)
    method_best = (result["function_variance"]/mean)*Q(q - length, length*(q - 1))
    _ensure(result["raw_gain_lower_bound"] <= method_best, "diagonal-removal coefficient decreases with zero mass")
    return {**result, "q": q, "components": len(vectors), "covariance_cases": length,
            "method_best_raw_gain": method_best,
            "general_positive_definiteness_solver": False}


def moment_diagnostics(nmax=6):
    """Finite rational iid, function and autocorrelation-mixture samples, N<=10."""
    _integer(nmax, "moment nmax", 2, 10)
    functions = covariance_cases = mixtures = collision_cases = signed_cases = 0
    for n in range(2, nmax + 1):
        for length in range(2, n + 1):
            q = _parameters(n, length)["q"]
            uniform = tuple(Q(1, q) if x < q else Q(0) for x in range(n))
            weighted = tuple(Q(2*(x + 1), q*(q + 1)) if x < q else Q(0) for x in range(n))
            samples = (tuple(Q(int(x == 0)) for x in range(n)),
                       tuple(Q((x*x + x) % 5, 4) for x in range(n)), (Q(1, 3),)*n)
            for p in (uniform, weighted):
                collision_cases += 1
                for g in samples:
                    result = function_diagnostic(n, length, g, p)
                    covariance_cases += result["covariance_cases"]
                    functions += 1
                signed = tuple(Q(x % 3 - 1, 2) for x in range(n))
                for h in (-n, -2, 0, 2, n):
                    square_covariance(n, signed, p, h)
                    signed_cases += 1
            positive_definite_mixture(n, length, samples[1], (uniform, weighted), (Q(1, 3), Q(2, 3)))
            mixtures += 1
    return {"nmax": nmax, "function_cases": functions, "function_covariance_cases": covariance_cases,
            "iid_collision_cases": collision_cases, "signed_square_identity_cases": signed_cases,
            "positive_definite_mixture_cases": mixtures,
            "scope": "explicit rational autocorrelation examples; no arbitrary Fourier-positivity solver"}


def prime_extremizer(prime, length):
    """Check quotient extremizers for prime q<=23 and 2<=L<=q exactly.

    All proper steps and all starting residue classes modulo q are checked.
    Starts with the same residue class are equivalent because A={x:q divides x}.
    """
    _integer(prime, "prime", 2, MAX_PRIME)
    _integer(length, "length", 2, prime)
    if any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
        raise ValueError("prime parameter must be prime")
    n = prime*(length - 1)
    p = _parameters(n, length)
    _ensure(p["m"] == length - 1 and p["q"] == prime and p["D"] == prime - 1,
            "extremizer arithmetic parameters")
    steps = quotient_windows = 0
    maximum_count = 0
    for step in range(1, n):
        if not _proper(n, length, step):
            continue
        _ensure(step % prime != 0, "proper step has nonzero prime quotient")
        residues = tuple(j*step % prime for j in range(length))
        _ensure(len(set(residues)) == length, "distinct quotient points")
        for start in range(prime):
            count = sum((start + residue) % prime == 0 for residue in residues)
            _ensure(count <= 1, "at most one extremizer hit")
            maximum_count = max(maximum_count, count)
            quotient_windows += 1
        steps += 1
    maximum = Q(maximum_count, length)
    delta = Q(1, prime)
    bound = delta + (1 - delta)*Q(prime - length, length*(prime - 1))
    _ensure(maximum == Q(1, length) == bound, "exact prime quotient extremizer equality")
    return {"prime": prime, "L": length, "N": n, "density": delta,
            "maximum_density": maximum, "gain": maximum - delta,
            "gain_ratio": Q(prime - length, prime - 1),
            "proper_steps": steps, "quotient_start_step_windows": quotient_windows}



def endpoint_diagnostic(n, selected, length):
    """Check sliding-window and image-subgroup identities for nontrivial A, N<=64.

    The refined gain is checked when more than half the directions are proper
    and N/gcd(N,L)>=L. These arithmetic hypotheses, and the stronger sufficient
    conditions N>L(L-1) and N>=L**2, are reported separately. Count gain eta is
    L times density gain. A failed hypothesis is not a failed diagnostic.
    """
    _integer(n, "modulus", 2, MAX_MODULUS)
    _integer(length, "length", 2, n)
    selected = _subset(n, selected)
    if not 0 < len(selected) < n:
        raise ValueError("endpoint diagnostic needs a nonempty proper subset")
    indicator = tuple(int(a in selected) for a in range(n))
    proper = tuple(d for d in range(1, n) if _proper(n, length, d))
    windows = {d: tuple(sum(indicator[(a + j*d) % n] for j in range(length))
                        for a in range(n)) for d in proper}
    maximum = max(count for row in windows.values() for count in row)
    delta = Q(len(selected), n)
    eta = maximum - length*delta
    _ensure(eta >= 0, "nonnegative count gain by averaging")
    for d in proper:
        row = windows[d]
        _ensure(sum(row) == n*length*delta, "proper-window conditional mean")
        for a in range(n):
            _ensure(row[(a + d) % n] - row[a] == indicator[(a + length*d) % n] - indicator[a],
                    "exact sliding-window identity")
    shifts = tuple(Q(sum(indicator[a] != indicator[(a + length*x) % n] for a in range(n)), 2*n)
                   for x in range(n))
    _ensure(all(shifts[d] <= eta for d in proper), "proper shift deficit inequality")
    beta = Q(n - len(proper), n)
    _ensure(n - len(proper) <= length*(length - 1)//2, "short-order direction union bound")
    majority = 2*len(proper) > n
    g = gcd(n, length)
    subgroup_order = n//g
    subgroup_proper = subgroup_order >= length
    densities = tuple(Q(sum(indicator[a] for a in range(c, n, g)), subgroup_order) for c in range(g))
    impurity = sum(p*(1 - p) for p in densities)/g
    _ensure(sum(densities)/g == delta, "image-subgroup coset mean")
    _ensure(sum(shifts)/n == impurity, "symmetric-difference coset identity")
    if majority:
        _ensure({(d - e) % n for d in proper for e in proper} == set(range(n)), "proper difference set covers group")
        _ensure(all(value <= 2*eta for value in shifts), "all-shift deficit inequality")
        _ensure(impurity <= (1 + beta)*eta, "averaged proper and bad shift bounds")
    if subgroup_proper:
        _ensure(all(p <= Q(maximum, length) for p in densities), "coset densities bounded by proper windows")
        _ensure(impurity >= delta*(1 - delta) - delta*eta/length, "coset impurity lower bound")
    applies = majority and subgroup_proper
    lower = None
    if applies:
        lower = delta*(1 - delta)/(1 + beta + delta/length)
        _ensure(eta >= lower, "refined arithmetic endpoint count gain")
    size_condition = n > length*(length - 1)
    square_condition = n >= length*length
    if size_condition:
        _ensure(applies, "strict quadratic size supplies both arithmetic hypotheses")
        _ensure(eta > delta*(1 - delta)/2, "strict bounded-density endpoint count gain")
    return {"N": n, "L": length, "density": delta, "maximum_count": maximum,
            "count_gain_eta": eta, "density_gain_H": eta/length, "bad_direction_proportion_beta": beta,
            "proper_direction_majority": majority, "image_subgroup_order": subgroup_order,
            "image_subgroup_direction_proper": subgroup_proper, "arithmetic_hypotheses_hold": applies,
            "strict_size_hypothesis_holds": size_condition, "square_size_hypothesis_holds": square_condition,
            "refined_count_gain_lower_bound": lower,
            "refined_density_gain_lower_bound": lower/length if lower is not None else None,
            "coset_impurity": impurity,
            "sliding_window_identities": n*len(proper), "shift_coset_identity_checked": True}


def dense_prime_boundary(prime, quotient_subset):
    """Check dense no-gain examples at L=p,N=p(p-1), prime p<=23.

    quotient_subset is any nonempty proper subset of Z/pZ. Every proper step
    and every starting residue class modulo p is checked, using quotient
    equivalence of starts. This finite calculation does not prove a limit.
    """
    _integer(prime, "prime", 2, MAX_PRIME)
    if any(prime % d == 0 for d in range(2, isqrt(prime) + 1)):
        raise ValueError("prime parameter must be prime")
    subset = _subset(prime, quotient_subset)
    if not 0 < len(subset) < prime:
        raise ValueError("quotient subset must be nonempty and proper")
    n = prime*(prime - 1)
    proper_steps = quotient_windows = 0
    for step in range(1, n):
        if not _proper(n, prime, step):
            continue
        residues = tuple(j*step % prime for j in range(prime))
        _ensure(set(residues) == set(range(prime)), "proper boundary window visits all quotient residues")
        for start in range(prime):
            _ensure(sum((start + x) % prime in subset for x in residues) == len(subset),
                    "dense boundary window has exactly global count")
            quotient_windows += 1
        proper_steps += 1
    _ensure(n//gcd(n, prime) == prime - 1, "boundary image subgroup is too short")
    return {"prime": prime, "N": n, "L": prime, "quotient_subset_size": len(subset),
            "density": Q(len(subset), prime), "count_gain_eta": Q(0),
            "proper_steps": proper_steps, "quotient_start_step_windows": quotient_windows,
            "image_subgroup_order": prime - 1}


def endpoint_diagnostics(nmax=8):
    """Exhaust endpoint inequalities through N<=12 and sample exact proof identities.

    Exhaustion covers every nontrivial A for every pair satisfying both
    arithmetic hypotheses. Identity checks use three specified subset patterns,
    including ineligible pairs. The N>=L**2 counter is only a subset count
    for the same refined-beta and strict-half bounds. Dense prime-boundary rows
    are separate samples.
    """
    _integer(nmax, "endpoint nmax", 2, MAX_NMAX)
    triples = strict_triples = square_triples = pairs = identity_cases = sliding_cases = 0
    ineligible_identity_cases = 0
    for n in range(2, nmax + 1):
        for length in range(2, n + 1):
            proper = tuple(d for d in range(1, n) if _proper(n, length, d))
            bad = n - len(proper)
            applies = 2*len(proper) > n and n//gcd(n, length) >= length
            patterns = {1, (1 << (n//2)) - 1, sum(1 << a for a in range(0, n, 2))}
            for mask in sorted(patterns):
                row = endpoint_diagnostic(n, {a for a in range(n) if mask & (1 << a)}, length)
                identity_cases += 1
                sliding_cases += row["sliding_window_identities"]
                ineligible_identity_cases += int(not row["arithmetic_hypotheses_hold"])
            if not applies:
                continue
            pairs += 1
            windows = _window_masks(n, length, proper)
            for mask in range(1, (1 << n) - 1):
                size = mask.bit_count()
                maximum = max((mask & window).bit_count() for window in windows)
                eta_numerator = maximum*n - size*length
                _ensure(eta_numerator*(length*(n + bad) + size) >= size*(n - size)*length,
                        "exhaustive refined endpoint bound")
                triples += 1
                if n > length*(length - 1):
                    _ensure(2*n*eta_numerator > size*(n - size), "exhaustive strict size endpoint")
                    strict_triples += 1
                if n >= length*length:
                    square_triples += 1
    rows = []
    for prime in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        if prime > (23 if nmax > 8 else 13):
            continue
        for size in sorted({1, max(1, prime//3), prime//2, prime - 1}):
            rows.append(dense_prime_boundary(prime, list(range(size))))
    return {"nmax": nmax, "arithmetic_parameter_pairs": pairs,
            "nontrivial_arithmetic_subset_length_triples": triples,
            "strict_size_subset_length_triples": strict_triples,
            "square_size_subset_length_triples": square_triples,
            "proof_identity_subset_length_samples": identity_cases,
            "ineligible_identity_samples": ineligible_identity_cases,
            "sliding_window_identity_cases": sliding_cases,
            "dense_prime_boundary_cases": len(rows),
            "dense_boundary_quotient_start_step_windows": sum(r["quotient_start_step_windows"] for r in rows),
            "dense_boundary_rows": rows, "quantitative_constant_claimed_optimal": False}


def half_gain_length(n):
    """Largest L certified by N>=2(L-1)^2+1, for 1<=N<2**128.

    Return one if no length at least two meets this size-only condition.
    Arithmetic information can certify larger lengths.
    """
    _integer(n, "modulus", 1, MAX_INTEGER)
    return 1 + isqrt((n - 1)//2)


def coefficient_budget(length, coefficient):
    """Exact sufficient D and N for gain c*(1-delta)/L, 0<c<1, L<=10**6."""
    _integer(length, "length", 2, MAX_LENGTH)
    coefficient = _fraction(coefficient, "coefficient")
    if not 0 < coefficient < 1:
        raise ValueError("coefficient must lie strictly between zero and one")
    ratio = (length - 1)/(1 - coefficient)
    D = -(-ratio.numerator//ratio.denominator)
    return {"L": length, "coefficient": coefficient, "D": D,
            "sufficient_N": (length - 1)*D + 1}


def rational_constant_bound(n, length, constant):
    """Check the exact coefficient 1-1/C under N>=C*L^2, rational C>1.

    N<2**128 and L<=10**6. No asymptotic sharpness is inferred from this check.
    """
    _integer(n, "modulus", 2, MAX_INTEGER)
    _integer(length, "length", 2, min(n, MAX_LENGTH))
    constant = _fraction(constant, "constant")
    if constant <= 1 or n < constant*length*length:
        raise ValueError("require C>1 and N>=C*L^2")
    D = (n - 1)//(length - 1)
    floor_CL = (constant*length).numerator//(constant*length).denominator
    _ensure(D >= n//length >= floor_CL >= constant*length - 1 >= constant*(length - 1),
            "rational C integer floor chain")
    achieved = 1 - Q(length - 1, D)
    _ensure(achieved >= 1 - 1/constant, "rational C coefficient")
    return {"N": n, "L": length, "C": constant, "D": D,
            "certified_coefficient": achieved, "target_coefficient": 1 - 1/constant}


def _ceil_root(value, degree):
    low, high = 0, 1
    while high**degree < value:
        high *= 2
    while low + 1 < high:
        middle = (low + high)//2
        if middle**degree < value:
            low = middle
        else:
            high = middle
    return high


def affine_scalar_assembly(n, r, delta, tau, alpha):
    """Exact scalar rounding/branch toy for the affine exact-mass corollary.

    n,r<2**128, 0<delta<=tau<=1, delta<1, r<=tau*n, and 0<alpha<=mu.
    Scalars do not certify an actual cover or its complex correlation premise.
    The analytic inequality pi<4 is used as a stated input, not computed.
    """
    _integer(n, "modulus", 2, MAX_INTEGER)
    _integer(r, "minimum parent length", 1, n)
    delta, tau, alpha = (_fraction(x, name) for x, name in
                         ((delta, "density"), (tau, "union density"), (alpha, "correlation")))
    if not (0 < delta < 1 and delta <= tau <= 1 and r <= tau*n):
        raise ValueError("require 0<delta<1, delta<=tau<=1 and r<=tau*N")
    b = 1 - delta
    mu = delta*(1 + tau - 2*delta)
    if not 0 < alpha <= mu:
        raise ValueError("require 0<alpha<=mu")
    H = r*b/mu
    length = min(_ceil_root(H/128, 3), _ceil_root(Q(n, 2), 2))
    _ensure(0 < mu <= 2*delta*b and delta*(1 - tau) >= 0, "cover scalar mass bounds")
    if length == 1:
        _ensure(b > alpha/3, "singleton gain")
        branch = "singleton"
    else:
        _ensure(n >= 2*(length - 1)**2 + 1, "affine ceiling fits new half-gain threshold")
        _ensure(H > 16*length**3, "affine cube-root rounding slack")
        if alpha <= 3*b/(2*length):
            _ensure(b/(2*length) >= alpha/3, "low-correlation variance branch")
            branch = "variance"
        else:
            _ensure(r > 24*length*length > length, "high-correlation refinement is legal")
            error_upper_using_pi_lt_four = 8*length*length*mu/r
            _ensure(error_upper_using_pi_lt_four < alpha/3, "high-correlation error budget")
            branch = "refinement"
    return {"N": n, "r": r, "density": delta, "union_density": tau, "mu": mu,
            "alpha": alpha, "H": H, "ceiling_length": length, "branch": branch,
            "actual_cover_or_phase_correlation_certified": False}


def rounding_diagnostics():
    """Finite integer half-gain, floor/ceiling, rational C and affine scalar checks."""
    half_cases = budget_cases = constant_cases = ceiling_cases = 0
    for length in range(2, 65):
        boundary = 2*(length - 1)**2 + 1
        _ensure(half_gain_length(boundary - 1) == length - 1, "half-gain below boundary")
        _ensure(half_gain_length(boundary) == length, "half-gain at boundary")
        _ensure(half_gain_length(boundary + 1) == length, "half-gain above boundary")
        half_cases += 3
        for coefficient in (Q(1, 4), Q(1, 2), Q(2, 3), Q(9, 10)):
            result = coefficient_budget(length, coefficient)
            D = result["D"]
            _ensure(1 - Q(length - 1, D) >= coefficient, "sufficient ceiling budget")
            _ensure(1 - Q(length - 1, D - 1) < coefficient, "preceding budget insufficient")
            _ensure((result["sufficient_N"] - 1)//(length - 1) == D, "exact geometric floor")
            _ensure((result["sufficient_N"] - 2)//(length - 1) == D - 1, "preceding modulus floor")
            budget_cases += 1
        for constant in (Q(4, 3), Q(3, 2), Q(2), Q(7, 2), Q(10)):
            bound = constant*length*length
            n = -(-bound.numerator//bound.denominator)
            rational_constant_bound(n, length, constant)
            constant_cases += 1
    for degree in (2, 3):
        for root in range(1, 33):
            boundary = Q(root**degree)
            _ensure(_ceil_root(boundary - Q(1, 2), degree) == root, "root ceiling below integer")
            _ensure(_ceil_root(boundary, degree) == root, "root ceiling at integer")
            _ensure(_ceil_root(boundary + Q(1, 2), degree) == root + 1, "root ceiling above integer")
            ceiling_cases += 3
    affine = []
    for delta, tau in ((Q(1, 2), Q(1)), (Q(1, 4), Q(1, 2)), (Q(1, 8), Q(1, 4))):
        n, r = 10**9, 10**6
        mu = delta*(1 + tau - 2*delta)
        for alpha in (Q(1, 10**6), mu):
            affine.append(affine_scalar_assembly(n, r, delta, tau, alpha))
    affine.append(affine_scalar_assembly(8, 1, Q(1, 2), Q(1), Q(1, 4)))
    for t in (2, 3, 8):
        # These two families hit cube and square ceiling boundaries exactly.
        affine.append(affine_scalar_assembly(10**8, 128*t**3, Q(1, 2), Q(1), Q(1, 1000)))
        n = 2*t*t
        row = affine_scalar_assembly(n, n, Q(1, 1024*n), Q(1), Q(1, 4096*n))
        _ensure(row["ceiling_length"] == t, "square-cap affine equality boundary")
        affine.append(row)
    return {"half_gain_boundary_cases": half_cases, "coefficient_ceiling_cases": budget_cases,
            "rational_C_cases": constant_cases, "root_ceiling_cases": ceiling_cases,
            "affine_scalar_cases": len(affine), "affine_examples": affine,
            "analytic_pi_lt_four_is_an_input": True}


def regression_diagnostics():
    """Named exact checks preserving support, scope, wrapping and threshold distinctions."""
    _ensure(arithmetic_parameters(7, 4)["arithmetic_coefficient"] == Q(1, 2), "prime arithmetic half gain")
    _ensure(half_gain_length(7) == 2, "size-only threshold is not arithmetic optimum")
    _ensure(arithmetic_parameters(12, 5)["q"] == 3 < 5, "nonpositive raw arithmetic regime")
    _ensure(proper_support(12, 3, (0, 4, 8)), "proper nonunit differences")
    wrapped = tuple((11 + 4*j) % 12 for j in range(3))
    _ensure(wrapped == (11, 3, 7), "wrapping nonunit progression")
    zero_gain = prime_extremizer(5, 5)
    _ensure(zero_gain["gain"] == 0 and zero_gain["N"] == 20, "strict positivity boundary obstruction")
    sample = prime_extremizer(7, 5)
    _ensure(sample["N"] > 25 and sample["gain_ratio"] == Q(1, 3), "L squared prime obstruction sample")
    signed = square_covariance(4, (Q(1, 2), Q(-1, 2), Q(1, 2), Q(-1, 2)),
                               (Q(1, 2), Q(1, 2), 0, 0), 2)
    _ensure(signed["square"] == Q(1, 4), "nonunit h covariance need not vanish")
    return {"wrapped_nonunit_points": wrapped, "nonunit_covariance": signed["square"],
            "prime_half_gain_L": 4, "same_modulus_size_only_L": 2,
            "strict_positivity_boundary": zero_gain,
            "quadratic_scale_coefficient_fixed_density_sharpness_proved": False, "finite_checks_prove_asymptotics": False}


def run_checks(nmax=8):
    """Run deterministic bounded Report 278 diagnostics, with exhaustive N cap 12."""
    _integer(nmax, "nmax", 2, MAX_NMAX)
    extremizers = [prime_extremizer(prime, length) for prime in (2, 3, 5, 7, 11, 13, 17, 19, 23)
                   if prime <= (23 if nmax > 8 else 13) for length in range(2, prime + 1)]
    result = {"report": 278, "finite_diagnostics_not_proofs": True,
              "parameters": {"nmax": nmax, "support_nmax": min(nmax, 10), "moment_nmax": min(nmax, 8)},
              "exhaustive_theorem": exhaustive_theorem(nmax),
              "maximal_supports": maximal_support_diagnostics(min(nmax, 10)),
              "exact_moments": moment_diagnostics(min(nmax, 8)),
              "endpoint": endpoint_diagnostics(nmax),
              "prime_extremizers": {"cases": len(extremizers),
                                    "quotient_start_step_windows": sum(r["quotient_start_step_windows"] for r in extremizers),
                                    "rows": extremizers},
              "rounding_and_assembly": rounding_diagnostics(), "regressions": regression_diagnostics()}
    return _jsonable(result)


def main(argv=None):
    """CLI: [--full] [--nmax 2..12]; default cap 8, full cap 12.

    Explicit --nmax overrides the profile. argv must be a bounded list or tuple
    of strings. Numeric length/range are checked before conversion to int.
    """
    if argv is None:
        argv = sys.argv[1:]
    if type(argv) not in (tuple, list) or len(argv) > 3:
        raise ValueError("at most three CLI tokens are accepted")
    if any(type(arg) is not str or not 1 <= len(arg) <= DIGIT_CAP + 8 for arg in argv):
        raise ValueError("CLI tokens must be bounded strings")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="use exhaustive modulus cap 12")
    parser.add_argument("--nmax", default=None, help="override exhaustive modulus cap, 2..12")
    args = parser.parse_args(argv)
    nmax = _parse(args.nmax, "nmax", 2, MAX_NMAX) if args.nmax is not None else (12 if args.full else 8)
    print(json.dumps(run_checks(nmax), sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, CheckFailure) as error:
        print(f"diagnostic error: {error}", file=sys.stderr)
        raise SystemExit(2)
