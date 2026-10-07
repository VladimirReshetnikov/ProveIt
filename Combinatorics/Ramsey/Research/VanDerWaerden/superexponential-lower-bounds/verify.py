#!/usr/bin/env python3
"""Exact finite companion checks for Optimized Van der Waerden Bounds.

Run: python verify.py
Requires Python 3.10+ and SymPy.  Writes verification_results.json beside
this script.  These are finite checks of formulas and interfaces, not a
proof of the asymptotic theorem, an implementation of its large coloring,
or a Lean validation.  No randomness or network access is used.
"""

from __future__ import annotations

from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, factorial, gcd, isqrt, prod
from pathlib import Path
import json
import platform
import time

import sympy as sp


def require(condition: bool, message: str, **context: object) -> None:
    if not condition:
        detail = json.dumps(context, default=str, sort_keys=True)
        raise AssertionError(f"{message}: {detail}")


def endpoint_cancellations() -> dict:
    rows = []
    for colors in (2, 3):
        g = F(colors - 1, colors)
        a = g / 12
        leading = 2 * a - g / 6
        correction = -10 * a + 5 * g / 6
        linear_balance_loss = F(-4, 2) * F(-1, 3)
        require(leading == correction == 0,
                "Endpoint cancellation failed", colors=colors)
        require(linear_balance_loss == F(2, 3),
                "Shrinking-tolerance linear contribution failed")
        rows.append({"colors": colors, "a": str(a), "g": str(g),
                     "k_log_k_coefficient": str(leading),
                     "k_log_log_k_coefficient": str(correction),
                     "linear_balance_loss": str(linear_balance_loss)})
    return {"status": "passed", "arithmetic": "fractions.Fraction",
            "palettes_checked": [2, 3], "identities_checked": 6,
            "values": rows}


def logarithmic_reversion() -> dict:
    # z stands for 1/T.  V=log(T) is treated as a coefficient symbol.
    z, V, beta, A, D2 = sp.symbols("z V beta A D2")
    factor = 1 + A * z + D2 * z**2
    log_factor = sp.series(sp.log(factor), z, 0, 4).removeO()
    log_u = 1 / z - V + log_factor
    log_log_u = V + sp.series(
        sp.log(1 - V * z + z * log_factor), z, 0, 4
    ).removeO()
    normalized = sp.series(
        factor * z * (log_u - 5 * log_log_u - beta), z, 0, 4
    ).removeO().expand()
    d = 6 * V + beta
    expected_1 = A - d
    expected_2 = D2 - A * d + A + 5 * V
    require(sp.expand(normalized.coeff(z, 1) - expected_1) == 0,
            "First reversion equation differs")
    require(sp.expand(normalized.coeff(z, 2) - expected_2) == 0,
            "Second reversion equation differs")
    solutions = sp.solve([normalized.coeff(z, 1),
                          normalized.coeff(z, 2)], [A, D2], dict=True)
    require(len(solutions) == 1, "Reversion equations not uniquely solved")
    solution = solutions[0]
    require(sp.expand(solution[A] - d) == 0,
            "First correction polynomial failed")
    require(sp.expand(solution[D2] - (d**2 - d - 5 * V)) == 0,
            "Second correction polynomial failed")
    residual = sp.expand(normalized.subs(solution) - 1)
    for degree in (0, 1, 2):
        require(residual.coeff(z, degree) == 0,
                "Residual has an unexpected low-order term", degree=degree)
    third = sp.expand(residual.coeff(z, 3))
    require(sp.Poly(third, V).degree() <= 3,
            "Third-order residual grows faster than V cubed")
    return {"status": "passed", "arithmetic": "SymPy symbolic algebra",
            "first_correction": str(sp.expand(solution[A])),
            "second_correction": str(sp.expand(solution[D2])),
            "normalized_residual_coefficient_at_T_minus_3": str(third),
            "residual_orders_zero": [0, 1, 2],
            "scope": "Formal correction coefficients; analytic remainder is proved in the article."}


def palette_optimization() -> dict:
    maximum_r = 10_000
    candidates = []
    b = 0
    while 3**b <= maximum_r:
        a = 0
        while 2**a * 3**b <= maximum_r:
            candidates.append((2**a * 3**b, a, b, F(a, 24) + F(b, 18)))
            a += 1
        b += 1
    comparisons = 0
    for r in range(2, maximum_r + 1):
        feasible = [(a, b, value) for cost, a, b, value in candidates
                    if cost <= r]
        comparisons += len(feasible)
        best = max(value for _, _, value in feasible)
        m = r.bit_length() - 1
        e = int(r >= 3 * 2**(m - 1))
        formula = F(m, 24) + F(e, 72)
        optimizer = (m - e, e)
        require(best == formula, "Palette formula differs from exhaustive maximum",
                r=r, exhaustive=best, formula=formula)
        require(2**optimizer[0] * 3**optimizer[1] <= r,
                "Claimed palette optimizer is infeasible", r=r)
        require(F(optimizer[0], 24) + F(optimizer[1], 18) == best,
                "Claimed palette optimizer does not attain maximum", r=r)
        require(all(b <= 1 for a, b, value in feasible if value == best),
                "An optimal palette has two or more ternary digits", r=r)
    return {"status": "passed", "arithmetic": "integers and exact fractions",
            "r_range_inclusive": [2, maximum_r],
            "r_values_checked": maximum_r - 1,
            "candidate_integer_pairs_in_full_range": len(candidates),
            "feasible_pair_comparisons": comparisons}


def radix_prefixes(radices: tuple[int, ...]) -> tuple[int, ...]:
    prefixes = [1]
    for base in radices:
        prefixes.append(prefixes[-1] * base)
    return tuple(prefixes)


def mixed_radix_identities() -> dict:
    radix_sets = ((2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (2, 4),
                  (4, 6), (6, 4), (2, 2, 3), (3, 3, 2), (4, 2, 3),
                  (2, 3, 4), (4, 4), (6, 6))
    lengths = (2, 3, 5, 7)
    cases = wraps = 0
    rows = []
    for radices in radix_sets:
        prefixes = radix_prefixes(radices)
        modulus = prefixes[-1]
        local_cases = local_wraps = 0
        for start in range(modulus):
            for step in range(1, modulus):
                active = max(i for i, base in enumerate(prefixes[:-1])
                             if step % base == 0)
                prefix, radix = prefixes[active], radices[active]
                reduced_step = step // prefix
                require(reduced_step % radix != 0,
                        "Active mixed-radix step vanished", radices=radices,
                        start=start, step=step, active=active)
                for length in lengths:
                    for j in range(length):
                        raw = start + j * step
                        exact_quotient = start // prefix + j * reduced_step
                        require(raw // prefix == exact_quotient,
                                "Unreduced floor identity failed", radices=radices,
                                start=start, step=step, j=j)
                        wrapped_quotient = (raw % modulus) // prefix
                        require(wrapped_quotient == exact_quotient -
                                (raw // modulus) * (modulus // prefix),
                                "Wrapped quotient identity failed", radices=radices,
                                start=start, step=step, j=j)
                        require(wrapped_quotient % radix == exact_quotient % radix,
                                "Digit identity after cyclic wrap failed", radices=radices,
                                start=start, step=step, j=j)
                        local_cases += 1
                        local_wraps += int(raw >= modulus)
        cases += local_cases
        wraps += local_wraps
        rows.append({"radices": list(radices), "modulus": modulus,
                     "contains_noncoprime_pair": any(gcd(a, b) > 1
                         for a, b in combinations(radices, 2)),
                     "sample_identities": local_cases,
                     "sample_identities_with_wrap": local_wraps})
    return {"status": "passed", "arithmetic": "exact integer quotients",
            "word_lengths": list(lengths), "all_starts_and_nonzero_steps": True,
            "sample_identities": cases, "sample_identities_with_wrap": wraps,
            "identities_per_sample": 3, "radix_cases": rows}


def distance(word: tuple) -> int:
    return len(word) - max(Counter(word).values())


def cyclic_minimum(table: tuple, length: int) -> tuple[int, int, dict]:
    modulus = len(table)
    best = length
    witness = {}
    count = 0
    for start in range(modulus):
        for step in range(1, modulus):
            word = tuple(table[(start + j * step) % modulus]
                         for j in range(length))
            value = distance(word)
            count += 1
            if value < best:
                best = value
                witness = {"start": start, "step": step}
    return best, count, witness


def robust_finite_products() -> dict:
    length = 6
    factors = {
        "binary_7": (0, 0, 0, 1, 1, 1, 1),
        "ternary_7": (0, 0, 1, 1, 2, 2, 2),
        "ternary_11": tuple(n % 3 for n in range(11)),
    }
    expected_minima = {"binary_7": 2, "ternary_7": 3, "ternary_11": 2}
    factor_rows = []
    for name, table in factors.items():
        minimum, count, witness = cyclic_minimum(table, length)
        require(minimum == expected_minima[name],
                "Small factor has unexpected cyclic robustness",
                factor=name, expected=expected_minima[name], observed=minimum)
        factor_rows.append({"name": name, "colors": list(table),
                            "minimum_distance": minimum, "cyclic_words_checked": count,
                            "minimum_witness": witness})
    pairs = (("binary_7", "binary_7"), ("binary_7", "ternary_7"),
             ("ternary_7", "binary_7"), ("binary_7", "ternary_11"),
             ("ternary_11", "binary_7"))
    rows = []
    total_cyclic = total_interval = 0
    for names in pairs:
        tables = tuple(factors[name] for name in names)
        radices = tuple(map(len, tables))
        modulus = prod(radices)
        guaranteed = min(expected_minima[name] for name in names)
        # Build digits by repeated divmod, independently of the floor formula.
        combined = []
        for n in range(modulus):
            quotient = n
            color = []
            for table in tables:
                quotient, digit = divmod(quotient, len(table))
                color.append(table[digit])
            require(quotient == 0, "Mixed-radix table did not consume integer")
            combined.append(tuple(color))
        combined = tuple(combined)
        cyclic_min, cyclic_count, cyclic_witness = cyclic_minimum(combined, length)
        require(cyclic_min >= guaranteed, "Robust cyclic product failed",
                factors=names, guaranteed=guaranteed, observed=cyclic_min)
        interval_length = (length - 1) * modulus
        interval_count = 0
        interval_min = length
        interval_witness = {}
        for step in range(1, (interval_length - 1) // (length - 1) + 1):
            for start in range(interval_length - (length - 1) * step):
                word = tuple(combined[(start + j * step) % modulus]
                             for j in range(length))
                value = distance(word)
                interval_count += 1
                if value < interval_min:
                    interval_min = value
                    interval_witness = {"start": start, "step": step}
                require(value >= guaranteed, "Robust periodic extension failed",
                        factors=names, start=start, step=step,
                        guaranteed=guaranteed, observed=value)
        total_cyclic += cyclic_count
        total_interval += interval_count
        rows.append({"factors": list(names), "radices": list(radices),
                     "modulus": modulus, "interval_length": interval_length,
                     "guaranteed_minimum_distance": guaranteed,
                     "observed_cyclic_minimum": cyclic_min,
                     "observed_interval_minimum": interval_min,
                     "cyclic_words_checked": cyclic_count,
                     "interval_words_checked": interval_count,
                     "cyclic_minimum_witness": cyclic_witness,
                     "interval_minimum_witness": interval_witness})
    return {"status": "passed", "arithmetic": "exhaustive finite color counts",
            "progression_length": length, "factor_checks": factor_rows,
            "product_cases": rows, "product_cyclic_words_checked": total_cyclic,
            "product_interval_words_checked": total_interval,
            "scope": "Small illustrative colorings, not the asymptotic construction."}


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def dilation_dichotomy() -> dict:
    caps = (4, 8, 12, 20, 30, 60)
    configurations = denominator_cases = small_period_cases = primary_cases = 0
    maximum_dilation = 1
    for cap in caps:
        for cutoff in range(1, min(cap, 12) + 1):
            prime_powers = {}
            dilation = 1
            for prime in range(2, cutoff + 1):
                if is_prime(prime):
                    power = prime
                    while power * prime <= cap:
                        power *= prime
                    prime_powers[prime] = power
                    dilation *= power
            maximum_dilation = max(maximum_dilation, dilation)
            configurations += 1
            for period in range(1, cap + 1):
                if period <= cutoff:
                    require(dilation % period == 0,
                            "Small period does not divide primary dilation",
                            cap=cap, cutoff=cutoff, period=period)
                    small_period_cases += 1
                for prime, power in prime_powers.items():
                    primary_part = 1
                    remainder = period
                    while remainder % prime == 0:
                        primary_part *= prime
                        remainder //= prime
                    require(power % primary_part == 0,
                            "Full small-prime primary part was not removed",
                            cap=cap, cutoff=cutoff, period=period, prime=prime)
                    primary_cases += 1
                for numerator in range(period):
                    denominator = period // gcd(period, dilation * numerator)
                    require(denominator == 1 or denominator > cutoff,
                            "Residual denominator dichotomy failed", cap=cap,
                            cutoff=cutoff, period=period, numerator=numerator,
                            denominator=denominator)
                    denominator_cases += 1
    return {"status": "passed", "arithmetic": "integer prime powers and gcd",
            "period_caps_2M": list(caps),
            "cutoffs": "Every integer from 1 through min(2M,12)",
            "numerators": "Every residue 0 through h-1 for every 1<=h<=2M",
            "configurations": configurations,
            "denominator_cases": denominator_cases,
            "small_period_divisibility_cases": small_period_cases,
            "primary_part_cases": primary_cases,
            "largest_dilation": maximum_dilation}


@lru_cache(maxsize=None)
def pair_partitions(k: int) -> tuple[tuple[tuple[int, ...], ...], ...]:
    """All literal key partitions with block size at most two, once each."""
    if k == 0:
        return ((),)
    result = []
    for previous in pair_partitions(k - 1):
        result.append(previous + ((k - 1,),))
        for i, block in enumerate(previous):
            if len(block) == 1:
                result.append(previous[:i] + (block + (k - 1,),) + previous[i + 1:])
    return tuple(result)


@lru_cache(maxsize=None)
def increment_distribution(colors: int, probability: F,
                           blocks: tuple[tuple[int, ...], ...]) -> tuple[F, ...]:
    """Exact convolution of independent key contributions to nonzero count.

    The colors in each block are relative to the target color, so the target
    is zero.  Blocks keep their repeated-key multiplicities.  Caching equal
    distributions is not an assertion that distinct signatures define the
    same event in the proof.
    """
    distribution = (F(1),)
    for block in blocks:
        contribution = [F(0) for _ in range(len(block) + 1)]
        for increment in range(colors):
            mass = 1 - probability if increment == 0 else probability / (colors - 1)
            outside = sum((outer + increment) % colors != 0 for outer in block)
            contribution[outside] += mass
        following = [F(0) for _ in range(len(distribution) + len(block))]
        for i, old_mass in enumerate(distribution):
            for j, new_mass in enumerate(contribution):
                following[i + j] += old_mass * new_mass
        distribution = tuple(following)
    require(sum(distribution) == 1, "Exact convolution lost total probability")
    return distribution


def exponential_lower_certificate(x: F) -> F:
    # Odd Taylor truncation is <= exp(-x) for x>=0, by Taylor's remainder.
    return sum(((-x)**degree / factorial(degree) for degree in range(10)), F(0))


def repeated_key_probability_checks() -> dict:
    probabilities = (F(1, 10), F(1, 4), F(1, 2))
    cases = rich_inequalities = affine_inequalities = 0
    incompatible_cases = compatible_cases = 0
    partition_counts = {}
    by_palette = {}
    largest_affine_ratio = F(0)
    worst_affine_witness = {}
    for colors in (2, 3):
        palette_cases = 0
        for k in range(1, 6):
            partitions = pair_partitions(k)
            partition_counts[k] = len(partitions)
            require(len(set(partitions)) == len(partitions),
                    "Literal partition enumeration has duplicates", k=k)
            for outer in product(range(colors), repeat=k):
                for partition in partitions:
                    multiplicity = max(map(len, partition))
                    for target in range(colors):
                        blocks = tuple(sorted(tuple(sorted((outer[j] - target) % colors
                            for j in block)) for block in partition))
                        initially_outside = sum(value != 0 for block in blocks for value in block)
                        incompatible = any(len(set(block)) > 1 for block in blocks)
                        for probability in probabilities:
                            distribution = increment_distribution(colors, probability, blocks)
                            mean = sum((F(i) * mass for i, mass in enumerate(distribution)), F(0))
                            require(mean >= probability * k,
                                    "Expected outside count fell below pk", colors=colors,
                                    k=k, outer=outer, partition=partition, target=target,
                                    p=probability, mean=mean)
                            if incompatible:
                                require(distribution[0] == 0,
                                        "Incompatible shared-key prescriptions were not impossible",
                                        colors=colors, k=k, outer=outer,
                                        partition=partition, target=target)
                                incompatible_cases += 1
                            else:
                                exact_mono = F(1)
                                for block in blocks:
                                    exact_mono *= ((1 - probability) if block[0] == 0
                                                   else probability / (colors - 1))
                                require(distribution[0] == exact_mono,
                                        "Compatible monochromatic prescription probability differs")
                                compatible_cases += 1
                            # Verify the rich-event estimate for every integer
                            # t with 1<=t<m, not just floor(pk/2).
                            change_probability = probability / (colors - 1)
                            for t in range(1, initially_outside):
                                actual = sum(distribution[:t], F(0))
                                prefactor = sum(comb(k, j) for j in range(t + 1))
                                exponent_numerator = initially_outside - t
                                forced_keys = (exponent_numerator + multiplicity - 1) // multiplicity
                                rational_bound = prefactor * change_probability**forced_keys
                                require(actual <= rational_bound,
                                        "Exact rich-event upper bound failed", colors=colors,
                                        k=k, outer=outer, partition=partition, target=target,
                                        p=probability, t=t, actual=actual, bound=rational_bound)
                                # The article has exponent (m-t)/mu.  Raising
                                # positive sides to mu compares it rationally.
                                require(actual**multiplicity <=
                                        prefactor**multiplicity * change_probability**exponent_numerator,
                                        "Article rich-event fractional-power bound failed")
                                rich_inequalities += 1
                            threshold = probability * k / 2
                            actual_tail = sum((mass for i, mass in enumerate(distribution)
                                               if F(i) < threshold), F(0))
                            x = probability * k / (8 * multiplicity)
                            certificate = exponential_lower_certificate(x)
                            require(certificate > 0 and actual_tail <= certificate,
                                    "Affine lower-tail inequality not certified exactly",
                                    colors=colors, k=k, outer=outer, partition=partition,
                                    target=target, p=probability, actual=actual_tail,
                                    exp_lower_certificate=certificate)
                            ratio = actual_tail / certificate
                            if ratio > largest_affine_ratio:
                                largest_affine_ratio = ratio
                                worst_affine_witness = {"colors": colors, "k": k,
                                    "outer_word": list(outer),
                                    "key_blocks": [list(block) for block in partition],
                                    "target": target, "p": str(probability),
                                    "probability": str(actual_tail),
                                    "rational_lower_bound_for_exponential": str(certificate)}
                            affine_inequalities += 1
                            cases += 1
                            palette_cases += 1
        by_palette[colors] = palette_cases
    return {"status": "passed", "arithmetic": "exact Fraction convolution",
            "k_range_inclusive": [1, 5], "palettes": [2, 3],
            "probabilities": [str(p) for p in probabilities],
            "outer_words": "All s^k words, all target colors, and all literal key partitions with block size<=2",
            "partitions_by_k": partition_counts, "distribution_cases": cases,
            "distribution_cases_by_palette": by_palette,
            "distinct_cached_convolutions": increment_distribution.cache_info().currsize,
            "rich_threshold_inequalities": rich_inequalities,
            "affine_tail_inequalities": affine_inequalities,
            "incompatible_monochromatic_prescription_cases": incompatible_cases,
            "compatible_monochromatic_prescription_cases": compatible_cases,
            "affine_certificate": "P(S<pk/2) <= sum_{j=0}^9 (-x)^j/j! <= exp(-x), x=pk/(8*mu)",
            "largest_affine_probability_to_certificate_ratio": str(largest_affine_ratio),
            "worst_affine_witness": worst_affine_witness,
            "scope": "Finite shared-variable probabilities, not a validation of the asymptotic event count."}


def half_open_norm_bands() -> dict:
    parameters = tuple(F(n, 8) for n in range(-32, 33))
    offsets = (F(0), F(1, 4), F(1, 2), F(3, 4), F(1))
    band_cases = triple_candidates = separated_pairs = 0
    for offset in offsets:
        for band in range(19):
            members = tuple(t for t in parameters if band <= t*t + offset < band + 1)
            for left, right in combinations(members, 2):
                if right - left >= 1:
                    separated_pairs += 1
                    require(not (0 <= left < right or left < right <= 0),
                            "Two separated points on the same half-line share a norm band",
                            offset=offset, band=band, left=left, right=right)
            for left, middle, right in combinations(members, 3):
                triple_candidates += 1
                require(not (middle - left >= 1 and right - middle >= 1),
                        "Three one-separated points share a half-open norm band",
                        offset=offset, band=band, triple=(left, middle, right))
            band_cases += 1
    witness = (F(-1, 2), F(1, 2))
    require(witness[1] - witness[0] == 1 and
            all(0 <= t*t < 1 for t in witness),
            "Two-point sharpness witness failed")
    closed_counterexample = (F(-1), F(0), F(1))
    require(all(0 <= t*t <= 1 for t in closed_counterexample),
            "Closed-boundary comparison failed")
    require(sum(0 <= t*t < 1 for t in closed_counterexample) == 1,
            "Half-open outer boundary was not enforced")
    return {"status": "passed", "arithmetic": "exact rational squared norms",
            "parameter_grid": "t=n/8, -32<=n<=32", "grid_points": len(parameters),
            "offsets": [str(value) for value in offsets],
            "integer_bands_inclusive": [0, 18], "band_cases": band_cases,
            "triple_candidates_checked": triple_candidates,
            "one_separated_pairs_found": separated_pairs,
            "sharp_two_point_witness_in_band_0": [str(value) for value in witness],
            "closed_band_three_point_counterexample": [str(value) for value in closed_counterexample],
            "scope": "Finite rational examples and boundary cases; the general line proof is in the article."}


def main() -> None:
    start = time.perf_counter()
    report = {
        "title": "Finite verification companion: Optimized Van der Waerden Bounds",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "running",
        "scope": "Finite exact checks of stated algebraic and probabilistic interfaces. Not a proof of the infinite theorem, not a construction at the asymptotic threshold, and not Lean validation.",
        "python_version": platform.python_version(), "sympy_version": sp.__version__,
        "checks": {},
    }
    output = Path(__file__).resolve().with_name("verification_results.json")
    checks = (
        ("endpoint_cancellations", endpoint_cancellations),
        ("logarithmic_reversion", logarithmic_reversion),
        ("palette_optimization", palette_optimization),
        ("mixed_radix_identities", mixed_radix_identities),
        ("robust_finite_products", robust_finite_products),
        ("dilation_dichotomy", dilation_dichotomy),
        ("repeated_key_probabilities", repeated_key_probability_checks),
        ("half_open_norm_bands", half_open_norm_bands),
    )
    try:
        for name, check in checks:
            result = check()
            report["checks"][name] = result
            print(f"PASS {name}", flush=True)
    except Exception as error:
        report["status"] = "failed"
        report["failure"] = {"check": name, "type": type(error).__name__,
                             "message": str(error)}
        report["elapsed_seconds"] = round(time.perf_counter() - start, 3)
        output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
        raise
    report["status"] = "passed"
    report["elapsed_seconds"] = round(time.perf_counter() - start, 3)
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"All {len(checks)} check groups passed; wrote {output.name}.", flush=True)


if __name__ == "__main__":
    main()
