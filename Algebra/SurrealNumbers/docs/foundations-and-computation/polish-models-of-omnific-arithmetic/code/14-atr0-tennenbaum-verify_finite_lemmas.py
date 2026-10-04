#!/usr/bin/env python3
"""Deterministic exact finite checks for the accompanying research manuscript.

Run with:
    python3 verify_finite_lemmas.py > finite_check_results.txt

Only Python's standard library is used. All numerical calculations use integers
or fractions.Fraction; there is no floating-point approximation or random input.

These checks concern standard finite instances of elementary identities and
inequalities. They do NOT prove their universal versions, construct a nonstandard
model, verify the MRDP theorem, formalize ATR0, or establish any infinite
topological, Borel, category, measure, or surreal-number theorem. The manuscript's
mathematical proofs supply those arguments independently.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import factorial, isqrt, prod


class CheckLog:
    """Count successful predicates, and fail even when Python uses -O."""

    def __init__(self):
        self.counts = Counter()
        self.coverage = {}

    def require(self, category, condition, context):
        if not condition:
            raise AssertionError(f"{category}: {context}")
        self.counts[category] += 1

    def record(self, label, value):
        self.coverage[label] = value


def root_chain(c):
    """Stop once standard iteration reaches 1; never simulate an infinite cut."""
    terms = [c]
    while terms[-1] > 1:
        terms.append(isqrt(terms[-1]))
    return terms


def sample_interval(last):
    """Exhaust small intervals; otherwise include endpoints and interior points."""
    if last <= 64:
        return range(last + 1)
    return sorted({0, 1, last // 3, last // 2, last - 1, last})


def check_root_scales(log):
    thresholds = list(range(65)) + [127, 255, 1000, 2**16, 10**12, 2**128]
    initial_values = [1, 2**16 + 1, 2**128 + 123, 2**512, 2**4096]
    threshold_cases = [
        (b, c0, max(c0, (b + 2) ** 4))
        for b in thresholds
        for c0 in initial_values
    ]

    carriers = set(range(1, 20001))
    for base in range(2, 101):
        carriers.update(base**4 + delta for delta in (-1, 0, 1))
    for k in range(1, 13):
        carriers.update(2 ** (2**k) + delta for delta in (-1, 0, 1))
    carriers.update(c for _, _, c in threshold_cases)

    admissible_levels = 0
    quotient_samples = 0
    x_samples = 0
    for c in sorted(carriers):
        terms = root_chain(c)
        quotients = [c // t for t in terms]
        context = f"c has {c.bit_length()} bits"
        for i, t in enumerate(terms):
            q = quotients[i]
            log.require("root quotient bounds", q * t <= c < (q + 1) * t,
                        f"{context}, level={i}")
        for i in range(len(terms) - 1):
            t, s = terms[i : i + 2]
            log.require("floor-square bounds", s * s <= t < (s + 1) ** 2,
                        f"{context}, level={i}")
            for x in sample_interval(t):
                q, r = divmod(x, s + 1)
                log.require("quotient-tree child bounds", 0 <= q <= s and 0 <= r <= s,
                            f"{context}, level={i}, sampled x")
                log.require("quotient-tree reconstruction", (s + 1) * q + r == x,
                            f"{context}, level={i}, sampled x")
                quotient_samples += 1

        for n in range(len(terms) - 2):
            t0, t1, t2 = terms[n : n + 3]
            if t2 <= 8:
                continue
            admissible_levels += 1
            q0, q1 = quotients[n : n + 2]
            detail = f"{context}, admissible level={n}"
            log.require("root-scale separation", q1 >= q0 * t1, detail)
            log.require("root-scale separation", q0 * t1 >= q0 * t2**2, detail)
            log.require("root-scale separation", q0 * t2**2 > 8 * q0 * t2, detail)
            log.require("root-scale separation", q1 > 8 * q0 * t2, detail)
            log.require("scale-set upper bound", q0 * t2 < c, detail)
            log.require("extremal perturbation separation", q1 > 8 * q0 * (t2 - 1),
                        detail)
            for i in sample_interval(t2 - 1):
                x = q0 * i
                log.require("sampled scale-set points", 0 <= x < c and x % q0 == 0,
                            f"{detail}, sampled index")
                x_samples += 1

    for b, c0, c in threshold_cases:
        t1 = isqrt(c)
        q1 = c // t1
        detail = f"b={b}, c0 has {c0.bit_length()} bits"
        log.require("threshold scale", c >= (b + 2) ** 4, detail)
        log.require("threshold scale", q1 >= t1, detail)
        log.require("threshold scale", t1 >= (b + 2) ** 2, detail)
        log.require("threshold scale", q1 > b, detail)

    log.record("Distinct root-scale carrier integers", len(carriers))
    log.record("Exhaustive root-scale carrier interval", "1 through 20000")
    log.record("Largest carrier bit length", max(c.bit_length() for c in carriers))
    log.record("Double-exponential samples", "2^(2^k) and adjacent integers, 1 <= k <= 12")
    log.record("Admissible root levels with t[n+2] > 8", admissible_levels)
    log.record("Quotient/remainder tree samples", quotient_samples)
    log.record("Sampled points in scale sets X_n", x_samples)
    log.record("Threshold pairs (b, initial c0)", len(threshold_cases))


def growth_families(seeds, factor, length):
    """Include multiplicative growth and near-boundary strict recurrences."""
    families = []
    for seed in seeds:
        for mode in range(3):
            values = [seed]
            for i in range(length - 1):
                if mode == 0:
                    next_value = (factor + 1) * values[-1]
                elif mode == 1:
                    next_value = factor * values[-1] + 1
                else:
                    next_value = factor * values[-1] + 1 + (i * i + seed) % 7
                values.append(next_value)
            families.append((f"seed={seed}, mode={mode}", values))
    return families


def subset_sums(values):
    """Entry m is the sum over the positions whose bits in m are 1."""
    sums = [0]
    for value in values:
        sums.extend(total + value for total in sums[:])
    return sums


def check_additive_growth(log):
    families = growth_families([1, 2, 17, 1001], 8, 12)
    subset_count = 0
    pair_count = 0
    absorption_count = 0
    for label, values in families:
        prefix = 0
        for n, value in enumerate(values):
            log.require("additive prefix domination", 7 * prefix < value,
                        f"{label}, n={n}")
            if n:
                log.require("additive strict growth", value > 8 * values[n - 1],
                            f"{label}, n={n}")
            prefix += value

        sums = subset_sums(values)
        subset_count += len(sums)
        log.require("all enumerated subset sums distinct", len(set(sums)) == 2**len(values),
                    label)
        small_sums = subset_sums(values[:8])
        for left, right in combinations(range(len(small_sums)), 2):
            m = (left ^ right).bit_length() - 1
            if not left & (1 << m):
                left, right = right, left
            difference = small_sums[left] - small_sums[right]
            earlier = sum(values[:m])
            detail = f"{label}, largest differing position={m}"
            log.require("additive largest-index domination", difference > 0, detail)
            log.require("additive largest-index domination", difference >= values[m] - earlier,
                        detail)
            pair_count += 1

        for n in range(len(values) - 1):
            for j in range(len(values) - 1):
                k = max(n, j) + 1
                log.require("additive one-bit absorption", values[k] > values[n] + 2 * values[j],
                            f"{label}, n={n}, j={j}")
                absorption_count += 1

    log.record("Additive growth families / length", f"{len(families)} / 12")
    log.record("Additive subset sums enumerated", subset_count)
    log.record("Additive subset pairs checked (8 positions)", pair_count)
    log.record("Additive absorption index pairs", absorption_count)


def check_product_growth(log):
    # y_i = 2^ell_i. Every comparison below is translated exactly to integers:
    # Q_n^4 < y_n                 iff 4*sum(ell_i for i<n) < ell_n;
    # p^2 > y_m*q^2              iff 2*log2(p) > ell_m + 2*log2(q);
    # y_k > y_n*y_j^2            iff ell_k > ell_n + 2*ell_j.
    # No numerical logarithm is calculated.
    families = growth_families([1, 2, 11], 5, 12)
    block_pairs = 0
    absorption_pairs = 0
    actual_products = 0
    for label, exponents in families:
        prefix = [0]
        for exponent in exponents:
            prefix.append(prefix[-1] + exponent)
        for n, exponent in enumerate(exponents):
            log.require("logarithmic product prefix bound", 4 * prefix[n] < exponent,
                        f"{label}, n={n}")
            if n:
                log.require("logarithmic product strict growth", exponent > 5 * exponents[n - 1],
                            f"{label}, n={n}")

        for n in range(len(exponents) - 1):
            for j in range(len(exponents) - 1):
                k = max(n, j) + 1
                log.require("logarithmic product absorption",
                            exponents[k] > exponents[n] + 2 * exponents[j],
                            f"{label}, n={n}, j={j}")
                absorption_pairs += 1

            for length in range(1, min(6, len(exponents) - n - 1) + 1):
                block = exponents[n + 1 : n + length + 1]
                sums = subset_sums(block)
                for left, right in combinations(range(2**length), 2):
                    local_m = (left ^ right).bit_length() - 1
                    m = n + 1 + local_m
                    if not left & (1 << local_m):
                        left, right = right, left
                    p_exp = sums[left & ~right]
                    q_exp = sums[right & ~left]
                    detail = f"{label}, n={n}, block length={length}, largest={m}"
                    log.require("far-block product domination", p_exp >= exponents[m], detail)
                    log.require("far-block product domination", q_exp <= prefix[m], detail)
                    log.require("far-block product domination",
                                2 * p_exp > exponents[m] + 2 * q_exp, detail)
                    log.require("far-block product domination",
                                exponents[m] + 2 * q_exp > exponents[n] + 2 * q_exp,
                                detail)
                    block_pairs += 1

        # Independently check short prefixes as actual integer powers/products.
        # This also cross-checks the exact logarithmic interpretation above.
        actual = [2**exponent for exponent in exponents[:4]]
        for n, value in enumerate(actual):
            product = prod(actual[:n])
            log.require("actual integer product cross-check", product**4 < value,
                        f"{label}, n={n}")
            log.require("actual integer product cross-check", product == 2**prefix[n],
                        f"{label}, n={n}")
            actual_products += 1

    log.record("Logarithmic product families / length", f"{len(families)} / 12")
    log.record("Far-block subset pairs checked (block lengths 1..6)", block_pairs)
    log.record("Multiplicative absorption index pairs", absorption_pairs)
    log.record("Actual integer product prefixes cross-checked", actual_products)


def scale_pair(scalar, point):
    return tuple(scalar * coordinate for coordinate in point)


def add_pairs(left, right):
    return tuple(a + b for a, b in zip(left, right))


def check_factorial_group(log):
    maximum = 32
    facts = [factorial(n) for n in range(maximum + 1)]
    totals = [0] * (maximum + 1)
    for n in range(1, maximum):
        totals[n + 1] = totals[n] + facts[n]
    unit = (Fraction(1), Fraction(0))
    generators = {
        n: (Fraction(totals[n], facts[n]), Fraction(1, facts[n]))
        for n in range(1, maximum + 1)
    }

    for n in range(1, maximum):
        log.require("factorial generator recurrence",
                    scale_pair(n + 1, generators[n + 1]) == add_pairs(generators[n], unit),
                    f"n={n}")
    for n in range(1, maximum + 1):
        log.require("factorial telescoping identity",
                    scale_pair(facts[n], generators[n])
                    == add_pairs(generators[1], scale_pair(totals[n], unit)),
                    f"n={n}")
        log.require("factorial generator positivity", generators[n][1] > 0, f"n={n}")
        if n >= 3:
            log.require("factorial sum bound", totals[n] <= 2 * facts[n - 1], f"n={n}")
            log.require("factorial complementary bound",
                        facts[n] - totals[n] >= (n - 2) * facts[n - 1], f"n={n}")

    normal_form_pairs = 0
    for large in range(1, maximum + 1):
        for small in range(1, large + 1):
            difference = totals[large] - totals[small]
            log.require("factorial normal-form coefficients", difference % facts[small] == 0,
                        f"i={small}, N={large}")
            reconstructed = add_pairs(
                scale_pair(facts[large] // facts[small], generators[large]),
                scale_pair(-(difference // facts[small]), unit),
            )
            log.require("factorial normal-form identity", reconstructed == generators[small],
                        f"i={small}, N={large}")
            normal_form_pairs += 1

    kernel_samples = 0
    for n in range(1, 13):
        for m in range(-5, 6):
            for k in range(-5, 6):
                point = add_pairs(scale_pair(m, unit), scale_pair(k, generators[n]))
                log.require("finite kernel samples", point[1] == Fraction(k, facts[n]),
                            f"N={n}, m={m}, k={k}")
                log.require("finite kernel samples", (point[1] == 0) == (k == 0),
                            f"N={n}, m={m}, k={k}")
                kernel_samples += 1

    witness_histogram = Counter()
    candidates = range(-1000, 1001)
    for first in candidates:
        value = Fraction(first)
        for n in range(1, 13):
            log.require("rational retraction recurrence",
                        value == Fraction(first + totals[n], facts[n]),
                        f"b1={first}, n={n}")
            value = (value + 1) / (n + 1)

        witness = next(
            (n for n in range(1, maximum + 1) if 0 < first + totals[n] < facts[n]),
            None,
        )
        log.require("bounded retraction obstruction", witness is not None, f"b1={first}")
        numerator = first + totals[witness]
        log.require("bounded retraction obstruction", numerator % facts[witness] != 0,
                    f"b1={first}, witness n={witness}")
        log.require("bounded retraction obstruction",
                    Fraction(numerator, facts[witness]).denominator > 1,
                    f"b1={first}, witness n={witness}")
        witness_histogram[witness] += 1

    log.record("Factorial generators checked", maximum)
    log.record("All normal-form index pairs 1 <= i <= N <= 32", normal_form_pairs)
    log.record("Kernel samples (N=1..12, m,k=-5..5)", kernel_samples)
    log.record("Proposed retraction initial values b1", "-1000 through 1000 (2001 values)")
    log.record("Largest first obstruction witness n", max(witness_histogram))
    log.record("First-witness histogram n:count",
               ", ".join(f"{n}:{count}" for n, count in sorted(witness_histogram.items())))


def check_fusion_constants(log):
    for n in range(65):
        tail = sum((Fraction(1, 2 ** (i + 4)) for i in range(n, n + 128)), Fraction(0))
        bound = Fraction(1, 2 ** (n + 3))
        log.require("finite geometric tail constants", tail < bound, f"N={n}")
        log.require("finite geometric tail constants",
                    bound - tail == Fraction(1, 2 ** (n + 131)), f"N={n}")
        log.require("fusion separation coefficient", 1 - 2 * bound > 0, f"N={n}")
    log.record("Geometric-tail starting indices / summands", "65 / 128")


def main():
    log = CheckLog()
    check_root_scales(log)
    check_additive_growth(log)
    check_product_growth(log)
    check_factorial_group(log)
    check_fusion_constants(log)

    print("EXACT FINITE CHECKS: PASS")
    print("Companion to Diophantine Definability and Topological Arithmetic")
    print("Deterministic Python 3; standard library; integer/Fraction arithmetic only.")
    print()
    print("COVERAGE")
    for label, value in log.coverage.items():
        print(f"{label}: {value}")
    print()
    print("SUCCESSFUL PREDICATES BY CATEGORY")
    for category, count in sorted(log.counts.items()):
        print(f"{category}: {count}")
    print(f"TOTAL SUCCESSFUL PREDICATES: {sum(log.counts.values())}")
    print()
    print("INTERPRETATION AND LIMITATIONS")
    print("1. Every tested value is a standard integer or exact rational number.")
    print("2. Strict scale separation is checked at levels satisfying t[n+2] > 8;")
    print("   standard chains eventually leave this regime and terminate at 1.")
    print("3. Subset and far-block checks exhaust the reported finite mask ranges;")
    print("   they do not exhaust all possible growth sequences or all block sizes.")
    print("4. Product logarithms mean exact integer exponents ell_i with y_i=2^ell_i.")
    print("   No floating-point logarithms or approximate exponentials are used.")
    print("5. The retraction check covers b1=-1000..1000. The argument for every")
    print("   integer b1 is the symbolic proof in the manuscript, not this search.")
    print("6. No computation here proves internal MRDP, verifies a weak-arithmetic")
    print("   derivation, constructs a nonstandard model, or formalizes ATR0.")
    print("7. No computation here proves the infinite fusion, Borel, category,")
    print("   measure, Polish-model, splitting, or surreal-embedding theorems.")
    print("8. These are reproducible finite checks of arithmetic details, not a")
    print("   proof-assistant certificate or a substitute for the mathematical proofs.")


if __name__ == "__main__":
    main()
