#!/usr/bin/env python3
r"""Exact certificate for the two-cube theorem in active dimension three.

THEOREM BEING CERTIFIED
----------------------
For every odd prime p, let P be the 3^8 multiaffine polynomials over F_p
taking values in {-1,0,1} at every vertex of {0,1}^3. A nonconstant f in P
has f(X+t) in P only when t lies in

    B = {t_i=0,1,-1 for some i, or t_i=t_j or t_i=-t_j for some i<j}.

The reverse containment follows from affine polynomials, as proved in the
accompanying article. Thus the nondegenerate translation count is exactly
(p-3)(p-5)(p-7). Including the zero-side arrangements gives

    delta_{3,1}(p) = 1-(p-1)^3(p-3)(p-5)(p-7)/p^6.

The analytic input from the article is the rank-at-most-two containment
theorem: if the span of a ternary multiaffine polynomial's first partial
derivatives has dimension at most two, every successful nonconstant
translation lies in B, for p>=11. The finite certificate below treats
all remaining dimension-three cases. No broad claim of exactness for
dimensions four or higher is used.

POLYNOMIAL AND INTEGER CONVENTIONS
---------------------------------
Boolean vertices are indexed by masks 0,...,7; the bit with value 2^i is
coordinate i. Mobius inversion transforms a ternary value vector into
the INTEGER coefficients

    (h,e,f,b,g,c,d,a),
    F(X,Y,Z)=h+eX+fY+bXY+gZ+cXZ+dYZ+aXYZ.

Every ternary polynomial over every odd prime is represented, because
the three vertex values remain distinct and the Boolean interpolation
transform is invertible. Coefficients satisfy |a|<=8 and |b|,|c|,|d|<=4.

LARGE PRIMES: CUBICS
--------------------
For p>=17, equality of top coefficients modulo p is equality of the
integer representatives in [-8,8]. Common negation lets us take a>0.
For F and G with the same a, write

    u=d_G-d_F, v=c_G-c_F, w=b_G-b_F.

Any successful translation MUST be (u/a,v/a,w/a). If this rational
candidate lies in B, so does its reduction modulo p. Otherwise define

    R_X = a(e_G-e_F)-(b v+c w+v w),
    R_Y = a(f_G-f_F)-(b u+d w+u w),
    R_Z = a(g_G-g_F)-(c u+d v+u v),
    R_0 = a^2(h_G-h_F)
          -a(e u+f v+g w)-buv-cuw-dvw-uvw.

Translation is possible modulo p only if p divides all four integers.
The program exhausts every ordered pair with positive a. Exactly 12,288
have a rational candidate outside B. Their nonnegative residual gcds
have histogram {1:9408, 2:2496, 3:96, 4:288}; none admits a prime >=17.
For every one of those candidates, the residual equations are also
checked against a separate direct expansion of F(X+t), with all
denominators cleared. This checks the algebra as well as the counts.

LARGE PRIMES: QUADRATICS
-----------------------
Let H be the symmetric, zero-diagonal Hessian matrix, let l,l' be the
linear-coefficient vectors of F,G, and let h,h' be their constants.
Their quadratic coefficients must agree as integers for p>=17. A
translation is equivalent, in odd characteristic, to the linear system

    M t = q,    M = [ H ; (l+l')^T ],
                q = [ l'-l ; 2(h'-h) ].

If M has rational rank three, choose its first nonzero 3-by-3 row minor
in lexicographic order, and use Cramer's rule to obtain t=n/D. There
are exactly 8,788 such ordered pairs. The selected absolute determinant
histogram is

    {1:3264, 2:3008, 3:576, 4:1416, 6:216, 8:252, 12:24, 16:32}.

Hence these determinants are invertible at every p>=17. Among those
pairs, exactly 480 rational candidates lie outside B. The gcds of the
four entries of M n-D q have histogram {3:288, 7:192}; therefore none
is a translation modulo a prime >=17.

Discarding rational rank-below-three M does not lose a case. Matrix
rank cannot increase after reduction modulo a prime. If Ht=l'-l is
consistent, (l+l')^T is congruent to 2l^T modulo the row space of H.
Consequently rank(M) equals the derivative rank of F for every odd p.
A successful pair with rank(M)<3 is therefore covered by the analytic
rank-at-most-two theorem. This argument also allows derivative rank
to drop modulo a prime; no unproved rank-stability assumption is used.

SMALL ODD PRIMES
---------------
For p=3,5,7 there are fewer than three unordered nonzero sign pairs
after removing {1,-1}. Thus B already fills F_p^3.

For p=11,13 every vector outside B has three distinct absolute residues
from {2,...,(p-1)/2}. Coordinate permutations and reflections X_i->1-X_i
preserve ternary cube values and change t by signed permutations. The
action is free outside B, of size 3! 2^3=48. We therefore check ALL
ternary polynomials at the four representatives for p=11 and the ten
representatives for p=13. At each representative, only the three
constant polynomials survive. This is an exhaustive reduction by an
explicit symmetry, not sampling.

CERTIFICATE FORMAT AND REPRODUCIBILITY
--------------------------------------
The JSON output uses schema_version=1. Its top-level fields are:

  theorem: exact statement, formula, assumptions, and analytic input;
  enumeration: vertex order, coefficient order, complete pattern count;
  cubic: group sizes, exhaustive pair count, gcd histograms, checks;
  quadratic: exhaustive matrix-rank/Cramer counts and gcd histograms;
  small_primes: all signed-permutation representatives and survivors;
  exact_formula: integer Laurent coefficients and finite fraction checks;
  verification: mathematical arithmetic, dependencies, source digest.

JSON object keys representing integer histogram bins are decimal strings.
All mathematical arithmetic uses Python integers or fractions. The
certificate contains deterministic summaries; this program regenerates
every case instead of trusting those summaries. This is an exhaustive
computer-assisted finite proof coupled to the stated analytic lemma,
not a kernel-checked formal proof.

Run: python3 verify_dimension_three.py
The only dependencies are Python's standard-library modules. By default
the certificate is written beside this file; --output chooses another
location. Running with -O is refused. No mathematical check uses assert.
"""

from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from math import gcd, prod
from pathlib import Path
from time import perf_counter
import json


if not __debug__:
    raise SystemExit("Verification refuses python -O; use ordinary python3.")


class VerificationError(RuntimeError):
    """A finite certificate check failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def equal(actual, expected, message):
    if actual != expected:
        raise VerificationError(f"{message}: expected {expected!r}, got {actual!r}")


def polynomial_coefficients(values):
    result = list(values)
    for coordinate in range(3):
        for mask in range(8):
            if mask & (1 << coordinate):
                result[mask] -= result[mask ^ (1 << coordinate)]
    return tuple(result)


def evaluate(coefficients, point, prime):
    h, e, f, b, g, c, d, a = coefficients
    x, y, z = point
    return (h + e*x + f*y + b*x*y + g*z + c*x*z + d*y*z
            + a*x*y*z) % prime


def signed_divisor(point, prime):
    if any(x % prime in (0, 1, prime - 1) for x in point):
        return True
    return any((point[i] - point[j]) % prime == 0
               or (point[i] + point[j]) % prime == 0
               for i in range(3) for j in range(i))


def rational_outside_divisor(numerators, denominator):
    absolute = tuple(abs(x) for x in numerators)
    return (all(x not in (0, abs(denominator)) for x in absolute)
            and len(set(absolute)) == 3)


def prime_divisors(integer):
    value = abs(integer)
    require(value != 0, "A zero gcd or denominator has no finite prime-divisor list")
    result = set()
    divisor = 2
    while divisor * divisor <= value:
        if value % divisor == 0:
            result.add(divisor)
            while value % divisor == 0:
                value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        result.add(value)
    return result


def histogram_primes(histogram):
    result = set()
    for key in histogram:
        result.update(prime_divisors(key))
    return sorted(result)


def sorted_histogram(histogram):
    return dict(sorted(histogram.items()))


def scaled_translate(coefficients, numerators, denominator):
    """Coefficients of denominator^3 F(X+numerators/denominator).

    Expand monomials directly. This does not use the residual formulae
    whose algebra it checks.
    """
    result = [0] * 8
    powers = [denominator ** j for j in range(4)]
    for mask, coefficient in enumerate(coefficients):
        if not coefficient:
            continue
        submask = mask
        while True:
            shifted = mask ^ submask
            value = coefficient * powers[3 - shifted.bit_count()]
            for coordinate in range(3):
                if shifted & (1 << coordinate):
                    value *= numerators[coordinate]
            result[submask] += value
            if submask == 0:
                break
            submask = (submask - 1) & mask
    return result


def determinant3(matrix):
    (a, b, c), (d, e, f), (g, h, i) = matrix
    return a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)


def cubic_certificate(rows):
    groups = defaultdict(list)
    for row in rows:
        if row[7] > 0:
            groups[row[7]].append(row)
    expected_sizes = {1: 1016, 2: 784, 3: 504, 4: 266,
                      5: 112, 6: 36, 7: 8, 8: 1}
    equal({a: len(group) for a, group in sorted(groups.items())},
          expected_sizes, "Positive cubic group sizes")
    total_pairs = 0
    outside_count = 0
    direct_checks = 0
    residual_gcds = Counter()
    by_a = []
    first_examples = {}
    for a in range(1, 9):
        local_gcds = Counter()
        group = groups[a]
        total_pairs += len(group) ** 2
        for row in group:
            h, e, f, b, g, c, d, _ = row
            for other in group:
                u, v, w = other[6] - d, other[5] - c, other[3] - b
                if not rational_outside_divisor((u, v, w), a):
                    continue
                outside_count += 1
                rx = a*(other[1] - e) - (b*v + c*w + v*w)
                ry = a*(other[2] - f) - (b*u + d*w + u*w)
                rz = a*(other[4] - g) - (c*u + d*v + u*v)
                r0 = (a*a*(other[0] - h)
                      - a*(e*u + f*v + g*w)
                      - b*u*v - c*u*w - d*v*w - u*v*w)
                divisor = gcd(rx, ry, rz, r0)
                require(divisor != 0, "A rational cubic translation escaped the divisor")
                residual_gcds[divisor] += 1
                local_gcds[divisor] += 1
                translated = scaled_translate(row, (u, v, w), a)
                differences = [a**3*y - x for x, y in zip(translated, other)]
                equal(differences,
                      [a*r0, a*a*rx, a*a*ry, 0, a*a*rz, 0, 0, 0],
                      "Cubic residuals versus direct monomial translation")
                direct_checks += 1
                if divisor not in first_examples:
                    first_examples[divisor] = {
                        "source_coefficients": row,
                        "target_coefficients": other,
                        "translation_numerators": [u, v, w],
                        "translation_denominator": a,
                        "residuals_x_y_z_constant": [rx, ry, rz, r0],
                    }
        by_a.append({"top_coefficient": a, "polynomial_count": len(group),
                     "ordered_pairs": len(group) ** 2,
                     "outside_candidates": sum(local_gcds.values()),
                     "residual_gcd_histogram": sorted_histogram(local_gcds)})
    equal(total_pairs, 1985589, "Cubic ordered-pair count")
    equal(outside_count, 12288, "Cubic outside-candidate count")
    equal(residual_gcds, Counter({1: 9408, 2: 2496, 3: 96, 4: 288}),
          "Cubic residual gcd histogram")
    equal(histogram_primes(residual_gcds), [2, 3], "Cubic residual primes")
    equal(direct_checks, outside_count, "Every outside cubic candidate was cross-checked")
    return {
        "positive_top_coefficient_group_sizes": expected_sizes,
        "ordered_pairs_examined": total_pairs,
        "outside_divisor_candidates": outside_count,
        "residual_gcd_histogram": sorted_histogram(residual_gcds),
        "residual_prime_divisors": histogram_primes(residual_gcds),
        "direct_scaled_translation_checks": direct_checks,
        "by_top_coefficient": by_a,
        "first_example_for_each_gcd": first_examples,
        "prime_range_excluded": "Every prime p>=17",
    }


def derivative_rank_quadratic(row):
    _, e, f, b, g, c, d, _ = row
    if not (b or c or d):
        return 1 if e or f or g else 0
    derivative_matrix = [[0, b, c, e], [b, 0, d, f], [c, d, 0, g]]
    for columns in combinations(range(4), 3):
        minor = [[r[j] for j in columns] for r in derivative_matrix]
        if determinant3(minor):
            return 3
    return 2


def quadratic_certificate(rows):
    quadratics = [row for row in rows if row[7] == 0]
    equal(len(quadratics), 1107, "Number of polynomials of degree at most two")
    ranks = Counter(derivative_rank_quadratic(row) for row in quadratics)
    equal(ranks, Counter({0: 3, 1: 30, 2: 270, 3: 804}),
          "Quadratic derivative-rank census over the rationals")
    groups = defaultdict(list)
    for row in quadratics:
        if row[3] or row[5] or row[6]:
            groups[row[3], row[5], row[6]].append(row)
    selected_determinants = Counter()
    residual_gcds = Counter()
    total_pairs = 0
    full_rank_pairs = 0
    lower_rank_pairs = 0
    outside_count = 0
    exact_translation_checks = 0
    first_examples = {}
    for key in sorted(groups):
        group = groups[key]
        for row in group:
            h, e, f, b, g, c, d, _ = row
            for other in group:
                total_pairs += 1
                hh, ee, ff, _, gg, _, _, _ = other
                matrix = [[0, b, c], [b, 0, d], [c, d, 0],
                          [e + ee, f + ff, g + gg]]
                rhs = [ee - e, ff - f, gg - g, 2*(hh - h)]
                chosen = None
                for indices in combinations(range(4), 3):
                    square = [matrix[i] for i in indices]
                    denominator = determinant3(square)
                    if denominator:
                        chosen = (indices, square, denominator)
                        break
                if chosen is None:
                    lower_rank_pairs += 1
                    continue
                indices, square, denominator = chosen
                full_rank_pairs += 1
                selected_determinants[abs(denominator)] += 1
                numerators = []
                for column in range(3):
                    replacement = [r.copy() for r in square]
                    for j, original_row in enumerate(indices):
                        replacement[j][column] = rhs[original_row]
                    numerators.append(determinant3(replacement))
                residuals = [sum(x*y for x, y in zip(r, numerators))
                             - denominator*s for r, s in zip(matrix, rhs)]
                if not any(residuals):
                    equal(scaled_translate(row, numerators, denominator),
                          [denominator**3*x for x in other],
                          "Quadratic linearization versus direct monomial translation")
                    exact_translation_checks += 1
                if not rational_outside_divisor(numerators, denominator):
                    continue
                outside_count += 1
                divisor = gcd(*residuals)
                require(divisor != 0, "A rational quadratic translation escaped the divisor")
                residual_gcds[divisor] += 1
                if divisor not in first_examples:
                    first_examples[divisor] = {
                        "source_coefficients": row,
                        "target_coefficients": other,
                        "selected_matrix_rows": indices,
                        "translation_numerators": numerators,
                        "translation_denominator": denominator,
                        "four_linear_residuals": residuals,
                    }
    expected_determinants = {1: 3264, 2: 3008, 3: 576, 4: 1416,
                             6: 216, 8: 252, 12: 24, 16: 32}
    equal(full_rank_pairs, 8788, "Full-rank quadratic pair count")
    equal(outside_count, 480, "Quadratic outside-candidate count")
    equal(selected_determinants, Counter(expected_determinants),
          "Selected quadratic determinant histogram")
    equal(residual_gcds, Counter({3: 288, 7: 192}),
          "Quadratic residual gcd histogram")
    equal(histogram_primes(selected_determinants), [2, 3],
          "Quadratic denominator primes")
    equal(histogram_primes(residual_gcds), [3, 7], "Quadratic residual primes")
    equal(total_pairs, full_rank_pairs + lower_rank_pairs,
          "Quadratic cases were exhaustively partitioned")
    return {
        "degree_at_most_two_polynomial_count": len(quadratics),
        "derivative_rank_census_over_Q": sorted_histogram(ranks),
        "nonzero_quadratic_part_group_count": len(groups),
        "ordered_pairs_with_identical_nonzero_quadratic_part": total_pairs,
        "full_rank_augmented_matrix_pairs": full_rank_pairs,
        "rank_below_three_augmented_matrix_pairs": lower_rank_pairs,
        "rank_below_three_disposition":
            "Any successful modular pair has derivative rank at most two; analytic containment applies",
        "selected_absolute_determinant_histogram": expected_determinants,
        "denominator_prime_divisors": histogram_primes(selected_determinants),
        "outside_divisor_candidates": outside_count,
        "residual_gcd_histogram": sorted_histogram(residual_gcds),
        "residual_prime_divisors": histogram_primes(residual_gcds),
        "exact_rational_translations_checked_by_direct_expansion": exact_translation_checks,
        "first_example_for_each_gcd": first_examples,
        "prime_range_excluded": "Every prime p>=17",
    }


def small_prime_certificate(rows):
    filled = []
    for prime in (3, 5, 7):
        count = sum(signed_divisor(t, prime)
                    for t in product(range(prime), repeat=3))
        equal(count, prime**3, "The divisor fills the small field")
        filled.append({"prime": prime, "divisor_size": count,
                       "available_sign_pairs_after_excluding_zero_and_unit": (prime - 3)//2,
                       "reason": "Fewer than three eligible unordered sign pairs"})
    direct_cases = []
    constants = {(-1, 0, 0, 0, 0, 0, 0, 0),
                 (0, 0, 0, 0, 0, 0, 0, 0),
                 (1, 0, 0, 0, 0, 0, 0, 0)}
    total_pattern_checks = 0
    for prime, expected_representatives in ((11, 4), (13, 10)):
        representatives = list(combinations(range(2, (prime - 1)//2 + 1), 3))
        equal(len(representatives), expected_representatives,
              "Signed-permutation representative count")
        complement = (prime - 3)*(prime - 5)*(prime - 7)
        equal(48 * len(representatives), complement,
              "The signed-permutation orbits exhaust the complement")
        checked_representatives = []
        for translation in representatives:
            require(not signed_divisor(translation, prime),
                    "A direct-test representative lies inside the divisor")
            points = [tuple(translation[i] + ((mask >> i) & 1)
                            for i in range(3)) for mask in range(8)]
            survivors = set()
            for row in rows:
                total_pattern_checks += 1
                if all(evaluate(row, point, prime) in (0, 1, prime - 1)
                       for point in points):
                    survivors.add(row)
            equal(survivors, constants,
                  f"Only constants survive at p={prime}, t={translation}")
            checked_representatives.append({
                "translation": translation,
                "ternary_polynomials_examined": len(rows),
                "surviving_constant_values": [-1, 0, 1],
                "surviving_nonconstant_count": 0,
            })
        direct_cases.append({"prime": prime,
                             "signed_permutation_orbit_size": 48,
                             "outside_divisor_translation_count": complement,
                             "representative_count": len(representatives),
                             "representatives": checked_representatives})
    equal(total_pattern_checks, 14 * 6561, "Every small-prime pattern was examined")
    return {"divisor_fills_field": filled, "direct_checks": direct_cases,
            "total_polynomial_representative_checks": total_pattern_checks,
            "symmetry": "Coordinate permutations and coordinate reflections X_i -> 1-X_i"}


def exact_formula_certificate():
    complement_coefficients = [1]
    for weight in (1, 1, 1, 3, 5, 7):
        result = [0] * (len(complement_coefficients) + 1)
        for i, coefficient in enumerate(complement_coefficients):
            result[i] += coefficient
            result[i + 1] -= weight * coefficient
        complement_coefficients = result
    delta_coefficients = [-x for x in complement_coefficients]
    delta_coefficients[0] += 1
    equal(delta_coefficients, [0, 18, -119, 364, -543, 386, -105],
          "Exact Laurent polynomial for arrangement degeneracy")
    cases = []
    for prime in (3, 5, 7, 11, 13, 17, 19, 23):
        complement = (prime - 3)*(prime - 5)*(prime - 7)
        exact = 1 - Fraction((prime - 1)**3 * complement, prime**6)
        expanded = sum((Fraction(c, prime**i)
                        for i, c in enumerate(delta_coefficients)), Fraction(0))
        equal(exact, expanded, "Factored and expanded arrangement formulae")
        cases.append({"prime": prime,
                      "nondegenerate_translation_count": complement,
                      "degeneracy_proportion": str(exact)})
    return {"factored": "1-(p-1)^3*(p-3)*(p-5)*(p-7)/p^6",
            "laurent_coefficients_starting_at_p_power_zero": delta_coefficients,
            "fraction_checks": cases}


def main():
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("dimension_three_certificate.json"))
    arguments = parser.parse_args()
    started = perf_counter()
    rows = [polynomial_coefficients(values)
            for values in product((-1, 0, 1), repeat=8)]
    equal(len(rows), 6561, "Complete ternary Boolean pattern count")
    equal(len(set(rows)), 6561, "Boolean interpolation is injective")
    equal(max(abs(row[7]) for row in rows), 8, "Cubic coefficient bound")
    equal(max(abs(row[i]) for row in rows for i in (3, 5, 6)), 4,
          "Quadratic coefficient bound")
    cubic = cubic_certificate(rows)
    print("Cubic certificate:", cubic["outside_divisor_candidates"],
          "outside candidates; gcds", cubic["residual_gcd_histogram"], flush=True)
    quadratic = quadratic_certificate(rows)
    print("Quadratic certificate:", quadratic["full_rank_augmented_matrix_pairs"],
          "full-rank pairs; gcds", quadratic["residual_gcd_histogram"], flush=True)
    small = small_prime_certificate(rows)
    formula = exact_formula_certificate()
    report = {
        "schema_version": 1,
        "theorem": {
            "name": "Exact two-cube degeneracy in active dimension three",
            "field_scope": "Every odd prime p",
            "translation_statement":
                "A nonconstant ternary Boolean polynomial has a ternary translate only in the signed-coordinate divisor",
            "nondegenerate_translation_count": "(p-3)*(p-5)*(p-7)",
            "arrangement_degeneracy_proportion": formula["factored"],
            "analytic_input":
                "The article's derivative-rank-at-most-two containment theorem for p>=11",
            "proof_status": "Exhaustive integer certificate plus the stated analytic lemma; not kernel formalized",
        },
        "enumeration": {
            "alphabet": [-1, 0, 1],
            "variable_count": 3,
            "vertex_mask_order": list(range(8)),
            "coefficient_monomial_order": ["1", "X", "Y", "XY", "Z", "XZ", "YZ", "XYZ"],
            "ternary_polynomial_count": len(rows),
            "interpolation_method": "Integer Boolean Mobius inversion",
            "cubic_coefficient_absolute_bound": 8,
            "quadratic_coefficient_absolute_bound": 4,
            "coefficient_rows_sha256": sha256(json.dumps(rows, separators=(",", ":")).encode()).hexdigest(),
        },
        "cubic": cubic,
        "quadratic": quadratic,
        "small_primes": small,
        "exact_formula": formula,
        "verification": {
            "all_checks_passed": True,
            "arithmetic": "Unbounded Python integers and exact rational fractions",
            "dependencies": "Python standard library only",
            "sampled_cases": 0,
            "assert_statements_used_for_mathematical_checks": False,
            "optimized_python_execution_refused": True,
            "program_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        },
    }
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(report, indent=2) + "\n").encode()
    arguments.output.write_bytes(data)
    elapsed = perf_counter() - started
    print("All exact dimension-three checks passed.", flush=True)
    print("Small-prime polynomial/representative checks:",
          small["total_polynomial_representative_checks"], flush=True)
    print("Runtime: {:.3f} seconds".format(elapsed), flush=True)
    print("Dependencies: Python standard library only", flush=True)
    print("Certificate:", arguments.output, flush=True)
    print("Certificate SHA256:", sha256(data).hexdigest(), flush=True)


if __name__ == "__main__":
    main()
