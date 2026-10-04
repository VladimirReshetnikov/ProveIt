#!/usr/bin/env python3
"""Finite exact diagnostics accompanying the Polish Presburger article.

Python 3.9+; standard library only. No files from previous research archives
are executed. These checks exercise finite rational instances and are not a
formal verification of the article's infinitary theorems.
"""

from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import json


def require(condition, message):
    """An assertion that remains active when Python is run with -O."""
    if not condition:
        raise AssertionError(message)


def sign(value):
    return (value > 0) - (value < 0)


def dot(left, right):
    return sum((a * b for a, b in zip(left, right)), Fraction(0))


def rational_rank(matrix):
    """Exact Gaussian elimination; entries may be integers or Fractions."""
    rows = [[Fraction(value) for value in row] for row in matrix]
    if not rows:
        return 0
    width = len(rows[0])
    require(all(len(row) == width for row in rows), "Ragged rank matrix")
    pivot_row = 0
    for column in range(width):
        pivot = next(
            (r for r in range(pivot_row, len(rows)) if rows[r][column]), None
        )
        if pivot is None:
            continue
        rows[pivot_row], rows[pivot] = rows[pivot], rows[pivot_row]
        divisor = rows[pivot_row][column]
        rows[pivot_row] = [value / divisor for value in rows[pivot_row]]
        for r in range(pivot_row + 1, len(rows)):
            multiple = rows[r][column]
            if multiple:
                rows[r] = [
                    value - multiple * pivot_value
                    for value, pivot_value in zip(rows[r], rows[pivot_row])
                ]
        pivot_row += 1
        if pivot_row == len(rows):
            break
    return pivot_row


def simplify_inequalities(rows):
    """Rows encode coefficient_vector dot x >= bound.

    Equal left sides are merged by retaining the strongest bound. A false
    constant inequality returns None; true constant inequalities are dropped.
    """
    strongest = {}
    for coefficients, bound in rows:
        coefficients = tuple(Fraction(c) for c in coefficients)
        bound = Fraction(bound)
        if not any(coefficients):
            if bound > 0:
                return None
            continue
        # Normalize by a positive factor only, preserving inequality direction.
        scale = abs(next(c for c in coefficients if c))
        coefficients = tuple(c / scale for c in coefficients)
        bound /= scale
        if coefficients not in strongest or bound > strongest[coefficients]:
            strongest[coefficients] = bound
    return list(strongest.items())


def fourier_motzkin_feasible(variable_count, inequalities):
    """Exact feasibility of finite nonstrict rational linear inequalities."""
    rows = simplify_inequalities(inequalities)
    if rows is None:
        return False
    require(
        all(len(coefficients) == variable_count for coefficients, _ in rows),
        "Incorrect inequality dimension",
    )
    for _ in range(variable_count):
        positive, negative, zero = [], [], []
        for coefficients, bound in rows:
            leading = coefficients[0]
            if leading > 0:
                positive.append((tuple(c / leading for c in coefficients[1:]),
                                 bound / leading))
            elif leading < 0:
                negative.append((tuple(c / -leading for c in coefficients[1:]),
                                 bound / -leading))
            else:
                zero.append((coefficients[1:], bound))
        projected = list(zero)
        for p_coefficients, p_bound in positive:
            for n_coefficients, n_bound in negative:
                projected.append((
                    tuple(a + b for a, b in zip(p_coefficients, n_coefficients)),
                    p_bound + n_bound,
                ))
        # If only lower or only upper bounds occur, that variable is free to
        # satisfy them, so all its nonzero-coefficient rows may be discarded.
        rows = simplify_inequalities(projected)
        if rows is None:
            return False
    return all(bound <= 0 for _, bound in rows)


def homogeneous_feasible(variable_count, constraints):
    """Feasibility for homogeneous ==, >=, >, <=, and < constraints.

    A finite homogeneous system with strict inequalities is feasible iff it
    remains feasible after each required strict positive quantity is >= 1:
    scale a witness by a common positive rational factor. This transformation
    would be invalid for arbitrary inhomogeneous strict systems.
    """
    inequalities = []
    for coefficients, relation in constraints:
        coefficients = tuple(Fraction(c) for c in coefficients)
        require(len(coefficients) == variable_count, "Constraint dimension")
        if relation == "==":
            inequalities.extend([
                (coefficients, 0), (tuple(-c for c in coefficients), 0)
            ])
        elif relation == ">=":
            inequalities.append((coefficients, 0))
        elif relation == ">":
            inequalities.append((coefficients, 1))
        elif relation == "<=":
            inequalities.append((tuple(-c for c in coefficients), 0))
        elif relation == "<":
            inequalities.append((tuple(-c for c in coefficients), 1))
        else:
            raise ValueError("Unknown homogeneous relation: " + relation)
    return fourier_motzkin_feasible(variable_count, inequalities)


def check_local_sign_feasibility():
    domain_face = [((1, 0), ">="), ((0, 1), ">=")]
    named_cases = [
        ("monus_positive_branch_at_zero_face", domain_face + [((1, -1), ">")], True),
        ("monus_negative_branch_at_zero_face", domain_face + [((1, -1), "<")], True),
        ("monus_equal_direction_at_zero_face", domain_face + [((1, -1), "==")], True),
        ("opposite_signs_of_dependent_forms", [((1, -1), ">"), ((2, -2), "<")], False),
        ("positive_summands_negative_sum", [((1, 0), ">"), ((0, 1), ">"), ((1, 1), "<")], False),
        ("equality_conflicts_with_positive_face", [((1, 1), "=="), ((1, 0), ">"), ((0, 1), ">=")], False),
        ("nonzero_rational_equality_ray", [((1, -2), "=="), ((1, 0), ">"), ((0, 1), ">")], True),
        ("identically_zero_cannot_be_positive", [((0, 0), ">")], False),
        ("identically_zero_is_nonnegative", [((0, 0), ">=")], True),
    ]
    for name, constraints, expected in named_cases:
        require(homogeneous_feasible(2, constraints) == expected, name)

    # Independently enumerate exact witnesses for the four-line arrangement.
    # Its eight rays, eight open sectors, and the origin are all represented
    # among these small integer vectors, providing all 17 feasible profiles.
    forms = [(1, 0), (0, 1), (1, -1), (1, 1)]
    witnessed = {
        tuple(sign(dot(form, vector)) for form in forms)
        for vector in product(range(-2, 3), repeat=2)
    }
    require(len(witnessed) == 17, "Four-line witness profile count")
    relation_for_sign = {-1: "<", 0: "==", 1: ">"}
    feasible_count = 0
    for profile in product((-1, 0, 1), repeat=len(forms)):
        constraints = [(form, relation_for_sign[s]) for form, s in zip(forms, profile)]
        feasible = homogeneous_feasible(2, constraints)
        require(feasible == (profile in witnessed), "Fourier-Motzkin/profile mismatch")
        feasible_count += feasible
    return {
        "named_cases": len(named_cases),
        "monus_accessible_signs_on_zero_face": ["negative", "zero", "positive"],
        "four_line_profiles_checked": 3 ** len(forms),
        "four_line_feasible_profiles": feasible_count,
        "four_line_infeasible_profiles": 3 ** len(forms) - feasible_count,
        "arithmetic": "exact fractions; homogeneous strict inequalities only",
    }


def is_power_of_two(value):
    return value > 0 and value & (value - 1) == 0


def in_localization_at_two(value):
    """Membership in Z_(2): reduced denominator is odd."""
    return Fraction(value).denominator % 2 == 1


def in_dyadic_localization(value):
    """Membership in Z[1/2]: reduced denominator is a power of two."""
    return is_power_of_two(Fraction(value).denominator)


def rational_mod(value, modulus):
    value = Fraction(value)
    if modulus == 1:
        return 0
    require(gcd(value.denominator, modulus) == 1, "Noninvertible denominator")
    return (value.numerator * pow(value.denominator, -1, modulus)) % modulus


def nonsplit_quotient_remainder(point, divisor):
    """K=Z_(2) x Z[1/2], unit (1,1), ordered by (v-u,u)."""
    require(divisor >= 1, "Positive divisor required")
    u, v = map(Fraction, point)
    power_two, odd = 1, divisor
    while odd % 2 == 0:
        power_two *= 2
        odd //= 2
    a = rational_mod(u, power_two)
    b = rational_mod(v, odd)
    if odd == 1:
        remainder = a
    else:
        multiplier = ((b - a) * pow(power_two, -1, odd)) % odd
        remainder = a + power_two * multiplier
    quotient = ((u - remainder) / divisor, (v - remainder) / divisor)
    return quotient, remainder


def nonsplit_sign(point):
    u, v = point
    return sign(v - u) if v != u else sign(u)


def check_nonsplit_division():
    first_coordinates = sorted({
        Fraction(numerator, denominator)
        for numerator in range(-3, 4)
        for denominator in (1, 3, 5, 7, 9)
    })
    second_coordinates = sorted({
        Fraction(numerator, 2 ** exponent)
        for numerator in range(-3, 4)
        for exponent in range(5)
    })
    division_count = positive_count = uniqueness_candidates = 0
    for point in product(first_coordinates, second_coordinates):
        u, v = point
        for divisor in range(1, 25):
            quotient, remainder = nonsplit_quotient_remainder(point, divisor)
            require(0 <= remainder < divisor, "CRT representative out of range")
            require(in_localization_at_two(quotient[0]), "First quotient membership")
            require(in_dyadic_localization(quotient[1]), "Second quotient membership")
            require(divisor * quotient[0] + remainder == u, "First division identity")
            require(divisor * quotient[1] + remainder == v, "Second division identity")
            division_count += 1
            if nonsplit_sign(point) >= 0:
                require(nonsplit_sign(quotient) >= 0, "Positive cone quotient")
                positive_count += 1

            # A separate exhaustive residue check confirms uniqueness on each
            # finite test instance, rather than only repeating the CRT formula.
            admissible = []
            for candidate in range(divisor):
                uniqueness_candidates += 1
                if (in_localization_at_two((u - candidate) / divisor)
                        and in_dyadic_localization((v - candidate) / divisor)):
                    admissible.append(candidate)
            require(admissible == [remainder], "Residue uniqueness")

    x, y = (Fraction(-1), Fraction(0)), (Fraction(0), Fraction(1))
    require(nonsplit_sign(x) > 0 and nonsplit_sign(y) > 0, "Positive witness pair")
    require((x[0] + 1, x[1] + 1) == y, "Witness successor relation")
    for exponent in range(13):
        qx = (x[0] / 3 ** exponent, x[1] / 3 ** exponent)
        qy = (y[0] / 2 ** exponent, y[1] / 2 ** exponent)
        require(in_localization_at_two(qx[0]) and in_dyadic_localization(qx[1]),
                "Finite 3-power divisibility witness")
        require(in_localization_at_two(qy[0]) and in_dyadic_localization(qy[1]),
                "Finite 2-power divisibility witness")
    return {
        "group": "Z_(2) x Z[1/2], unit (1,1), order by (v-u,u)",
        "distinct_first_coordinates": len(first_coordinates),
        "distinct_second_coordinates": len(second_coordinates),
        "divisors": {"minimum": 1, "maximum": 24},
        "division_instances": division_count,
        "nonnegative_input_instances": positive_count,
        "independent_uniqueness_candidates": uniqueness_candidates,
        "divisibility_witness_exponents": {"minimum": 0, "maximum": 12},
    }


def truncated_form_sign(coefficients, rows, integer_part=0):
    for row in rows:
        value = dot(coefficients, row)
        if value:
            return sign(value)
    return sign(integer_part)


def diagnostic_trace(coefficients, rows, evaluator):
    values = [bool(evaluator(rows[:prefix])) for prefix in range(len(rows) + 1)]
    ranks = [
        rational_rank([tuple(dot(c, row) for c in coefficients) for row in rows[:prefix]])
        for prefix in range(len(rows) + 1)
    ]
    change_stages = []
    for stage in range(1, len(values)):
        if values[stage] != values[stage - 1]:
            require(ranks[stage] > ranks[stage - 1],
                    "Truth changed without a restricted-row rank increase")
            change_stages.append(stage)
    coefficient_rank = rational_rank(coefficients)
    require(len(change_stages) <= coefficient_rank, "Mind-change rank bound")
    return {
        "input_stream_count": len(rows[0]) if rows else 0,
        "distinct_affine_tests": len(coefficients),
        "coefficient_rank": coefficient_rank,
        "initial_value": values[0],
        "final_value": values[-1],
        "truth_change_count": len(change_stages),
        "change_prefix_lengths": change_stages,
        "final_restricted_row_rank": ranks[-1],
    }


def check_stream_truth_rank():
    # F=((x+y=0) XOR (x=y)) AND
    #   AND_{m=1}^{32} (m*x < (m+1)*y OR x=y).
    # At row 2 the sum resolves; at row 7 the difference resolves.
    coefficients = [(1, 1), (1, -1)] + [(m, -m - 1) for m in range(1, 33)]
    rows = [(0, 0) for _ in range(10)]
    rows[2], rows[7] = (1, 1), (1, 0)

    def many_tests(prefix):
        sum_zero = truncated_form_sign((1, 1), prefix) == 0
        same = truncated_form_sign((1, -1), prefix) == 0
        inequalities = all(
            truncated_form_sign((m, -m - 1), prefix) < 0 or same
            for m in range(1, 33)
        )
        return (sum_zero != same) and inequalities

    rank_two = diagnostic_trace(coefficients, rows, many_tests)
    require(rank_two["coefficient_rank"] == 2, "Rank-two example coefficient rank")
    require(rank_two["truth_change_count"] == 2, "Rank-two example sharpness")
    require(rank_two["change_prefix_lengths"] == [3, 8], "Rank-two stage convention")

    xor_examples = []
    for dimension in range(1, 9):
        coefficients = [
            tuple(int(i == j) for j in range(dimension))
            for i in range(dimension)
        ]
        rows = [tuple(0 for _ in range(dimension)) for _ in range(2 * dimension + 2)]
        for i, basis_vector in enumerate(coefficients):
            rows[2 * i + 2] = basis_vector

        def parity(prefix):
            return sum(truncated_form_sign(c, prefix) != 0 for c in coefficients) % 2 == 1

        trace = diagnostic_trace(coefficients, rows, parity)
        require(trace["truth_change_count"] == dimension, "XOR example sharpness")
        require(trace["coefficient_rank"] == dimension, "XOR coefficient rank")
        xor_examples.append(trace)
    return {
        "stage_convention": "prefix length s includes coordinate rows 0 through s-1",
        "secondary_integer_coordinates": "all zero in these diagnostics",
        "many_tests_rank_two": rank_two,
        "sharp_xor_examples": xor_examples,
    }


def longest_boolean_lattice_alternation(dimension, label):
    """Exact weighted longest path through the finite subset lattice.

    Here S records which nonnegative input streams are nonzero. Adding one
    new member resolves one formerly zero sign. Edge weight is a truth-label
    change. Covers suffice: subdividing a comparable jump cannot reduce its
    endpoint label alternation.
    """
    best = [0] * (1 << dimension)
    for mask in range(1, 1 << dimension):
        best[mask] = max(
            best[mask ^ (1 << bit)]
            + int(label(mask) != label(mask ^ (1 << bit)))
            for bit in range(dimension) if mask & (1 << bit)
        )
    return best[-1]


def check_finite_alternation_complexity():
    examples = []
    for dimension in range(1, 9):
        parity = longest_boolean_lattice_alternation(
            dimension, lambda mask: bin(mask).count("1") % 2 == 1
        )
        all_zero = longest_boolean_lattice_alternation(
            dimension, lambda mask: mask == 0
        )
        require(parity == dimension, "Parity alternation height")
        require(all_zero == 1, "All-zero conjunction alternation height")
        examples.append({
            "dimension": dimension,
            "sign_patterns": 1 << dimension,
            "parity_alternation_height": parity,
            "all_zero_conjunction_alternation_height": all_zero,
        })
    return {
        "domain_regime": "nonnegative streams with secondary integer coordinates zero",
        "finite_poset": "subsets of resolved positive coordinate signs, ordered by inclusion",
        "examples": examples,
    }


def main():
    results = {
        "format_version": 1,
        "scope": "finite exact diagnostics; not infinitary or kernel proof verification",
        "local_sign_feasibility": check_local_sign_feasibility(),
        "nonsplit_quotient_remainder": check_nonsplit_division(),
        "rank_controlled_stream_truth": check_stream_truth_rank(),
        "exact_finite_alternation_examples": check_finite_alternation_complexity(),
        "all_passed": True,
    }
    destination = Path(__file__).resolve().with_name("verification_results.json")
    destination.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "all_passed": True,
        "result_file": destination.name,
        "sign_profiles": results["local_sign_feasibility"]["four_line_profiles_checked"],
        "division_instances": results["nonsplit_quotient_remainder"]["division_instances"],
        "rank_two_changes": results["rank_controlled_stream_truth"]["many_tests_rank_two"]["truth_change_count"],
        "xor_dimensions": list(range(1, 9)),
        "finite_alternation_dimensions": list(range(1, 9)),
    }, indent=2))


if __name__ == "__main__":
    main()
