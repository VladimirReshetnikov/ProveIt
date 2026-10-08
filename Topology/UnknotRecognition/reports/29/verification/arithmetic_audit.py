"""Independent finite audit of modular L1 lift and threshold theorems.

This reference deliberately does not import fastunknot. The lift optimum is
checked against dynamic programming over an explicit finite integer box.
Run with Python 3; the JSON count record is printed to standard output.
"""
import json
from itertools import product


def minimum_formula(balanced_vector, modulus, exact_sum):
    assert (exact_sum - sum(balanced_vector)) % modulus == 0
    steps = (exact_sum - sum(balanced_vector)) // modulus
    discounts = sorted(
        (abs(value) for value in balanced_vector if value * steps < 0),
        reverse=True,
    )
    return (sum(map(abs, balanced_vector)) + modulus * abs(steps)
            - 2 * sum(discounts[:abs(steps)]))


def balanced(value, modulus):
    radius = (modulus - 1) // 2
    return (value + radius) % modulus - radius


def main():
    counts = {"lift_formula_cases": 0, "threshold_cases": 0}
    for modulus in (3, 5, 7):
        radius = (modulus - 1) // 2
        for dimension in (1, 2, 3, 4):
            for vector in product(range(-radius, radius + 1), repeat=dimension):
                # Finite independent oracle: every coordinate shift is in
                # [-5,5], retaining all intermediate sums and minimum costs.
                dynamic = {0: 0}
                for value in vector:
                    following = {}
                    for total, cost in dynamic.items():
                        for shift in range(-5, 6):
                            target = total + shift
                            candidate = cost + abs(value + modulus * shift)
                            following[target] = min(
                                following.get(target, 10**9), candidate)
                    dynamic = following
                for shift_sum in range(-4, 5):
                    total = sum(vector) + modulus * shift_sum
                    predicted = minimum_formula(vector, modulus, total)
                    assert predicted == dynamic[shift_sum], (
                        modulus, vector, shift_sum, predicted, dynamic[shift_sum])
                    counts["lift_formula_cases"] += 1

    for coordinate_bound in range(5):
        for dimension in (1, 2, 3, 4):
            values = range(-coordinate_bound, coordinate_bound + 1)
            for vector in product(values, repeat=dimension):
                exact = sum(map(abs, vector))
                exact_sum = sum(vector)
                for modulus in (3, 5, 7, 9, 11):
                    residues = [balanced(value, modulus) for value in vector]
                    ordinary = sum(map(abs, residues))
                    improved = minimum_formula(residues, modulus, exact_sum)
                    assert ordinary <= improved <= exact
                    for weight in (1, 2, 3):
                        for threshold in range(9):
                            if modulus > coordinate_bound + threshold // weight:
                                assert (weight * ordinary > threshold) == (
                                    weight * exact > threshold)
                            if modulus > coordinate_bound + threshold // (2 * weight):
                                assert (weight * improved > threshold) == (
                                    weight * exact > threshold)
                            if weight * abs(exact_sum) <= 1 and weight * ordinary <= 1:
                                assert ordinary == improved
                            counts["threshold_cases"] += 1
    print(json.dumps(counts, sort_keys=True))


if __name__ == "__main__":
    main()
