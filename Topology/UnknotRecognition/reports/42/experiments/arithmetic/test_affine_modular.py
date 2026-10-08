"""Independent finite-domain checks for the affine modular kernel.

Run: python -m unittest discover -s agent_family -p 'test_*.py' -v
The small-domain oracle enumerates original variables, never reuses the
congruence solver or the affine gcd theorem to derive expected answers.
"""

from copy import deepcopy
from itertools import product
from math import gcd
import random
import unittest

from affine_modular import (
    minimise_affine_gcd,
    optimise_cyclic_affine_family,
    solve_congruences,
    verify_infeasibility_certificate,
    verify_optimality_certificate,
)


def direct_solutions(matrix, rhs, modulus, variables):
    return {
        point for point in product(range(modulus), repeat=variables)
        if all((sum(a * z for a, z in zip(row, point)) - value) % modulus == 0
               for row, value in zip(matrix, rhs))
    }


def expand_coset(solution):
    modulus = solution.modulus
    return {
        tuple((value + sum(t * column[index]
                           for t, column in zip(parameters, solution.generators))) % modulus
              for index, value in enumerate(solution.particular))
        for parameters in product(range(modulus), repeat=len(solution.generators))
    }


class AffineModularTests(unittest.TestCase):
    def test_scalar_merge_exhaustive(self):
        for modulus in range(1, 49):
            for a, b in product(range(modulus), repeat=2):
                answer = minimise_affine_gcd(modulus, [a], [[b]])
                expected = min(gcd(modulus, a + t * b) for t in range(modulus))
                self.assertEqual(answer.divisor, expected, (modulus, a, b))
                self.assertEqual(answer.vector, ((a + answer.coefficients[0] * b) % modulus,))

    def test_vector_merge_exhaustive(self):
        for modulus in range(1, 9):
            for a0, a1, b0, b1 in product(range(modulus), repeat=4):
                answer = minimise_affine_gcd(modulus, [a0, a1], [[b0, b1]])
                expected = min(gcd(modulus, a0 + t * b0, a1 + t * b1)
                               for t in range(modulus))
                self.assertEqual(answer.divisor, expected)

    def test_two_generators_exhaustive(self):
        for modulus in range(1, 11):
            for a, b, c in product(range(modulus), repeat=3):
                answer = minimise_affine_gcd(modulus, [a], [[b], [c]])
                expected = min(gcd(modulus, a + s * b + t * c)
                               for s, t in product(range(modulus), repeat=2))
                self.assertEqual(answer.divisor, expected)

    def test_scalar_congruences_exhaustive(self):
        for modulus in range(1, 25):
            for a, b in product(range(modulus), repeat=2):
                expected = direct_solutions([[a]], [b], modulus, 1)
                answer = solve_congruences([[a]], [b], modulus)
                if expected:
                    self.assertIsNotNone(answer)
                    self.assertEqual(expand_coset(answer), expected)
                    self.assertEqual(answer.solution_count, len(expected))
                else:
                    self.assertIsNone(answer)

    def test_two_by_two_congruences_exhaustive(self):
        for modulus in range(1, 5):
            for values in product(range(modulus), repeat=6):
                matrix = [values[:2], values[2:4]]
                rhs = values[4:]
                expected = direct_solutions(matrix, rhs, modulus, 2)
                answer = solve_congruences(matrix, rhs, modulus)
                if expected:
                    self.assertIsNotNone(answer)
                    self.assertEqual(expand_coset(answer), expected)
                    self.assertEqual(answer.solution_count, len(expected))
                else:
                    self.assertIsNone(answer)

    def test_affine_family_exhaustive_one_constraint(self):
        # Every one-variable affine family with one seam, m <= 6.
        for modulus in range(1, 7):
            for a, b, c, h in product(range(modulus), repeat=4):
                expected = direct_solutions([[a]], [b], modulus, 1)
                result = optimise_cyclic_affine_family(modulus, [c], [[h]], [[a]], [b])
                self.assertEqual(result["feasible"], bool(expected))
                self.assertEqual(result["solution_count"], len(expected))
                if expected:
                    minimum = min(gcd(modulus, c + h * z[0]) for z in expected)
                    self.assertEqual(result["minimum_components"], minimum)
                    self.assertTrue(verify_optimality_certificate(
                        modulus, [c], [[h]], [[a]], [b], result))
                else:
                    self.assertTrue(verify_infeasibility_certificate(
                        modulus, [[a]], [b], result))

    def test_random_dense_families_against_original_variables(self):
        randomizer = random.Random(20261008)
        for trial in range(2000):
            modulus = randomizer.randrange(1, 10)
            variables = randomizer.randrange(4)
            constraints = randomizer.randrange(4)
            loops = randomizer.randrange(4)
            matrix = [[randomizer.randrange(-2 * modulus, 2 * modulus + 1)
                       for _ in range(variables)] for _ in range(constraints)]
            rhs = [randomizer.randrange(-modulus, modulus + 1) for _ in range(constraints)]
            holonomy = [[randomizer.randrange(-2 * modulus, 2 * modulus + 1)
                         for _ in range(variables)] for _ in range(loops)]
            constants = [randomizer.randrange(-modulus, modulus + 1) for _ in range(loops)]
            expected = direct_solutions(matrix, rhs, modulus, variables)
            result = optimise_cyclic_affine_family(
                modulus, constants, holonomy, matrix, rhs, variable_count=variables)
            self.assertEqual(result["feasible"], bool(expected), trial)
            self.assertEqual(result["solution_count"], len(expected), trial)
            if expected:
                solution = solve_congruences(matrix, rhs, modulus, variable_count=variables)
                self.assertEqual(expand_coset(solution), expected, trial)
                minimum = min(
                    gcd(modulus, *(constant + sum(a * z for a, z in zip(row, point))
                                   for constant, row in zip(constants, holonomy)))
                    for point in expected)
                self.assertEqual(result["minimum_components"], minimum, trial)
                self.assertIn(tuple(result["parameters"]), expected, trial)
                self.assertTrue(verify_optimality_certificate(
                    modulus, constants, holonomy, matrix, rhs, result,
                    variable_count=variables), trial)
            else:
                self.assertTrue(verify_infeasibility_certificate(
                    modulus, matrix, rhs, result, variable_count=variables), trial)

    def test_zero_one_and_empty_dimensions(self):
        for modulus in (1, 2, 6, 30):
            zero = optimise_cyclic_affine_family(modulus, [], [], variable_count=0)
            self.assertEqual(zero["minimum_components"], modulus)
            self.assertEqual(zero["solution_count"], 1)
            free = optimise_cyclic_affine_family(modulus, [], [], variable_count=3)
            self.assertEqual(free["minimum_components"], modulus)
            self.assertEqual(free["solution_count"], modulus ** 3)
        self.assertIsNone(solve_congruences([[]], [1], 6, variable_count=0))
        self.assertEqual(solve_congruences([[]], [0], 6, variable_count=0).solution_count, 1)

    def test_nontrivial_dual_and_tamper_rejection(self):
        modulus, constants, holonomy = 60, [0, 6], [[1, 2], [6, 12]]
        seams, rhs = [[1, 2]], [12]
        result = optimise_cyclic_affine_family(modulus, constants, holonomy, seams, rhs)
        self.assertEqual(result["minimum_components"], 6)
        self.assertTrue(any(any(row) for row in result["dual_rows"]))
        self.assertTrue(verify_optimality_certificate(
            modulus, constants, holonomy, seams, rhs, result))
        for field in ("parameters", "holonomies", "dual_rows", "minimum_components"):
            broken = deepcopy(result)
            if field == "dual_rows":
                broken[field][0][0] += 1
            elif field == "minimum_components":
                broken[field] = 2
            else:
                broken[field][0] += 1
            self.assertFalse(verify_optimality_certificate(
                modulus, constants, holonomy, seams, rhs, broken), field)

    def test_gcd_saturation_is_needed(self):
        # Trying only t=0 or t=1 fails; the deterministic coefficient is 3.
        answer = minimise_affine_gcd(6, [2], [[1]])
        self.assertEqual(answer.divisor, 1)
        self.assertEqual(answer.coefficients, (3,))
        self.assertEqual(answer.vector, (5,))
        # Taking t=m/gcd(m,a) without saturation also fails here.
        answer = minimise_affine_gcd(12, [2], [[1]])
        self.assertEqual(answer.coefficients, (3,))
        self.assertEqual(answer.vector, (5,))

    def test_infeasibility_certificate_tampering(self):
        result = optimise_cyclic_affine_family(12, [0], [[1]], [[6]], [3])
        self.assertFalse(result["feasible"])
        self.assertTrue(verify_infeasibility_certificate(12, [[6]], [3], result))
        broken = deepcopy(result)
        broken["obstruction"]["multipliers"][0] = 0
        self.assertFalse(verify_infeasibility_certificate(12, [[6]], [3], broken))

    def test_callbacks_are_not_swallowed(self):
        class StopWork(RuntimeError):
            pass
        def stop():
            raise StopWork("cancelled")
        with self.assertRaises(StopWork):
            optimise_cyclic_affine_family(6, [2], [[1]], check=stop)
        with self.assertRaises(StopWork):
            solve_congruences([[2]], [2], 6, check=stop)

    def test_validation(self):
        for modulus in (0, -1, True, 2.0):
            with self.assertRaises(ValueError):
                solve_congruences([], [], modulus)
        with self.assertRaises(ValueError):
            solve_congruences([[1, 2], [3]], [0, 0], 6)
        with self.assertRaises(ValueError):
            optimise_cyclic_affine_family(6, [0], [[1]], [[1]], [])
        with self.assertRaises(ValueError):
            minimise_affine_gcd(6, [0, 1], [[1]])


if __name__ == "__main__":
    unittest.main(verbosity=2)
