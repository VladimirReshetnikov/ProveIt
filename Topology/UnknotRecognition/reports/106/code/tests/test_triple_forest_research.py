"""Independent finite checks for the exceptional-row research solvers."""

import copy
import itertools
import random
import unittest

from triple_forest_research import base, base_verify, nonlinear, solver


def brute_trees(problem):
    """Tiny independent graph/peeling oracle, with explicit block merging."""
    rank = problem["vertices"] - 1
    answers = []
    for chosen in itertools.combinations(range(len(problem["rows"])), rank):
        blocks = [{vertex} for vertex in range(problem["vertices"])]
        for row in chosen:
            edge = problem["edges"][row]
            if edge is None:
                break
            left = next(i for i, block in enumerate(blocks) if edge[0] in block)
            right = next(i for i, block in enumerate(blocks) if edge[1] in block)
            if left == right:
                break
            blocks[left].update(blocks[right])
            del blocks[right]
        else:
            if len(blocks) != 1:
                continue
            live = set(range(len(problem["rows"]))) - set(chosen)
            while live:
                owner, totals = {}, {}
                for row in live:
                    for column, value in problem["rows"][row]:
                        totals[column] = totals.get(column, 0) + value
                        owner[column] = row
                private = next((column for column, value in totals.items() if value == 1), None)
                if private is None:
                    break
                live.remove(owner[private])
            if not live:
                answers.append(chosen)
    return answers


def one_triple():
    # First spanning tree stalls; deleting row 1 seeds row 0 and then row 2.
    return base.from_dense(2, [[0, 1], [0, 1], [0, 0]],
                           [[1, 1], [1, 2], [1, 0]])


class Values:
    def __init__(self, values):
        self.values = iter(values)

    def randrange(self, prime):
        value = next(self.values)
        assert 0 <= value < prime
        return value


class ExceptionalRowsTests(unittest.TestCase):
    def test_new_three_row_success(self):
        problem = one_triple()
        self.assertEqual(base.solve_degree_two(problem)["status"], "INCONCLUSIVE")
        for result in (solver.solve(problem), solver.solve_randomized(problem, seed=10),
                       nonlinear.solve_boolean(problem, seed=10),
                       nonlinear.solve_width(problem)):
            self.assertEqual(result["status"], "SUCCESS")
            self.assertEqual(result["certificate"]["tree"], [1])
            self.assertTrue(base_verify.verify(problem, result))

    def test_future_head_does_not_seed_its_own_prerequisites(self):
        problem = base.from_dense(1, [[0, 0]] * 3,
                                  [[1, 2, 2], [1, 1, 0], [1, 0, 1]])
        self.assertFalse(brute_trees(problem))
        self.assertEqual(solver.solve(problem)["status"], "NO_FOREST")
        result = nonlinear.solve_boolean(problem, seed=20)
        self.assertEqual(result["status"], "INCONCLUSIVE")

    def test_exhaustive_binary_three_by_two(self):
        choices = [None, [0, 0], [0, 1], [1, 1]]
        checked = 0
        for edges in itertools.product(choices, repeat=3):
            for bits in itertools.product((0, 1), repeat=6):
                matrix = [list(bits[2 * row:2 * row + 2]) for row in range(3)]
                problem = base.from_dense(2, list(edges), matrix)
                expected = bool(brute_trees(problem))
                exact = solver.solve(problem)
                self.assertEqual(exact["status"] == "SUCCESS", expected)
                random_result = nonlinear.solve_boolean(problem, seed=checked)
                self.assertEqual(random_result["status"] == "SUCCESS", expected)
                width_result = nonlinear.solve_width(problem)
                self.assertEqual(width_result["status"] == "SUCCESS", expected)
                if expected:
                    self.assertTrue(base_verify.verify(problem, exact))
                    self.assertTrue(base_verify.verify(problem, random_result))
                    self.assertTrue(base_verify.verify(problem, width_result))
                checked += 1
        self.assertEqual(checked, 4096)

    def test_generated_weighted_wider_columns(self):
        rng = random.Random(4218003)
        for case in range(320):
            vertices, rows = rng.randint(1, 4), rng.randint(3, 7)
            edges = [None if rng.randrange(7) == 0 else
                     [rng.randrange(vertices), rng.randrange(vertices)] for _ in range(rows)]
            matrix = [[rng.choice((0, 0, 1, 1, 2)) for _ in range(3)] for _ in range(rows)]
            problem = base.from_dense(vertices, edges, matrix)
            expected = bool(brute_trees(problem))
            result = nonlinear.solve_boolean(problem, seed=case, trials=2)
            self.assertEqual(result["status"] == "SUCCESS", expected)
            exact = nonlinear.solve_width(problem)
            self.assertEqual(exact["status"] == "SUCCESS", expected)
            if expected:
                self.assertTrue(base_verify.verify(problem, result))
                self.assertTrue(base_verify.verify(problem, exact))

    def test_boolean_mobius_identity_for_every_three_bit_function(self):
        for truth_bits in range(256):
            values = [(truth_bits >> mask) & 1 for mask in range(8)]
            coefficients = nonlinear._mobius_filter(values, base.Work())
            for hit in range(8):
                actual = sum(coefficients[mask] for mask in range(8) if mask & hit == 0)
                self.assertEqual(actual, values[hit])

    def test_ideal_filter_chain_and_all_small_posets(self):
        rng = random.Random(76879)
        for dimension in range(1, 7):
            # A directed acyclic graph in label order; include a chain and
            # an antichain explicitly.  Check by enumerating all subsets.
            for sample in range(30):
                ancestors = [1 << i for i in range(dimension)]
                for i in range(dimension):
                    for j in range(i):
                        if sample == 0 or (sample > 1 and rng.randrange(3) == 0):
                            ancestors[i] |= ancestors[j]
                prepared = {"ancestors": ancestors}
                ideals = nonlinear._ideal_masks(prepared, list(range(dimension)), base.Work())
                expected = [mask for mask in range(1 << dimension)
                            if all(ancestors[i] & mask == ancestors[i]
                                   for i in range(dimension) if mask & (1 << i))]
                self.assertEqual(ideals, expected)
                if sample == 0:
                    self.assertEqual(len(ideals), dimension + 1)
                if sample == 1:
                    self.assertEqual(len(ideals), 1 << dimension)
                values = [rng.randrange(-7, 8) for _ in ideals]
                coefficients = nonlinear._ideal_mobius(ideals, values, dimension, base.Work())
                for index, mask in enumerate(ideals):
                    self.assertEqual(sum(value for subset, value in coefficients
                                         if subset & mask == subset), values[index])

    def test_scc_order_is_not_row_order(self):
        # Ordinary implications go backwards in row-label order.
        problem = base.from_dense(2, [[0, 1], [0, 0], [0, 0]],
                                  [[1, 1, 0], [1, 2, 1], [1, 0, 2]])
        prepared, special, _ = nonlinear._special_state(base.normalize(problem), base.Work())
        self.assertEqual(special, [2, 1, 0])
        self.assertEqual(nonlinear._ideal_masks(prepared, special, base.Work()), [0, 1, 3, 7])
        self.assertEqual(nonlinear.solve_width(problem)["status"] == "SUCCESS",
                         bool(brute_trees(problem)))

    def test_repeated_pass_extraction(self):
        problem = base.from_dense(2, [[0, 1]] * 3, [[], [], []], columns=0)
        work = base.Work()
        sieve = solver.CoverageSieve(base.normalize(problem), (), (), 7,
                                    Values([1, 1, 6]), work)
        self.assertEqual(sieve.tree(), [1])
        self.assertEqual(work.counts["self_reduction_tests"], 4)

    def test_distinct_copy_variables_prevent_symbolic_cancellation(self):
        problem = base.from_dense(3, [[0, 1], [0, 2]], [[], []], columns=0)
        data = base.normalize(problem)
        # Identifying the two variables for each edge cancels the polynomial.
        bad = solver.CoverageSieve(data, (3,), (), 7, Values([1, 1, 1, 1]), base.Work())
        self.assertIsNone(bad.tree())
        good = solver.CoverageSieve(data, (3,), (), 7, Values([1, 2, 3, 4]), base.Work())
        self.assertEqual(good.tree(), [0, 1])

    def test_too_many_mandatory_groups(self):
        data = base.normalize(base.from_dense(2, [[0, 1], [0, 1]], [[], []], columns=0))
        sieve = solver.CoverageSieve(data, (1, 2), (), 7, Values([]), base.Work())
        self.assertIsNone(sieve.tree())

    def test_budgets_are_inconclusive(self):
        problem = one_triple()
        self.assertEqual(solver.solve(problem, max_work=0)["status"], "INCONCLUSIVE")
        self.assertEqual(solver.solve(problem, max_histories=0)["status"], "INCONCLUSIVE")
        self.assertEqual(nonlinear.solve_boolean(problem, max_table_bits=0)["status"],
                         "INCONCLUSIVE")
        self.assertEqual(nonlinear.solve_boolean(problem, max_states=0)["status"],
                         "INCONCLUSIVE")
        self.assertEqual(nonlinear.solve_width(problem, max_states=0)["status"],
                         "INCONCLUSIVE")

    def test_independent_replay_rejects_mutated_source_and_proof(self):
        problem = one_triple()
        result = nonlinear.solve_boolean(problem, seed=7)
        changed = copy.deepcopy(problem)
        changed["rows"][2][0][1] = 2
        self.assertFalse(base_verify.verify(changed, result))
        changed = copy.deepcopy(result)
        changed["certificate"]["tree"] = [0]
        self.assertFalse(base_verify.verify(problem, changed))
        changed = copy.deepcopy(result)
        changed["certificate"]["peeling"].pop()
        self.assertFalse(base_verify.verify(problem, changed))

    def test_no_randomized_zero_is_a_negative_certificate(self):
        problem = base.from_dense(2, [[0, 1]] * 3, [[1], [1], [1]])
        result = nonlinear.solve_boolean(problem, seed=8)
        self.assertEqual(result["status"], "INCONCLUSIVE")
        self.assertFalse(base_verify.verify(problem, result))

    def test_large_counts_and_unbounded_inert_support(self):
        problem = base.from_dense(2, [[0, 1], [0, 0], [0, 0], [0, 0]],
                                  [[2**1000, 0, 0, 0], [2**1000, 1, 0, 0],
                                   [2**1000, 0, 1, 0], [2**1000, 0, 0, 1]])
        self.assertEqual(nonlinear.solve_boolean(problem)["status"], "SUCCESS")

    def test_input_validation(self):
        for prime in (0, 2**64, 9, True):
            with self.assertRaises(ValueError):
                nonlinear.solve_boolean(one_triple(), prime=prime)
        with self.assertRaises(ValueError):
            nonlinear.solve_boolean(one_triple(), trials=0)
        with self.assertRaises(ValueError):
            nonlinear.solve_boolean(one_triple(), max_table_bits=-1)
        malformed = one_triple()
        malformed["rows"][0].append(malformed["rows"][0][0])
        with self.assertRaises(ValueError):
            nonlinear.solve_boolean(malformed)


if __name__ == "__main__":
    unittest.main()
