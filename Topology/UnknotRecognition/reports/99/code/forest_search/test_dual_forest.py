import copy
import unittest

from dual_forest_search import (
    InvalidProblem, from_dense, solve_by_stopping, solve_degree_two,
)
from dual_forest_verify import verify


class ForestTests(unittest.TestCase):
    def assert_both(self, problem, status):
        for solver in (solve_degree_two, solve_by_stopping):
            result = solver(problem)
            self.assertEqual(result["status"], status)
            self.assertTrue(verify(problem, result))

    def test_forest_choice_changes_answer(self):
        problem = from_dense(2, [[0, 1], [0, 1]], [[1], [3]])
        for solver in (solve_degree_two, solve_by_stopping):
            result = solver(problem)
            self.assertEqual(result["certificate"]["tree"], [1])
            self.assertTrue(verify(problem, result))
            wrong = copy.deepcopy(result)
            wrong["certificate"] = {"kind": "success", "tree": [0], "peeling": [[1, 0]]}
            self.assertFalse(verify(problem, wrong))

    def test_matroid_exchange_is_used(self):
        problem = from_dense(3, [[0, 1], [1, 2], [0, 1]], [[1], [1], [0]])
        result = solve_degree_two(problem)
        self.assertEqual(result["status"], "SUCCESS")
        self.assertEqual(result["certificate"]["tree"], [1, 2])
        self.assertGreater(result["stats"]["matroid_path_vertices"],
                           result["stats"]["matroid_augmentations"])
        self.assertTrue(verify(problem, result))

    def test_proper_subfamily_rank_defect(self):
        problem = from_dense(4, [[0, 1], [0, 1], [1, 2], [2, 3]], [[0], [0], [1], [1]])
        result = solve_degree_two(problem)
        self.assertEqual(result["status"], "NO_FOREST")
        self.assertEqual(result["certificate"]["rank"], 1)
        self.assertEqual(result["certificate"]["stopping_sets"], [[0], [1]])
        self.assertTrue(verify(problem, result))

    def test_parallel_forced_rows_contradict(self):
        problem = from_dense(2, [[0, 1], [0, 1]], [[2], [2]])
        self.assert_both(problem, "NO_FOREST")
        result = solve_by_stopping(problem)
        self.assertEqual(result["stats"]["forced_choices"], 1)
        self.assertEqual(result["stats"]["blocked_leaves"], 1)

    def test_directed_chain_reachability(self):
        problem = from_dense(2, [[0, 1], None, None], [[2, 0], [1, 2], [0, 1]])
        self.assert_both(problem, "SUCCESS")

    def test_seed_propagates_without_deletion(self):
        problem = from_dense(1, [None, None, None], [[1, 1, 0], [0, 1, 1], [0, 0, 1]])
        self.assert_both(problem, "SUCCESS")

    def test_inert_large_support_is_allowed(self):
        problem = from_dense(3, [[0, 1], [1, 2], None], [[2, 0], [2, 0], [2, 1]])
        self.assert_both(problem, "SUCCESS")

    def test_active_large_support_is_not_degree_two(self):
        problem = from_dense(2, [[0, 1], None, None], [[1], [1], [1]])
        result = solve_degree_two(problem)
        self.assertEqual(result["status"], "INCONCLUSIVE")
        result = solve_by_stopping(problem)
        self.assertEqual(result["status"], "NO_FOREST")
        self.assertTrue(verify(problem, result))

    def test_empty_problem(self):
        self.assert_both(from_dense(1, [], []), "SUCCESS")

    def test_loop_is_never_a_tree_edge(self):
        self.assert_both(from_dense(1, [[0, 0]], [[0]]), "NO_FOREST")

    def test_disconnected_graph(self):
        self.assert_both(from_dense(3, [[0, 1]], [[1]]), "NO_FOREST")

    def test_huge_omitted_namespace_does_not_expand(self):
        problem = from_dense(2**4096, [[0, 1]], [[1]])
        self.assert_both(problem, "NO_FOREST")

    def test_huge_sparse_column_namespace_does_not_expand(self):
        problem = {"vertices": 1, "columns": 2**4096,
                   "edges": [None], "rows": [[[2**4095, 1]]]}
        self.assert_both(problem, "SUCCESS")

    def test_budgets_do_not_prove_negatives(self):
        problem = from_dense(2, [[0, 1], [0, 1]], [[1], [3]])
        for result in (solve_degree_two(problem, max_work=0),
                       solve_by_stopping(problem, max_work=0),
                       solve_by_stopping(problem, max_nodes=0)):
            self.assertEqual(result["status"], "INCONCLUSIVE")
            self.assertNotIn("certificate", result)
            self.assertFalse(verify(problem, result))

    def test_malformed_inputs(self):
        source = from_dense(2, [[0, 1]], [[1]])
        malformed = []
        for key, value in (("vertices", True), ("vertices", 0), ("columns", -1),
                           ("edges", [[0, 2]]), ("edges", []),
                           ("rows", [[[0, 1], [0, 2]]]), ("rows", [[[0, False]]]),
                           ("rows", [[[1, 1]]]), ("rows", [[[0, 0]]])):
            bad = copy.deepcopy(source)
            bad[key] = value
            malformed.append(bad)
        malformed.append(dict(source, extra=1))
        for bad in malformed:
            for solver in (solve_degree_two, solve_by_stopping):
                with self.assertRaises(InvalidProblem):
                    solver(bad)
            self.assertFalse(verify(bad, {"status": "SUCCESS", "certificate": {}}))

    def test_rank_proof_mutations(self):
        problem = from_dense(2, [[0, 1], [0, 1]], [[2], [2]])
        result = solve_degree_two(problem)
        for change in ("rank", "missing_set", "overlap", "false_status"):
            bad = copy.deepcopy(result)
            if change == "rank":
                bad["certificate"]["rank"] = 0
            elif change == "missing_set":
                bad["certificate"]["stopping_sets"].pop()
            elif change == "overlap":
                bad["certificate"]["stopping_sets"][1] = [0]
            else:
                bad["status"] = "SUCCESS"
            self.assertFalse(verify(problem, bad))

    def test_branch_coverage_mutations(self):
        problem = from_dense(2, [[0, 1], [0, 1], None], [[1], [1], [1]])
        result = solve_by_stopping(problem, minimize_witness=False)
        self.assertEqual(result["status"], "NO_FOREST")
        self.assertEqual(len(result["certificate"]["children"]), 2)
        self.assertTrue(verify(problem, result))
        bad = copy.deepcopy(result)
        bad["certificate"]["children"].pop()
        self.assertFalse(verify(problem, bad))
        bad = copy.deepcopy(result)
        bad["certificate"]["witness"] = [0]
        self.assertFalse(verify(problem, bad))

    def test_peeling_timestamp_mutations(self):
        problem = from_dense(1, [None, None], [[1, 0], [1, 1]])
        result = solve_degree_two(problem)
        for moves in ([[0, 0], [1, 1]], [[1, 1]], [[1, 1], [0, 1]]):
            bad = copy.deepcopy(result)
            bad["certificate"]["peeling"] = moves
            self.assertFalse(verify(problem, bad))


if __name__ == "__main__":
    unittest.main()
