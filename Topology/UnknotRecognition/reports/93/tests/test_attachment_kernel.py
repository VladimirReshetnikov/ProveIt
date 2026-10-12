import copy
import itertools
import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
from attachment_kernel import kernelize_attachment_network, source_route
from attachment_kernel_verify import verify_attachment_kernel


def network(n, pairs, nonballs=()):
    v = [{"id": i, "euler_characteristic": 0 if i in nonballs else 1}
         for i in range(n)]
    e = [{"id": i, "ends": list(p)} for i, p in enumerate(pairs)]
    return v, e


def connected(n, pairs):
    adj = [set() for _ in range(n)]
    for u, v in pairs:
        adj[u].add(v)
        adj[v].add(u)
    seen, stack = set(), [0]
    while stack:
        u = stack.pop()
        if u not in seen:
            seen.add(u)
            stack.extend(adj[u] - seen)
    return len(seen) == n


class AttachmentKernelTests(unittest.TestCase):
    def assert_kernel(self, v, e):
        cert = kernelize_attachment_network(v, e)
        self.assertTrue(verify_attachment_kernel(v, e, cert))
        k = cert["kernel"]
        beta = len(e) - len(v) + 1
        self.assertEqual(beta, k["cycle_rank"])
        self.assertEqual(len(k["edges"]) - len(k["vertices"]) + 1, beta)
        for vertex in v:
            route = source_route(cert, vertex["id"])
            self.assertLess(len(route), len(v))
        return cert

    def test_torus_tree_core(self):
        v, e = network(6, [(0, 1), (1, 2), (2, 3), (1, 4), (4, 5)], [3])
        cert = self.assert_kernel(v, e)
        self.assertEqual(cert["kernel"]["vertices"], [[3, 0]])
        self.assertEqual(cert["kernel"]["edges"], [])

    def test_all_ball_cycle_and_parallel_edges(self):
        v, e = network(4, [(0, 1), (1, 2), (2, 3), (3, 0), (0, 1)])
        cert = self.assert_kernel(v, e)
        self.assertEqual(cert["kernel"]["cycle_rank"], 2)
        self.assertEqual(cert["kernel"]["vertices"], [[0, 1]])
        self.assertTrue(all(row[1:] == [0, 0] for row in cert["kernel"]["edges"]))

    def test_source_loops_and_nontrivial_deficits(self):
        v, e = network(3, [(0, 0), (0, 1), (1, 2), (2, 2)], [1, 2])
        v[1]["euler_characteristic"] = -3
        cert = self.assert_kernel(v, e)
        self.assertEqual(cert["kernel"]["euler_deficit"], 7)

    def test_singletons(self):
        for c in [1, 0, -10]:
            self.assert_kernel([{"id": 5, "euler_characteristic": c}], [])

    def test_exhaustive_small_connected_graphs(self):
        cases = 0
        for n in range(1, 6):
            pairs = list(itertools.combinations(range(n), 2))
            for mask in range(1 << len(pairs)):
                chosen = [p for i, p in enumerate(pairs) if mask >> i & 1]
                if not connected(n, chosen):
                    continue
                for marked in [[], [0], list(range(n))]:
                    self.assert_kernel(*network(n, chosen, marked))
                    cases += 1
        self.assertEqual(cases, 2316)

    def test_random_multigraphs(self):
        rng = random.Random(20261012)
        for _ in range(500):
            n = rng.randrange(1, 60)
            pairs = [(v, rng.randrange(v)) for v in range(1, n)]
            pairs += [(rng.randrange(n), rng.randrange(n)) for _ in range(rng.randrange(n + 1))]
            marked = [v for v in range(n) if rng.randrange(4) == 0]
            v, e = network(n, pairs, marked)
            for row in v:
                if row["id"] in marked:
                    row["euler_characteristic"] = -rng.randrange(5)
            self.assert_kernel(v, e)

    def test_corruption_rejected(self):
        v, e = network(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], [1, 3])
        cert = self.assert_kernel(v, e)
        mutations = []
        x = copy.deepcopy(cert); x["input_sha256"] = "0" * 64; mutations.append(x)
        x = copy.deepcopy(cert); x["forest_edges"].pop(); mutations.append(x)
        x = copy.deepcopy(cert); x["vertex_roots"][0][1] = 99; mutations.append(x)
        x = copy.deepcopy(cert); x["parent_forest"][0][1] = 99; mutations.append(x)
        x = copy.deepcopy(cert); x["kernel"]["edges"][0][1] = 99; mutations.append(x)
        x = copy.deepcopy(cert); x["kernel"]["euler_deficit"] += 1; mutations.append(x)
        x = copy.deepcopy(cert); x["kernel"]["cycle_rank"] = float(x["kernel"]["cycle_rank"]); mutations.append(x)
        x = copy.deepcopy(cert); x["vertex_roots"][0][0] = False; mutations.append(x)
        x = copy.deepcopy(cert); x["forest_edges"].append(x["forest_edges"][0]); mutations.append(x)
        for bad in mutations:
            self.assertFalse(verify_attachment_kernel(v, e, bad))

    def test_disconnected_and_bad_labels_rejected(self):
        for marked in [[], [0], [0, 1]]:
            v, e = network(2, [], marked)
            with self.assertRaises(ValueError):
                kernelize_attachment_network(v, e)
        with self.assertRaises(ValueError):
            kernelize_attachment_network([{"id": 0, "euler_characteristic": 2}], [])

    def test_genus_bounds_are_sharp(self):
        for g in range(1, 20):
            # Boundary connected sum of g solid tori: g distinguished roots,
            # g-1 surviving handles.  No root can be absorbed as a ball.
            v, e = network(2 * g - 1, [(i, i + 1) for i in range(2 * g - 2)],
                           list(range(0, 2 * g - 1, 2)))
            cert = self.assert_kernel(v, e)
            self.assertEqual(len(cert["kernel"]["vertices"]), g)
            self.assertEqual(len(cert["kernel"]["edges"]), g - 1)

    def test_cancellation_propagates(self):
        v, e = network(5, [(i, i + 1) for i in range(4)])
        def stop():
            raise RuntimeError("cancelled")
        with self.assertRaisesRegex(RuntimeError, "cancelled"):
            kernelize_attachment_network(v, e, check=stop)


if __name__ == "__main__":
    unittest.main()
