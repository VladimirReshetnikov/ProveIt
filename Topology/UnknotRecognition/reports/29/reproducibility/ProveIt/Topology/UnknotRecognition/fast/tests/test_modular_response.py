"""Independent quotient determinants, completed diagrams and interruption checks."""
import copy
import itertools
import random
import unittest

from fastunknot import Diagram
from fastunknot.boundary_tait import BoundaryDeclined, BoundaryTait, coloring
from fastunknot.integer_determinant import bareiss
from fastunknot.modular_response import ModularTerminalKernel, validate_prime
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import ClosureShadow


def laplacian(size, edges):
    result = [[0] * size for _ in range(size)]
    for u, v, weight in edges:
        if u != v:
            result[u][u] += weight
            result[v][v] += weight
            result[u][v] -= weight
            result[v][u] -= weight
    return result


def quotient_minor(matrix, terminals, partition):
    """Form the entire integer quotient before grounding; no response formula."""
    blocks = {}
    labels = [blocks.setdefault(label, len(blocks)) for label in partition]
    interior = [i for i in range(len(matrix)) if i not in terminals]
    owner = {v: i for i, v in enumerate(interior)}
    owner.update({v: len(interior) + labels[i] for i, v in enumerate(terminals)})
    size = len(interior) + len(blocks)
    result = [[0] * size for _ in range(size)]
    for i in range(len(matrix)):
        for j in range(len(matrix)):
            result[owner[i]][owner[j]] += matrix[i][j]
    ground = len(interior)
    return [[result[i][j] for j in range(size) if j != ground]
            for i in range(size) if i != ground]


def dense_modular_determinant(matrix, prime):
    """Full normalized Gaussian elimination, independent of symmetric setup."""
    rows = [[value % prime for value in row] for row in matrix]
    determinant = 1
    for k in range(len(rows)):
        pivot = next((i for i in range(k, len(rows)) if rows[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            rows[k], rows[pivot] = rows[pivot], rows[k]
            determinant = -determinant
        value = rows[k][k]
        determinant = determinant * value % prime
        inverse = pow(value, prime - 2, prime)
        rows[k] = [x * inverse % prime for x in rows[k]]
        for i in range(k + 1, len(rows)):
            factor = rows[i][k]
            rows[i] = [(x - factor * y) % prime for x, y in zip(rows[i], rows[k])]
    return determinant % prime


def partitions(size):
    if size == 0:
        yield ()
        return
    for prefix in partitions(size - 1):
        for last in range(max(prefix, default=-1) + 2):
            yield prefix + (last,)


def matchings(labels):
    if not labels:
        yield ()
        return
    for i in range(1, len(labels)):
        for rest in matchings(labels[1:i] + labels[i + 1:]):
            yield ((labels[0], labels[i]),) + rest


def component_count(size, edges):
    graph = [set() for _ in range(size)]
    for left, right in edges:
        graph[left].add(right)
        graph[right].add(left)
    seen, count = set(), 0
    for start in range(size):
        if start in seen:
            continue
        count += 1
        seen.add(start)
        stack = [start]
        while stack:
            for other in graph[stack.pop()]:
                if other not in seen:
                    seen.add(other)
                    stack.append(other)
    return count


def completion_counts(pd, order, stage, pairs):
    """Rebuild all suffix darts and traverse full completion graphs."""
    suffix = [pd[i] for i in order[stage:]]
    where = {}
    for i, row in enumerate(suffix):
        for j, label in enumerate(row):
            where.setdefault(label, []).append(4 * i + j)
    alpha = [-1] * (4 * len(suffix))
    for darts in where.values():
        if len(darts) == 2:
            a, b = darts
            alpha[a], alpha[b] = b, a
    for a, b in pairs:
        left, right = where[a][0], where[b][0]
        alpha[left], alpha[right] = right, left
    assert -1 not in alpha
    edge_pairs = list(enumerate(alpha))
    shadows = component_count(len(suffix), ((a // 4, b // 4) for a, b in edge_pairs))
    links = component_count(len(alpha), edge_pairs + [(a, a ^ 2) for a in range(len(alpha))])
    zero = component_count(len(alpha), edge_pairs + [(a, a ^ 1) for a in range(len(alpha))])
    seen, faces = set(), 0
    for start in range(len(alpha)):
        if start in seen:
            continue
        faces += 1
        dart = start
        while dart not in seen:
            seen.add(dart)
            other = alpha[dart]
            dart = (other & -4) | ((other + 1) & 3)
        assert dart == start
    return shadows, links, zero, faces


class Interrupted(RuntimeError):
    pass


class Counter:
    def __init__(self, limit=None):
        self.calls, self.limit = 0, limit

    def __call__(self):
        self.calls += 1
        if self.limit is not None and self.calls >= self.limit:
            raise Interrupted("cancelled exact computation")


class ModularKernelTests(unittest.TestCase):
    def test_random_signed_quotients_against_full_modular_and_integer_determinants(self):
        rng = random.Random(261008)
        queries = singular = two_pivots = 0
        for size in range(1, 9):
            for _ in range(12):
                edges = [(i, j, rng.randrange(-4, 5)) for i in range(size)
                         for j in range(i, size) if rng.randrange(3)]
                matrix = laplacian(size, edges)
                before = copy.deepcopy(matrix)
                b = rng.randrange(1, size + 1)
                terminals = rng.sample(range(size), b)
                labels = list(partitions(b)) if b <= 4 else [
                    tuple(rng.randrange(b) for _ in range(b)) for _ in range(15)]
                for prime in (3, 5, 7, 101):
                    kernel = ModularTerminalKernel.build(matrix, terminals, prime)
                    singular += int(kernel.nullity > 0)
                    two_pivots += kernel.stats['two_pivots']
                    for partition in labels:
                        full = quotient_minor(matrix, terminals, partition)
                        actual = kernel.query(partition)
                        self.assertEqual(actual, dense_modular_determinant(full, prime))
                        self.assertEqual(actual, bareiss(copy.deepcopy(full), lambda _: None) % prime)
                        q = len(set(partition)) - 1
                        if kernel.nullity <= q:
                            self.assertLessEqual(kernel.nullity + q, 2 * (b - 1))
                        queries += 1
                self.assertEqual(matrix, before)
        self.assertGreater(queries, 1900)
        self.assertGreater(singular, 20)
        self.assertGreater(two_pivots, 0)

    def test_radical_coupling_and_forced_two_by_two_pivots(self):
        two = [[0, 1, -1], [1, 0, -1], [-1, -1, 2]]
        kernel = ModularTerminalKernel.build(two, [2], 101)
        self.assertEqual(kernel.stats['two_pivots'], 1)
        self.assertEqual((kernel.nullity, kernel.query((0,))), (0, 100))
        singular = [[0, 1, -1], [1, -1, 0], [-1, 0, 1]]
        kernel = ModularTerminalKernel.build(singular, [1, 2], 101)
        self.assertEqual(kernel.nullity, 1)
        self.assertEqual(kernel.query((0, 1)), 100)
        self.assertEqual(kernel.query((0, 0)), 0)
        self.assertEqual(kernel.query((41, 8)), 100)
        zero = ModularTerminalKernel.build([[0] * 4 for _ in range(4)], [2, 3], 7)
        self.assertTrue(zero.universal_zero)
        self.assertEqual(zero.coupling, ())
        self.assertEqual(zero.query((0, 1)), 0)
        all_terminal = ModularTerminalKernel.build([[0] * 4 for _ in range(4)], range(4), 7)
        self.assertEqual(all_terminal.query((9, 9, 9, 9)), 1)
        self.assertEqual(all_terminal.query((0, 0, 0, 1)), 0)

    def test_exceptional_primes_change_rank_without_losing_the_answer(self):
        triangle = laplacian(3, [(0, 1, 2), (0, 2, 1), (1, 2, 1)])
        good = ModularTerminalKernel.build(triangle, [1, 2], 7)
        exceptional = ModularTerminalKernel.build(triangle, [1, 2], 3)
        self.assertEqual((good.nullity, exceptional.nullity), (0, 1))
        self.assertEqual(good.query((0, 1)), 5)
        self.assertEqual(exceptional.query((0, 1)), 2)
        divisible = ModularTerminalKernel.build(triangle, [2], 5)
        self.assertEqual(divisible.query((0,)), 0)
        self.assertGreater(divisible.nullity, 0)
        matrix = [[3, 1, -4], [1, 3, -4], [-4, -4, 8]]
        mod3 = ModularTerminalKernel.build(matrix, [2], 3)
        mod5 = ModularTerminalKernel.build(matrix, [2], 5)
        self.assertEqual((mod3.stats['two_pivots'], mod5.stats['one_pivots']), (1, 2))
        self.assertEqual((mod3.query((0,)), mod5.query((0,))), (2, 3))

    def test_prime_validation_is_deterministic_within_the_supported_range(self):
        for number in range(3, 2000, 2):
            expected = all(number % d for d in range(2, int(number ** 0.5) + 1))
            if expected:
                self.assertEqual(validate_prime(number), number)
            else:
                with self.assertRaises(ValueError):
                    validate_prime(number)
        self.assertEqual(validate_prime(2147483647), 2147483647)
        for bad in (None, True, 2, 0, -7, 3.0, 2047, 1373653, 25326001,
                    2147483645, 2147483649, 4759123141):
            with self.assertRaises(ValueError):
                validate_prime(bad)
        matrix = [[1, -1], [-1, 1]]
        with self.assertRaises(ValueError):
            ModularTerminalKernel.build(matrix, [0], 9)

    def test_malformed_matrices_terminals_and_partitions(self):
        for matrix in ([], [[0], [0]], [[1, 0], [0, -1]], [[1, -1], [-2, 2]],
                       [[0.0]], [[False]], [[0, 0], [0]]):
            with self.assertRaises(ValueError):
                ModularTerminalKernel.build(matrix, [0], 7)
        matrix = [[1, -1], [-1, 1]]
        for terminals in ([], [0, 0], [-1], [2], [True], [0.0]):
            with self.assertRaises(ValueError):
                ModularTerminalKernel.build(matrix, terminals, 7)
        kernel = ModularTerminalKernel.build(matrix, [0, 1], 7)
        for partition in ((), (0,), (0, 0, 0), (0, -1), (0, True), (0, 1.0), (0, [])):
            with self.assertRaises(ValueError):
                kernel.query(partition)

    def test_callbacks_abort_setup_query_and_zero_shortcuts_without_mutation(self):
        matrix = laplacian(6, [(i, j, i + j - 3) for i in range(6) for j in range(i)])
        before = copy.deepcopy(matrix)
        for limit in (1, 30, 100, 200):
            with self.assertRaises(Interrupted):
                ModularTerminalKernel.build(matrix, [3, 4, 5], 101, Counter(limit))
            self.assertEqual(matrix, before)
        kernel = ModularTerminalKernel.build(matrix, [3, 4, 5], 101)
        state = copy.deepcopy(kernel.__dict__)
        counter = Counter()
        value = kernel.query((0, 1, 2), counter)
        self.assertGreater(counter.calls, 5)
        for limit in (1, counter.calls // 2, counter.calls):
            with self.assertRaises(Interrupted):
                kernel.query((0, 1, 2), Counter(limit))
            self.assertEqual(kernel.__dict__, state)
        self.assertEqual(kernel.query((0, 1, 2)), value)
        zero = ModularTerminalKernel.build([[0] * 3 for _ in range(3)], [2], 7)
        with self.assertRaises(Interrupted):
            zero.query((0,), Counter(3))
        with self.assertRaises(Interrupted):
            validate_prime(2147483647, Counter(5))


class BoundaryGeometryTests(unittest.TestCase):
    def test_live_completions_against_full_geometry_and_exact_shadow(self):
        rng = random.Random(261009)
        accepted = queries = disconnected = 0
        while accepted < 24:
            strands = rng.randrange(2, 5)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 10))]
            try:
                diagram = Diagram.from_braid(strands, word)
            except ValueError:
                continue
            accepted += 1
            for diagram in (diagram, diagram.mirror()):
                order = list(range(diagram.crossings))
                rng.shuffle(order)
                palette = coloring(diagram.pd)
                exact = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
                scan = FastScan(shape_cache=False)
                for stage, index in enumerate(order):
                    geometry = BoundaryTait(diagram.pd, order, stage, palette)
                    self.assertIs(geometry.palette, palette)
                    kernels = [ModularTerminalKernel.build(geometry.laplacian,
                                                          geometry.terminals, p)
                               for p in (3, 5, 101)]
                    for matching in set(scan.mid) - {None}:
                        pairs = scan.algebra.pairs[matching]
                        data = geometry.partition(pairs)
                        shadow, links, zero, faces = completion_counts(diagram.pd, order, stage, pairs)
                        self.assertEqual(data['shadow_components'], shadow)
                        self.assertEqual(data['link_components'], links)
                        self.assertEqual(data['zero_circles'], zero)
                        self.assertEqual(faces, geometry.n + 2 * shadow)
                        self.assertEqual(data['unreduced_euler'], exact.evaluate_one(stage, pairs))
                        vector = exact.evaluate(stage, pairs)
                        expected = (vector[0] - vector[2], vector[1] - vector[3])
                        unit = ((1, 0), (0, -1), (-1, 0), (0, 1))[data['phase']]
                        for kernel in kernels:
                            value = kernel.query(data['partition']) if shadow == 1 else 0
                            actual = tuple(x * value % kernel.prime for x in unit)
                            self.assertEqual(actual, tuple(x % kernel.prime for x in expected))
                        self.assertEqual(tuple(dict.fromkeys(data['partition'])),
                                         tuple(range(len(set(data['partition'])))))
                        queries += 1
                        disconnected += int(shadow > 1)
                    scan.add_crossing(diagram.pd[index])
        self.assertGreater(queries, 500)
        self.assertGreater(disconnected, 0)

    def test_arbitrary_pairings_are_checked_before_any_residue(self):
        declined = nonspherical = accepted = 0
        diagram = Diagram.from_braid(3, [1, 2] * 4)
        order = [0, 3, 6, 1, 4, 7, 2, 5]
        for stage in range(2, 7):
            geometry = BoundaryTait(diagram.pd, order, stage)
            if len(geometry.labels) > 8:
                continue
            for pairs in matchings(geometry.labels):
                shadow, _, _, faces = completion_counts(diagram.pd, order, stage, pairs)
                try:
                    data = geometry.partition(pairs)
                except BoundaryDeclined:
                    declined += 1
                except ValueError:
                    nonspherical += 1
                    self.assertNotEqual(faces, geometry.n + 2 * shadow)
                else:
                    accepted += 1
                    self.assertEqual(faces, geometry.n + 2 * shadow)
                    self.assertEqual(data['shadow_components'], shadow)
        self.assertGreater(declined, 0)
        self.assertGreater(nonspherical, 0)
        self.assertGreater(accepted, 0)

    def test_malformed_sources_orders_palettes_and_pair_coverage(self):
        for pd in ((), ((0, 0, 0, 0),), ((0, 1, 0, 1),), ((0, 0, 1),),
                   ((0, 0, 1, True),), ((0, 0, 1, 2),)):
            with self.assertRaises(ValueError):
                BoundaryTait(pd, list(range(len(pd))), 0)
        diagram = Diagram.from_braid(2, [1, 1, 1])
        for order in ([], [0, 1], [0, 1, 1], [0, 1, 3], [False, 1, 2]):
            with self.assertRaises(ValueError):
                BoundaryTait(diagram.pd, order, 0)
        for stage in (-1, 3, True, 1.0):
            with self.assertRaises(ValueError):
                BoundaryTait(diagram.pd, [0, 1, 2], stage)
        for palette in ((), (0,) * 12, (2,) * 12, (True,) * 12):
            with self.assertRaises(ValueError):
                BoundaryTait(diagram.pd, [0, 1, 2], 1, palette)
        palette = coloring(diagram.pd)
        geometry = BoundaryTait(diagram.pd, [0, 1, 2], 1, tuple(palette))
        scan = FastScan(shape_cache=False)
        scan.add_crossing(diagram.pd[0])
        pairs = scan.algebra.pairs[next(m for m in scan.mid if m is not None)]
        self.assertEqual(geometry.partition(pairs),
                         BoundaryTait(diagram.pd, [0, 1, 2], 1, palette).partition(pairs))
        a = geometry.labels[0]
        for bad in ((), pairs + (pairs[0],), ((-1, -2),) + pairs[1:],
                    ((a, a),) + pairs[1:], ((a,),) + pairs[1:], ((a, True),) + pairs[1:]):
            with self.assertRaises(ValueError):
                geometry.partition(bad)
        with self.assertRaises(AttributeError):
            palette.colors = ()
        closed = BoundaryTait(diagram.pd, [0, 1, 2], 0, palette)
        self.assertEqual((closed.labels, closed.partition(())['partition']), ((), (0,)))

    def test_callbacks_and_boundary_query_work_do_not_depend_on_suffix_length(self):
        query_counts = []
        for length in (3, 43):
            diagram = Diagram.from_braid(2, [1] * length)
            order = list(range(length))
            palette = coloring(diagram.pd)
            for limit in (1, 10, 30):
                with self.assertRaises(Interrupted):
                    BoundaryTait(diagram.pd, order, 1, palette, Counter(limit))
            geometry = BoundaryTait(diagram.pd, order, 1, palette)
            scan = FastScan(shape_cache=False)
            scan.add_crossing(diagram.pd[0])
            pairs = scan.algebra.pairs[next(m for m in scan.mid if m is not None)]
            check = Counter()
            expected = geometry.partition(pairs, check)
            query_counts.append(check.calls)
            for limit in (1, check.calls // 2, check.calls):
                with self.assertRaises(Interrupted):
                    geometry.partition(pairs, Counter(limit))
            self.assertEqual(geometry.partition(pairs), expected)
        self.assertEqual(query_counts[0], query_counts[1])
        with self.assertRaises(Interrupted):
            coloring(Diagram.from_braid(2, [1, 1, 1]).pd, Counter(30))


if __name__ == '__main__':
    unittest.main()
