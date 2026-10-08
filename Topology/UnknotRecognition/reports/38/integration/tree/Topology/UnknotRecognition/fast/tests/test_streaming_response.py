"""Independent graph/cofactor checks for the reverse suffix compiler."""
import random
import unittest

from fastunknot.diagram import Diagram
from fastunknot.integer_determinant import bareiss
from fastunknot.scan_fast import FastScan
from fastunknot.shadow_scan import ClosureShadow
from fastunknot.streaming_response import (
    ResponseBudget, StreamingResponse, compile_suffix_responses, iter_suffix_responses,
)


def palette(diagram):
    alpha = diagram.alpha()
    faces = diagram.faces()
    owner = {dart: i for i, face in enumerate(faces) for dart in face}
    adjacent = [set() for _ in faces]
    for dart, other in enumerate(alpha):
        adjacent[owner[dart]].add(owner[other])
    colors = {0: 0}
    queue = [0]
    for face in queue:
        for other in adjacent[face]:
            if other not in colors:
                colors[other] = 1 - colors[face]
                queue.append(other)
    return tuple(colors[owner[d]] for d in range(len(alpha)))


def independent_suffix_graph(diagram, order, stage):
    """Rebuild by graph components, without compiler union-find or responses."""
    color = palette(diagram)
    alpha = diagram.alpha()
    darts = {4 * crossing + j for crossing in order[stage:] for j in range(4)}
    neighbors = {d: set() for d in darts}
    for dart in darts:
        other = alpha[dart]
        if other in darts:
            target = 4 * (other // 4) + (other + 1) % 4
            neighbors[dart].add(target)
            neighbors[target].add(dart)
    groups, seen = [], set()
    for start in sorted(darts):
        if start in seen:
            continue
        group, pending = set(), [start]
        while pending:
            dart = pending.pop()
            if dart in group:
                continue
            group.add(dart)
            pending.extend(neighbors[dart] - group)
        groups.append(group)
        seen.update(group)
    black = [group for group in groups if color[next(iter(group))]]
    owner = {dart: i for i, group in enumerate(black) for dart in group}
    matrix = [[0] * len(black) for _ in black]
    for crossing in order[stage:]:
        slots = [j for j in range(4) if color[4 * crossing + j]]
        u, v = (owner[4 * crossing + j] for j in slots)
        weight = -1 if slots == [0, 2] else 1
        if u != v:
            matrix[u][u] += weight
            matrix[v][v] += weight
            matrix[u][v] -= weight
            matrix[v][u] -= weight
    return matrix, owner


def cofactor(matrix, terminals, partition, prime):
    """Integer quotient followed by the preexisting fraction-free reference."""
    blocks = {vertex: ("interior", vertex) for vertex in range(len(matrix))}
    for vertex, block in zip(terminals, partition):
        blocks[vertex] = ("terminal", block)
    names = {}
    ids = [names.setdefault(blocks[v], len(names)) for v in range(len(matrix))]
    quotient = [[0] * len(names) for _ in names]
    for i in range(len(matrix)):
        for j in range(len(matrix)):
            quotient[ids[i]][ids[j]] += matrix[i][j]
    ground = ids[terminals[0]]
    minor = [[value for j, value in enumerate(row) if j != ground]
             for i, row in enumerate(quotient) if i != ground]
    return bareiss(minor, lambda amount: None) % prime


def graph_laplacian(vertices, edges):
    names = {v: i for i, v in enumerate(sorted(vertices))}
    matrix = [[0] * len(names) for _ in names]
    for a, b, weight in edges:
        u, v = names[a], names[b]
        if u != v:
            matrix[u][u] += weight
            matrix[v][v] += weight
            matrix[u][v] -= weight
            matrix[v][u] -= weight
    return matrix, names


class StreamingResponseTests(unittest.TestCase):
    def test_singular_interior_survives_and_two_pivot_repairs_it(self):
        state = StreamingResponse.empty(2)
        state = state.advance((0, 1, 2), ((0, 1, 1), (1, 2, 1)),
                              {0: 0, 1: 1, 2: 2}, (0, 2))
        self.assertEqual(state.radical, 1)
        self.assertFalse(state.zero)
        self.assertEqual(state.query((0, 1)), 1)
        self.assertEqual(state.query((0, 0)), 0)
        state = state.advance((3,), ((2, 3, 1),), {0: 0, 2: 2, 3: 3}, (0, 3))
        self.assertEqual(state.query((0, 1)), 1)
        self.assertEqual(dict(state.stats)["two_pivots"], 1)
        self.assertEqual(state.radical, 0)

    def test_absorbing_zero_under_future_attachments(self):
        state = StreamingResponse.empty(101)
        state = state.advance((0, 1), ((0, 1, 1), (0, 1, -1)),
                              {0: 0, 1: 1}, (0,))
        self.assertTrue(state.zero)
        for vertex in range(2, 12):
            state = state.advance((vertex,), ((0, vertex, vertex),),
                                  {0: 0, vertex: vertex}, (0,))
            self.assertTrue(state.zero)
            self.assertEqual(state.query((0,)), 0)

    def test_random_graph_streams_with_merges_and_forgetting(self):
        rng = random.Random(2026100804)
        for prime in (2, 3, 5, 101):
            for repeat in range(10):
                state = StreamingResponse.empty(prime)
                vertices, edges = {0}, []
                state = state.advance((0,), (), {0: 0}, (0,))
                for vertex in range(1, 19):
                    current = state.terminals + (vertex,)
                    identifications = {v: v for v in current}
                    new_edges = [(rng.choice(state.terminals), vertex,
                                  rng.choice((-3, -2, -1, 1, 2, 3)))]
                    if len(current) >= 3 and rng.random() < 0.45:
                        first, second = rng.sample(current, 2)
                        first, second = sorted((first, second))
                        identifications[second] = first
                    merged = set(identifications.values())
                    keep = tuple(sorted(v for v in merged if v == 0 or rng.random() < 0.8))
                    state = state.advance((vertex,), new_edges, identifications, keep)
                    vertices.add(vertex)
                    vertices = {identifications.get(v, v) for v in vertices}
                    edges = [(identifications.get(a, a), identifications.get(b, b), w)
                             for a, b, w in edges + new_edges]
                    matrix, names = graph_laplacian(vertices, edges)
                    for _ in range(4):
                        partition = tuple(rng.randrange(3) for _ in keep)
                        expected = cofactor(matrix, [names[v] for v in keep], partition, prime)
                        self.assertEqual(state.query(partition), expected)

    def test_all_suffixes_against_independent_integer_cofactors(self):
        rng = random.Random(98123)
        diagrams = []
        for _ in range(90):
            strands = rng.randrange(2, 6)
            word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                    for _ in range(rng.randrange(1, 17))]
            try:
                diagrams.append(Diagram.from_braid(strands, word))
            except ValueError:
                pass
        self.assertGreater(len(diagrams), 20)
        for diagram in diagrams:
            order = list(range(diagram.crossings))
            rng.shuffle(order)
            for prime in (2, 3, 101):
                snapshots = compile_suffix_responses(diagram.pd, order, prime)
                for stage, snapshot in enumerate(snapshots):
                    matrix, owner = independent_suffix_graph(diagram, order, stage)
                    state = snapshot.response
                    terminals = [owner[v] for v in state.terminals]
                    for _ in range(5):
                        partition = tuple(rng.randrange(4) for _ in terminals)
                        self.assertEqual(state.query(partition),
                                         cofactor(matrix, terminals, partition, prime))
                    self.assertLessEqual(dict(state.stats)["max_new_interior"], 4)

    def test_actual_scanner_completions_and_raw_phase(self):
        rng = random.Random(7482)
        for strands, word in ((2, [1] * 7), (3, [1, 2] * 5),
                              (3, [1, -2] * 4), (4, [1, 2, 3] * 3)):
            for diagram in (Diagram.from_braid(strands, word),
                            Diagram.from_braid(strands, word).mirror()):
                order = list(range(diagram.crossings))
                rng.shuffle(order)
                snapshots = compile_suffix_responses(diagram.pd, order, 101)
                scan = FastScan(shape_cache=False)
                reference = ClosureShadow(diagram.pd, order, max_states=None, max_work=None)
                for stage, snapshot in enumerate(snapshots):
                    for matching in set(scan.mid) - {None}:
                        pairs = scan.algebra.pairs[matching]
                        value = reference.evaluate(stage, pairs)
                        expected = ((value[0] - value[2]) % 101,
                                    (value[1] - value[3]) % 101)
                        self.assertEqual(snapshot.query(pairs)["value_i"], expected)
                    scan.add_crossing(diagram.pd[order[stage]])

    def test_validation_and_immutable_snapshots(self):
        for prime in (-1, 0, 1, 4, 9, 341, 561, 1 << 31, True):
            with self.assertRaises(ValueError):
                StreamingResponse.empty(prime)
        state = StreamingResponse.empty(101)
        state = state.advance((0, 1), ((0, 1, 1),), {0: 0, 1: 1}, (0,))
        with self.assertRaises(AttributeError):
            state.factor = 0
        with self.assertRaises(ValueError):
            state.advance((2,), ((1, 2, 1),), {0: 0, 2: 2}, (0, 2))
        with self.assertRaises(ValueError):
            state.query(())
        diagram = Diagram.from_braid(2, [1] * 3)
        snapshot = compile_suffix_responses(diagram.pd)[1]
        with self.assertRaises(ValueError):
            snapshot.query(())
        with self.assertRaises(ValueError):
            compile_suffix_responses(diagram.pd, [0, 0, 1])
        with self.assertRaises(ValueError):
            compile_suffix_responses([[0, 1, 2, 3]])
        self.assertEqual(compile_suffix_responses([]), ())

    def test_cancellation_never_changes_a_published_response(self):
        state = StreamingResponse.empty(101)
        state = state.advance((0, 1), ((0, 1, 1),), {0: 0, 1: 1}, (0, 1))
        before = (state.matrix, state.stats, state.factor, state.terminals)
        for cutoff in (1, 5, 12, 20, 30):
            calls = 0

            def stop():
                nonlocal calls
                calls += 1
                if calls == cutoff:
                    raise TimeoutError("test cancellation")

            with self.assertRaises(TimeoutError):
                state.advance((2, 3), ((1, 2, 1), (2, 3, -1)),
                              {0: 0, 1: 1, 2: 2, 3: 3}, (0, 3), stop)
            self.assertEqual((state.matrix, state.stats, state.factor, state.terminals), before)
        diagram = Diagram.from_braid(2, [1] * 11)
        calls = 0

        def stop_source():
            nonlocal calls
            calls += 1
            if calls == 15:
                raise TimeoutError("source cancellation")

        with self.assertRaises(TimeoutError):
            next(iter_suffix_responses(diagram.pd, check=stop_source))

    def test_frontier_and_retained_storage_allowances(self):
        diagram = Diagram.from_braid(3, [1, 2] * 8)
        ordinary = compile_suffix_responses(diagram.pd)
        total = sum(len(s.response.matrix) ** 2 for s in ordinary)
        capped = compile_suffix_responses(diagram.pd, max_boundary=6,
                                           max_stored_elements=total)
        self.assertEqual(capped[0].query(()), ordinary[0].query(()))
        with self.assertRaises(ResponseBudget):
            compile_suffix_responses(diagram.pd, max_boundary=3)
        with self.assertRaises(ResponseBudget):
            compile_suffix_responses(diagram.pd, max_stored_elements=total - 1)
        for kwargs in ({"max_boundary": -1}, {"max_stored_elements": True}):
            with self.assertRaises(ValueError):
                compile_suffix_responses(diagram.pd, **kwargs)


if __name__ == "__main__":
    unittest.main()
