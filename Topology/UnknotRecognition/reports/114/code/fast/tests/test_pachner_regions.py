import itertools
import unittest

from fastunknot.pachner_regions import connected_regions, footprint_regions


def components(graph, selected):
    unseen = set(selected)
    count = 0
    while unseen:
        count += 1
        todo = [unseen.pop()]
        while todo:
            v = todo.pop()
            new = set(graph[v]) & unseen
            unseen.difference_update(new)
            todo.extend(new)
    return count


class RegionEnumerationTests(unittest.TestCase):
    def check_graph(self, graph):
        n = len(graph)
        subsets = [tuple(i for i in range(n) if mask >> i & 1)
                   for mask in range(1 << n)]
        for size in range(n+1):
            expected = {s for s in subsets
                        if len(s) <= size and components(graph, s) == 1}
            got = list(connected_regions(graph, size))
            self.assertEqual(len(got), len(set(got)))
            self.assertEqual(set(got), expected)
            for bound in range(min(3, size)+1):
                expected = {s for s in subsets
                            if len(s) <= size and components(graph, s) <= bound}
                got = list(footprint_regions(graph, size, bound))
                self.assertEqual(len(got), len(set(got)))
                self.assertEqual(set(got), expected)

    def test_every_graph_through_four_vertices(self):
        for n in range(5):
            edges = list(itertools.combinations(range(n), 2))
            for mask in range(1 << len(edges)):
                graph = [set() for _ in range(n)]
                for i, (a, b) in enumerate(edges):
                    if mask >> i & 1:
                        graph[a].add(b)
                        graph[b].add(a)
                self.check_graph(graph)

    def test_larger_structured_graphs(self):
        self.check_graph([{1}, {0, 2}, {1, 3}, {2, 4}, {3, 5}, {4}])
        self.check_graph([{1, 5}, {0, 2}, {1, 3}, {2, 4}, {3, 5}, {0, 4}])
        self.check_graph([{1, 2, 3, 4}, {0}, {0}, {0}, {0}, set()])

    def test_empty_option_and_duplicated_edges(self):
        self.assertEqual(list(footprint_regions([], 3, 3)), [()])
        self.assertEqual(list(footprint_regions([], 3, 3, include_empty=False)), [])
        graph = [[0, 1, 1], [0, 0]]
        self.assertEqual(set(connected_regions(graph, 2)), {(0,), (1,), (0, 1)})

    def test_invalid_and_cancellation(self):
        for graph in ([[1], []], [[2], []], [[True], [0]]):
            with self.assertRaises(ValueError):
                list(connected_regions(graph, 2))
        for bound in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                list(connected_regions([], bound))
        class Cancelled(RuntimeError):
            pass
        def cancel():
            raise Cancelled('cancel')
        with self.assertRaises(Cancelled):
            list(connected_regions([[]], 1, check=cancel))


if __name__ == '__main__':
    unittest.main()
