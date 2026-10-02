"""Exact finite sanity checks of the two near-Hamiltonian graph templates.

These checks corroborate the safe-corridor argument; they are not a proof for
unbounded n. Only standard-library Python is required.
"""
from math import gcd
import argparse
import json


def elementary_cycles(graph):
    """Yield directed elementary cycles once, based at their smallest vertex."""
    for start in sorted(graph):
        def visit(vertex, path):
            for target in sorted(graph[vertex]):
                if target == start:
                    yield path
                elif target > start and target not in path:
                    yield from visit(target, path + [target])
        yield from visit(start, [start])


def check_graph(graph, safe_edges, allowed_lengths):
    count = 0
    for cycle in elementary_cycles(graph):
        edges = set(zip(cycle, cycle[1:] + cycle[:1]))
        assert len(cycle) in allowed_lengths, (cycle, allowed_lengths)
        assert safe_edges <= edges, (cycle, safe_edges - edges)
        count += 1
    # Each internal vertex of any retained corridor component remains
    # unbranched in both directions, in the whole template graph.
    incoming_vertices = {v for u, v in safe_edges}
    outgoing_vertices = {u for u, v in safe_edges}
    for vertex in incoming_vertices & outgoing_vertices:
        assert len(graph[vertex]) == 1, ('outdegree', vertex)
        assert sum(vertex in targets for targets in graph.values()) == 1, ('indegree', vertex)
    return count


def check_templates(max_n):
    graph_count = cycle_count = 0
    for n in range(6, max_n + 1):
        k = n - 1
        for j in range(n // 2 + 1, k):
            if gcd(k, j) != 1:
                continue
            a = n - j
            corridor = {(i, i - 1) for i in range(a + 1, j + 1)}
            base = {i: {i - 1 if i > 1 else k} for i in range(1, n)}
            for i in range(1, a + 1):
                base[i].add(i + j - 1)
            for replica in range(1, n):
                graph = {i: set(targets) for i, targets in base.items()}
                graph[n] = set(base[replica])
                for i, targets in base.items():
                    if replica in targets:
                        graph[i].add(n)
                safe = {edge for edge in corridor if replica not in edge}
                cycle_count += check_graph(graph, safe, {j, k})
                graph_count += 1
            graph = {i: set(targets) for i, targets in base.items()}
            graph[n] = {n - 2, j - 1}
            graph[1].add(n)
            safe = corridor - {(j, j - 1)}
            cycle_count += check_graph(graph, safe, {j, k})
            graph_count += 1
    return {'maximum_n': max_n, 'templates_checked': graph_count,
            'elementary_cycles_checked': cycle_count, 'all_checks_passed': True}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-n', type=int, default=20)
    args = parser.parse_args()
    print(json.dumps(check_templates(args.max_n), indent=2))
