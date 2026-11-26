#!/usr/bin/env python3
"""Exact finite matching certificates and a simultaneous extension of one graph.

Run with Python 3. No third-party packages or network access are required.
The universal lower bound applies to every simple graph with the same degrees.
The explicit matching and extension exhibit a single realization.
"""
from bisect import bisect_right
from collections import Counter
from heapq import heapify, heappop, heappush
from math import isqrt
import json


def primes_up_to(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytes((limit - p * p) // p + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


def matching_certificate(degrees):
    """Maximize the integer consequence of the degree truncation inequality."""
    counts = Counter(degrees)
    edge_count = sum(degrees) // 2
    remaining_high_degree_sum = 2 * edge_count
    candidates = []
    for degree in sorted(counts):
        remaining_high_degree_sum -= degree * counts[degree]
        threshold = degree + 1
        kept = edge_count - remaining_high_degree_sum
        guaranteed = (kept + threshold - 1) // threshold
        candidates.append((guaranteed, -threshold, remaining_high_degree_sum))
    guaranteed, minus_threshold, high_sum = max(candidates)
    return guaranteed, -minus_threshold, high_sum


def havel_hakimi(degrees):
    heap = [(-d, vertex) for vertex, d in enumerate(degrees) if d]
    heapify(heap)
    edges = []
    while heap:
        neg_degree, vertex = heappop(heap)
        neighbors = [heappop(heap) for _ in range(-neg_degree)]
        for other_neg_degree, other in neighbors:
            edges.append((min(vertex, other), max(vertex, other)))
            if other_neg_degree < -1:
                heappush(heap, (other_neg_degree + 1, other))
    return edges


def verify_graph(edges, degrees):
    assert len(set(edges)) == len(edges)
    observed = [0] * len(degrees)
    for u, v in edges:
        assert 0 <= u < v < len(degrees)
        observed[u] += 1
        observed[v] += 1
    assert observed == degrees


def main():
    primes = primes_up_to(200_000)
    n = 10_000
    p = primes[n - 1]
    degrees = [b - a for a, b in zip([1] + primes, primes)]
    base = degrees[:n]
    bound, threshold, high_sum = matching_certificate(base)
    next_index = bisect_right(primes, p + 2 * bound)
    assert next_index < len(primes)
    new_degrees = degrees[n:next_index]
    used_edges = sum(new_degrees) // 2
    assert all(d % 2 == 0 for d in new_degrees)
    assert 0 < used_edges <= bound

    edges = havel_hakimi(base)
    verify_graph(edges, base)
    used_vertices = set()
    matched = []
    for u, v in edges:
        if u not in used_vertices and v not in used_vertices:
            used_vertices.update((u, v))
            matched.append((u, v))
    assert used_edges <= len(matched)
    deleted = set(matched[:used_edges])
    result = [edge for edge in edges if edge not in deleted]
    offset = 0
    touched = set()
    for j, d in enumerate(new_degrees, start=n):
        for u, v in matched[offset:offset + d // 2]:
            assert max(u, v) < n and u not in touched and v not in touched
            touched.update((u, v))
            result.extend(((u, j), (v, j)))
        offset += d // 2
    assert offset == used_edges
    verify_graph(result, degrees[:next_index])
    print(json.dumps({
        'starting_vertices': n, 'starting_prime': p, 'starting_edges': len(edges),
        'threshold': threshold, 'sum_of_degrees_at_least_threshold': high_sum,
        'matching_lower_bound_for_every_realization': bound,
        'last_prime_in_certified_block': primes[next_index - 1],
        'following_prime': primes[next_index],
        'new_vertices_in_certified_block': len(new_degrees),
        'old_edges_used': used_edges,
        'greedy_matching_in_test_realization': len(matched),
        'ending_edges': len(result), 'all_checks_passed': True,
    }, indent=2))


if __name__ == '__main__':
    main()
