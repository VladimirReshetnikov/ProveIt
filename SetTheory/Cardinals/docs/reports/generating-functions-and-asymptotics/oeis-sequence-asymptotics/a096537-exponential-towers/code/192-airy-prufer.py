#!/usr/bin/env python3
"""Independent exhaustive Cayley-tree enumeration with root label zero.

No tower recurrence or generated coefficient fixture is imported here.
Pruefer strings of length n-1 enumerate all trees on n+1 distinct labels.
"""
from heapq import heapify, heappop, heappush
from itertools import product

MAX_N = 7


def need(condition, message):
    if not condition:
        raise ValueError(message)


def decode(sequence, vertices):
    need(type(vertices) is int and 2 <= vertices <= MAX_N+1, 'vertex domain')
    need(type(sequence) in (tuple, list) and len(sequence) == vertices-2, 'Pruefer length')
    need(all(type(v) is int and 0 <= v < vertices for v in sequence), 'Pruefer labels')
    degree = [1] * vertices
    for vertex in sequence:
        degree[vertex] += 1
    leaves = [v for v, d in enumerate(degree) if d == 1]
    heapify(leaves)
    adjacency = [[] for _ in degree]
    for vertex in sequence:
        leaf = heappop(leaves)
        adjacency[leaf].append(vertex)
        adjacency[vertex].append(leaf)
        degree[vertex] -= 1
        if degree[vertex] == 1:
            heappush(leaves, vertex)
    first, second = leaves
    adjacency[first].append(second)
    adjacency[second].append(first)
    return adjacency


def depths(adjacency):
    vertices = len(adjacency)
    need(1 <= vertices <= MAX_N+1, 'adjacency domain')
    result = [-1] * vertices
    result[0] = 0
    stack = [0]
    while stack:
        vertex = stack.pop()
        for neighbor in adjacency[vertex]:
            need(type(neighbor) is int and 0 <= neighbor < vertices, 'invalid neighbor')
            if result[neighbor] < 0:
                result[neighbor] = result[vertex] + 1
                stack.append(neighbor)
    need(all(d >= 0 for d in result), 'decoded graph is disconnected')
    return result


def enumerate_trees(n):
    need(type(n) is int and 0 <= n <= MAX_N, 'exhaustive tree domain n=0..7')
    if n == 0:
        return {'n': 0, 'trees': 1, 'depth_product_sum': 1,
                'height_sums': [1], 'shift_two_sum': 1}
    sums = [0] * (n+1)
    count = 0
    shift_two = 0
    for sequence in product(range(n+1), repeat=n-1):
        distance = depths(decode(sequence, n+1))
        weight = shifted = 1
        for depth in distance[1:]:
            weight *= depth
            shifted *= depth + 1
        sums[max(distance)] += weight
        shift_two += shifted
        count += 1
    need(count == (n+1)**(n-1), 'Cayley enumeration count')
    return {'n': n, 'trees': count, 'depth_product_sum': sum(sums),
            'height_sums': sums, 'shift_two_sum': shift_two}
