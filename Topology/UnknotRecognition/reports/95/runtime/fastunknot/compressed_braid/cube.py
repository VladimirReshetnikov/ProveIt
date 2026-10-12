"""Reduced F2 cube for bounded exceptional factors, with rank transcripts.

Resolution and Frobenius construction adapted from the MIT-0 report-34 oracle
(reports/34/braidkernel/cube.py). Rank-proof production is maintained code.
This is an exponential complete fallback, not a compressed homology claim.
"""
from ..compressed_words import CompressedLimit


class DSU:
    def __init__(self, n):
        self.parent = list(range(n))
        self.size = [1] * n

    def find(self, a):
        while a != self.parent[a]:
            self.parent[a] = self.parent[self.parent[a]]
            a = self.parent[a]
        return a

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            if self.size[a] < self.size[b]:
                a, b = b, a
            self.parent[b] = a
            self.size[a] += self.size[b]


def expand_leaf(data, length, max_crossings, check):
    """Expand only a validated projected grammar after the binary preflight."""
    if length > max_crossings:
        raise CompressedLimit('exceptional factor crossing allowance exhausted')
    word, pending = [], [data['root']]
    # Skip empty children: a huge DAG of concatenated empties must not unfold.
    lengths = [0]
    for rule in data['rules'][1:]:
        check()
        lengths.append(1 if rule[0] == 'g' else lengths[rule[1]] + lengths[rule[2]])
    while pending:
        check()
        node = pending.pop()
        if not lengths[node]:
            continue
        rule = data['rules'][node]
        if rule[0] == 'g':
            word.append(rule[1])
        else:
            pending.extend((rule[2], rule[1]))
    if len(word) != length:
        raise ArithmeticError('projected expansion length mismatch')
    return word


def resolution(strands, word, state, check):
    dsu, top = DSU(strands + 2 * len(word)), list(range(strands))
    for j, g in enumerate(word):
        check()
        i = abs(g) - 1
        a, b = top[i], top[i+1]
        c, d = strands + 2*j, strands + 2*j + 1
        if bool((state >> j) & 1) == (g > 0):
            dsu.union(a, b)
            dsu.union(c, d)
        else:
            dsu.union(a, c)
            dsu.union(b, d)
        top[i], top[i+1] = c, d
    for i in range(strands):
        check()
        dsu.union(i, top[i])
    components = {}
    for i in range(strands + 2 * len(word)):
        check()
        components.setdefault(dsu.find(i), set()).add(i)
    # Vertex zero fixes the marked circle as circle zero in every resolution.
    return tuple(sorted((frozenset(c) for c in components.values()), key=min))


def edge_labels(source, target, label):
    lookup = {s: j for j, s in enumerate(target)}
    common = [(i, lookup[s]) for i, s in enumerate(source) if s in lookup]
    common_s, common_t = {i for i, _ in common}, {j for _, j in common}
    src = [i for i in range(len(source)) if i not in common_s]
    dst = [j for j in range(len(target)) if j not in common_t]
    out = sum(((label >> i) & 1) << j for i, j in common)
    if len(src) == 2 and len(dst) == 1:
        a, b = ((label >> i) & 1 for i in src)
        if a and b:
            return ()
        answer = out | ((a | b) << dst[0])
        return (answer,) if answer & 1 else ()
    if len(src) == 1 and len(dst) == 2:
        a, (u, v) = (label >> src[0]) & 1, dst
        answers = (out | (1 << u) | (1 << v),) if a else (out | (1 << u), out | (1 << v))
        return tuple(value for value in answers if value & 1)
    raise ArithmeticError('cube edge is not a merge or split')


def build_complex(strands, word, *, check, reserve):
    """Trusted explicit Frobenius construction shared with proof replay.

    reserve counts generators cumulatively before matrix allocation. All vector
    operations are exact; callers also supply a cooperative shared work check.
    """
    n = len(word)
    circles, offsets, dimensions = [], [], [0] * (n + 1)
    for state in range(1 << n):
        check()
        cs = resolution(strands, word, state, check)
        size, degree = 1 << (len(cs) - 1), state.bit_count()
        reserve(size)
        circles.append(cs)
        offsets.append(dimensions[degree])
        dimensions[degree] += size
    matrices = [[0] * dimensions[h] for h in range(n)]
    for state, source in enumerate(circles):
        check()
        h = state.bit_count()
        if h == n:
            continue
        successors = [state | (1 << j) for j in range(n) if not (state >> j) & 1]
        for label in range(1, 1 << len(source), 2):
            col = 0
            for target in successors:
                check()
                for image in edge_labels(source, circles[target], label):
                    col ^= 1 << (offsets[target] + (image >> 1))
            matrices[h][offsets[state] + (label >> 1)] = col
    return dimensions, matrices


def check_chain(matrices, check):
    """Check d squared before using dimension minus twice differential rank."""
    for source, target in zip(matrices, matrices[1:]):
        for column in source:
            check()
            value = 0
            while column:
                check()
                bit = column & -column
                value ^= target[bit.bit_length() - 1]
                column ^= bit
            if value:
                raise ArithmeticError('cube differential does not square to zero')


def rank_trace(columns, check):
    pivots, vectors, steps = {}, {}, []
    for index, column in enumerate(columns):
        check()
        used = []
        while column:
            check()
            row = column.bit_length() - 1
            if row not in pivots:
                pivots[row], vectors[index] = index, column
                break
            previous = pivots[row]
            used.append(previous)
            column ^= vectors[previous]
        steps.append(dict(xor=used, pivot=column.bit_length() - 1))
    return len(pivots), steps


def produce(data, summary, *, max_crossings, check, reserve):
    word = expand_leaf(data, summary['length'], max_crossings, check)
    dimensions, matrices = build_complex(data['strands'], word, check=check, reserve=reserve)
    check_chain(matrices, check)
    ranks, traces = [], []
    for columns in matrices:
        rank, trace = rank_trace(columns, check)
        ranks.append(rank)
        traces.append(trace)
    homology = [dim - (ranks[h] if h < len(ranks) else 0) - (ranks[h-1] if h else 0)
                for h, dim in enumerate(dimensions)]
    if any(value < 0 for value in homology) or sum(homology) < 1:
        raise ArithmeticError('invalid reduced knot homology')
    status = 'UNKNOT' if sum(homology) == 1 else 'KNOTTED'
    return dict(version='exceptional-cube-f2-v1', status=status,
                strands=data['strands'], word=word, dimensions=dimensions,
                differential_ranks=ranks, homology=homology, elimination=traces)
