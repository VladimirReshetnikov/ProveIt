"""Finite reference calculations for the Schreier and folding proofs.

Represent letters by signed positive integers, and a geometric edge by
(tail, positive letter, head). Its reverse has the negative letter.
Running this file uses the Python standard library only.
"""
from collections import deque
from itertools import groupby, product


def inverse(word):
    return tuple(-a for a in reversed(word))


def reduce_word(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def orientations(edges):
    for index, (tail, letter, head) in enumerate(edges):
        yield tail, letter, head, index
        yield head, -letter, tail, index


class BasedGraph:
    """A connected deterministic inverse graph, with base vertex 0."""

    def __init__(self, edges):
        self.next = {}
        for tail, letter, head, index in orientations(edges):
            assert (tail, letter) not in self.next
            self.next[tail, letter] = head, index
        outgoing = {}
        for tail, letter in self.next:
            outgoing.setdefault(tail, []).append(letter)

        routes = {0: ()}
        tree = set()
        queue = deque([0])
        while queue:
            tail = queue.popleft()
            for letter in sorted(outgoing.get(tail, [])):
                head, index = self.next[tail, letter]
                if head not in routes:
                    routes[head] = routes[tail] + (letter,)
                    tree.add(index)
                    queue.append(head)

        self.positive_basis = []
        self.symbol = {}
        for index, (tail, letter, head) in enumerate(edges):
            assert tail in routes and head in routes
            if index not in tree:
                loop = routes[tail] + (letter,) + inverse(routes[head])
                self.positive_basis.append(reduce_word(loop))
                self.symbol[index] = len(self.positive_basis)
        self.vertex_count = len(routes)
        self.edge_count = len(edges)
        assert len(self.positive_basis) == self.edge_count - self.vertex_count + 1

    def read(self, word):
        """Return reduced basis coordinates, or None for a nonmember."""
        vertex, output = 0, []
        for letter in reduce_word(word):
            step = self.next.get((vertex, letter))
            if step is None:
                return None
            vertex, index = step
            symbol = self.symbol.get(index)
            if symbol is not None:
                output.append(symbol if letter > 0 else -symbol)
        return reduce_word(output) if vertex == 0 else None

    def expand(self, word):
        output = []
        for letter in word:
            value = self.positive_basis[abs(letter) - 1]
            output.extend(value if letter > 0 else inverse(value))
        return reduce_word(output)


def action_graph(permutations, degree):
    edges = []
    for letter, table in enumerate(permutations, start=1):
        assert sorted(table) == list(range(degree))
        edges.extend((v, letter, table[v]) for v in range(degree))
    graph = BasedGraph(edges)
    assert graph.vertex_count == degree
    return graph


def folded_graph(generators):
    edges = []
    fresh_vertex = 1
    for word in generators:
        tail = 0
        for pos, letter in enumerate(word):
            assert letter != 0
            head = 0 if pos + 1 == len(word) else fresh_vertex
            if head != 0:
                fresh_vertex += 1
            if letter > 0:
                edges.append((tail, letter, head))
            else:
                edges.append((head, -letter, tail))
            tail = head

    original_size = len(edges)
    for _ in range(original_size + 1):
        seen = {}
        for tail, letter, head, index in orientations(edges):
            key = tail, letter
            if key not in seen:
                seen[key] = head
                continue
            # The two equally labelled transitions have a common initial
            # vertex. After merging their targets, discard the duplicate edge.
            keep, discard = sorted((head, seen[key]))
            edges = [(keep if u == discard else u, a, keep if v == discard else v)
                     for j, (u, a, v) in enumerate(edges) if j != index]
            break
        else:
            return BasedGraph(edges), original_size - len(edges)
    raise AssertionError("Fold count exceeded the number of initial edges")


def words(rank, limit, *, reduced=False):
    letters = tuple(a for i in range(1, rank + 1) for a in (i, -i))
    for length in range(limit + 1):
        for w in product(letters, repeat=length):
            if not reduced or all(a != -b for a, b in zip(w, w[1:])):
                yield w


def verify(graph, rank, membership):
    count = 0
    for word in words(rank, 5):
        coordinates = graph.read(word)
        assert (coordinates is not None) == membership(word)
        if coordinates is not None:
            assert graph.expand(coordinates) == reduce_word(word)
        count += 1
    for basis_word in words(len(graph.positive_basis), 3, reduced=True):
        assert graph.read(graph.expand(basis_word)) == basis_word
        count += 1
    return count


def main():
    total = 0

    # The cycle (0 1 2) and the transposition (1 2) give a noncommuting
    # action. The independent token calculation handles inverse rotations.
    tables = [(1, 2, 0), (0, 2, 1)]
    def fixes_zero(word):
        position = 0
        for letter in word:
            if abs(letter) == 1:
                position = (position + (1 if letter > 0 else -1)) % 3
            else:
                position = (-position) % 3
        return position == 0
    action = action_graph(tables, 3)
    assert len(action.positive_basis) == 4
    total += verify(action, 2, fixes_zero)

    # The kernel of F(a,b) -> Z/2, a |-> 1, b |-> 0, has rank three.
    parity_generators = [(2,), (1, 1), (1, 2, -1)]
    parity = lambda w: sum(abs(a) == 1 for a in w) % 2 == 0
    graph, folds = folded_graph(parity_generators)
    assert folds > 0 and graph.vertex_count == 2 and len(graph.positive_basis) == 3
    total += verify(graph, 2, parity)
    parity_action = action_graph([(1, 0), (0, 1)], 2)
    total += verify(parity_action, 2, parity)

    # A cyclic subgroup with a nontrivial stem; the second word is the square
    # of the first. A nonidentity reduced member is precisely a b^k a^-1.
    conjugate, folds = folded_graph([(1, 2, -1), (1, 2, 2, -1)])
    assert folds > 0 and len(conjugate.positive_basis) == 1
    def conjugate_power(word):
        w = reduce_word(word)
        return (not w or (len(w) >= 3 and w[0] == 1 and w[-1] == -1
                          and all(abs(a) == 2 for a in w[1:-1])))
    total += verify(conjugate, 2, conjugate_power)

    # Each syllable of a reduced member of <a^2,b^2> has even length.
    squares, _ = folded_graph([(1, 1), (2, 2)])
    def even_syllables(word):
        return all(sum(1 for _ in run) % 2 == 0
                   for _, run in groupby(reduce_word(word), key=abs))
    total += verify(squares, 2, even_syllables)

    trivial, _ = folded_graph([(), (1, -1)])
    total += verify(trivial, 2, lambda w: not reduce_word(w))
    empty, _ = folded_graph([])
    total += verify(empty, 0, lambda w: not w)
    assert action_graph([], 1).positive_basis == []
    print(f"Schreier checks passed: {total} word tests, including folds and basis round trips.")


if __name__ == "__main__":
    main()
