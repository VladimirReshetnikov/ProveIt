"""Exact cyclic-word operations. Integers encode signed free generators."""
from __future__ import annotations
from collections import Counter
from collections.abc import Iterable

Word = tuple[int, ...]
Graph = dict[tuple[int, int], int]

class ResourceLimit(RuntimeError):
    """Local exhaustion: never evidence of nontriviality."""

class Budget:
    def __init__(self, max_work: int = 10_000_000, check=lambda: None):
        if type(max_work) is not int or max_work < 0:
            raise ValueError("max_work must be a nonnegative integer")
        self.left = max_work
        self.used = 0
        self.check = check

    def tick(self, amount: int = 1) -> None:
        self.check()
        self.used += amount
        self.left -= amount
        if self.left < 0:
            raise ResourceLimit("local work allowance exhausted")


def validate_words(words: Iterable[Iterable[int]], alive: Iterable[int]) -> tuple[list[Word], tuple[int, ...]]:
    generators = tuple(sorted(alive))
    if not generators or any(type(x) is not int or x <= 0 for x in generators):
        raise ValueError("alive must contain positive integer generator names")
    if len(set(generators)) != len(generators):
        raise ValueError("duplicate generator")
    gs = set(generators)
    result = []
    for word in words:
        w = tuple(word)
        if any(type(x) is not int or abs(x) not in gs for x in w):
            raise ValueError("invalid or inactive signed letter")
        if cyclic_reduce(w) != w:
            raise ValueError("input words must be freely and cyclically reduced")
        result.append(w)
    return result, generators


def free_reduce(letters: Iterable[int], *, cap: int | None = None) -> Word:
    stack: list[int] = []
    for x in letters:
        if stack and stack[-1] == -x:
            stack.pop()
        else:
            stack.append(x)
            if cap is not None and len(stack) > cap:
                raise ResourceLimit("literal stack allowance exhausted")
    return tuple(stack)


def cyclic_reduce(letters: Iterable[int], *, cap: int | None = None) -> Word:
    stack = free_reduce(letters, cap=cap)
    left, right = 0, len(stack)
    while right-left > 1 and stack[left] == -stack[right-1]:
        left += 1
        right -= 1
    return stack[left:right]


def inverse(word: Iterable[int]) -> Word:
    return tuple(-x for x in reversed(tuple(word)))


def whitehead_image(x: int, a: int, shore: set[int]) -> Word:
    if abs(x) == abs(a):
        return (x,)
    return ((-a,) if -x in shore else ()) + (x,) + ((a,) if x in shore else ())


def apply_whitehead(words: list[Word], a: int, shore: set[int], budget: Budget, cap: int) -> list[Word]:
    if a not in shore or -a in shore:
        raise ValueError("not an admissible Whitehead shore")
    before = sum(map(len, words))
    if 3*before > cap:
        raise ResourceLimit("Whitehead workspace allowance exhausted")
    budget.tick(3*before + 1)
    return [cyclic_reduce(y for x in w for y in whitehead_image(x, a, shore)) for w in words]


def eliminate(words: list[Word], j: int, g: int, budget: Budget, cap: int) -> list[Word]:
    positions = [i for i, x in enumerate(words[j]) if abs(x) == g]
    if len(positions) != 1:
        raise ValueError("the selected relation is not defining")
    p = positions[0]
    pivot = words[j]
    rest = pivot[p+1:] + pivot[:p]
    value = inverse(rest) if pivot[p] > 0 else rest
    total = sum(map(len, words))
    count = sum(sum(abs(x) == g for x in w) for w in words)
    raw_bound = total-len(pivot)+(count-1)*(len(pivot)-2)
    if raw_bound > cap:
        raise ResourceLimit("substitution allocation allowance exhausted")
    budget.tick(total + raw_bound + 1)
    images = {g: value, -g: inverse(value)}
    return [() if i == j else cyclic_reduce(y for x in w for y in images.get(x, (x,)))
            for i, w in enumerate(words)]


def word_graph(word: Word) -> Graph:
    result: Counter[tuple[int, int]] = Counter()
    for i, x in enumerate(word):
        y = -word[(i+1) % len(word)]
        if x == y:
            raise ValueError("a reducible cyclic word has a graph loop")
        result[tuple(sorted((x, y)))] += 1
    return dict(result)


def add_graphs(graphs: Iterable[Graph]) -> Graph:
    result: Counter[tuple[int, int]] = Counter()
    for graph in graphs:
        result.update(graph)
    return dict(result)


def degrees(graph: Graph, vertices: Iterable[int]) -> dict[int, int]:
    result = dict.fromkeys(vertices, 0)
    for (u, v), weight in graph.items():
        result[u] += weight
        result[v] += weight
    return result


def cut_capacity(graph: Graph, shore: set[int]) -> int:
    return sum(c for (u, v), c in graph.items() if (u in shore) != (v in shore))


def validate_graph(graph: Graph, vertices: tuple[int, ...]) -> None:
    allowed = set(vertices)
    for edge, capacity in graph.items():
        if (type(edge) is not tuple or len(edge) != 2 or any(type(x) is not int for x in edge)
                or edge[0] >= edge[1] or not set(edge) <= allowed
                or type(capacity) is not int or capacity <= 0):
            raise ValueError("invalid canonical positive-capacity graph")
