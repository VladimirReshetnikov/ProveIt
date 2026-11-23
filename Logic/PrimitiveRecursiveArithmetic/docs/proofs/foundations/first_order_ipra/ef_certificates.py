"""Finite relational Ehrenfeucht--Fraisse games with distinguishing formulas.

Run with Python 3.10 or newer: python ef_certificates.py
An environment tuple is indexed from the front. A quantifier prepends its move.
The relation signature is the tuple of arities; nullary relations are supported.
"""
from dataclasses import dataclass
from functools import cache
from itertools import permutations, product


@dataclass(frozen=True)
class Structure:
    size: int
    arities: tuple
    relations: tuple

    def __post_init__(self):
        if self.size < 1 or len(self.arities) != len(self.relations):
            raise ValueError("expected a nonempty carrier and one table per symbol")
        for arity, table in zip(self.arities, self.relations):
            if arity < 0 or any(
                len(row) != arity or any(v not in range(self.size) for v in row)
                for row in table
            ):
                raise ValueError("invalid relation table")


def value(model, formula, env=()):
    op, *args = formula
    if op == "eq":
        i, j = args
        return env[i] == env[j]
    if op == "rel":
        symbol, coords = args
        return tuple(env[i] for i in coords) in model.relations[symbol]
    if op == "not":
        return not value(model, args[0], env)
    if op == "and":
        return all(value(model, child, env) for child in args)
    if op == "or":
        return any(value(model, child, env) for child in args)
    if op in ("exists", "forall"):
        instances = (value(model, args[0], (i,) + env) for i in range(model.size))
        return any(instances) if op == "exists" else all(instances)
    raise ValueError("unknown formula constructor")


def rank(formula):
    op, *args = formula
    if op in ("eq", "rel"):
        return 0
    if op in ("exists", "forall"):
        return 1 + rank(args[0])
    return max(map(rank, args), default=0)


class Game:
    def __init__(self, left, right):
        if left.arities != right.arities:
            raise ValueError("signatures differ")
        self.left = left
        self.right = right
        # Scope the memo table to this pair of models.
        self._solve = cache(self._separator)

    def solve(self, rounds, left_tuple=(), right_tuple=()):
        if (rounds < 0 or len(left_tuple) != len(right_tuple)
                or any(a not in range(self.left.size) for a in left_tuple)
                or any(b not in range(self.right.size) for b in right_tuple)):
            raise ValueError("invalid game position")
        return self._solve(rounds, tuple(left_tuple), tuple(right_tuple))

    def _separator(self, rounds, left_tuple, right_tuple):
        # None is a winning Duplicator position. All other results are formulas
        # true of left_tuple and false of right_tuple.
        k = len(left_tuple)
        for i in range(k):
            for j in range(i):
                a = left_tuple[i] == left_tuple[j]
                b = right_tuple[i] == right_tuple[j]
                if a != b:
                    atom = ("eq", i, j)
                    return atom if a else ("not", atom)
        for symbol, arity in enumerate(self.left.arities):
            for coords in product(range(k), repeat=arity):
                a = tuple(left_tuple[i] for i in coords) in self.left.relations[symbol]
                b = tuple(right_tuple[i] for i in coords) in self.right.relations[symbol]
                if a != b:
                    atom = ("rel", symbol, coords)
                    return atom if a else ("not", atom)
        if rounds == 0:
            return None
        for a in range(self.left.size):
            branches = []
            for b in range(self.right.size):
                child = self._solve(rounds - 1, (a,) + left_tuple, (b,) + right_tuple)
                if child is None:
                    break
                branches.append(child)
            else:
                return ("exists", ("and", *branches))
        for b in range(self.right.size):
            branches = []
            for a in range(self.left.size):
                child = self._solve(rounds - 1, (a,) + left_tuple, (b,) + right_tuple)
                if child is None:
                    break
                branches.append(child)
            else:
                return ("forall", ("or", *branches))
        return None

    def reply(self, side, element, rounds, left_tuple=(), right_tuple=()):
        """Return the least safe Duplicator reply from a winning position."""
        if rounds <= 0 or self.solve(rounds, left_tuple, right_tuple) is not None:
            raise ValueError("a winning position with a move remaining is required")
        if side == "left" and element in range(self.left.size):
            for b in range(self.right.size):
                if self.solve(rounds - 1, (element,) + left_tuple, (b,) + right_tuple) is None:
                    return b
        elif side == "right" and element in range(self.right.size):
            for a in range(self.left.size):
                if self.solve(rounds - 1, (a,) + left_tuple, (element,) + right_tuple) is None:
                    return a
        else:
            raise ValueError("invalid side or element")
        raise AssertionError("winning node lacks a safe reply")


def strict_order(n):
    rows = frozenset((a, b) for a in range(n) for b in range(a + 1, n))
    return Structure(n, (2,), (rows,))


def isomorphic(left, right):
    if left.size != right.size or left.arities != right.arities:
        return False
    return any(
        all({tuple(p[a] for a in row) for row in s} == t
            for s, t in zip(left.relations, right.relations))
        for p in permutations(range(left.size))
    )


def audit(game, rounds, left_tuple=(), right_tuple=()):
    phi = game.solve(rounds, left_tuple, right_tuple)
    if phi is not None:
        assert rank(phi) <= rounds
        assert value(game.left, phi, left_tuple)
        assert not value(game.right, phi, right_tuple)
    elif rounds:
        for side, size in (("left", game.left.size), ("right", game.right.size)):
            for element in range(size):
                game.reply(side, element, rounds, left_tuple, right_tuple)
    return phi is None


def regression():
    # All directed graphs (loops allowed) of sizes one and two.
    graphs = []
    for size in (1, 2):
        pairs = list(product(range(size), repeat=2))
        for mask in range(1 << len(pairs)):
            rows = frozenset(row for i, row in enumerate(pairs) if mask & (1 << i))
            graphs.append(Structure(size, (2,), (rows,)))
    for left, right in product(graphs, repeat=2):
        game = Game(left, right)
        for r in range(3):
            win = audit(game, r)
            if r >= max(left.size, right.size):
                assert win == isomorphic(left, right)
        for a, b in product(range(left.size), range(right.size)):
            audit(game, 1, (a,), (b,))
    for m, n in product(range(1, 7), repeat=2):
        game = Game(strict_order(m), strict_order(n))
        for r in range(4):
            assert audit(game, r) == (m == n or min(m, n) >= (1 << r) - 1)
    flag = Game(Structure(1, (0,), (frozenset({()}),)),
                Structure(1, (0,), (frozenset(),)))
    assert not audit(flag, 0)
    print("Passed: 324 graph pairs, pointed positions, 36 order pairs, nullary atom.")


if __name__ == "__main__":
    regression()
