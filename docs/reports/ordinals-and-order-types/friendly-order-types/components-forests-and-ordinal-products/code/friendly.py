"""Finite-poset engine: friendly order type, protected roots, forest certificates.

Python 3.10+, standard library only.  Relations are reflexive internally; JSON
input supplies strict generating relations (e.g. Hasse edges), whose transitive
closure is computed.  No graph-rank formula is used in the independent DP.

This module is the engine only.  The command-line front end lives in
``friendly_cli.py``; the companion module ``finite_posets.py`` provides the
second, independent finite representation used for products, heights, widths,
and the compositionality counterexample.
"""
from __future__ import annotations

from functools import lru_cache
from typing import Iterable, Iterator, Sequence


def bits(mask: int) -> Iterator[int]:
    """Yield set-bit indices in increasing order."""
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


class Poset:
    """A finite partial order on {0,...,n-1}, stored as upward-closure masks."""

    def __init__(self, upper: Sequence[int], *, validate: bool = True) -> None:
        self.upper = tuple(upper)
        self.n = len(self.upper)
        self.full = (1 << self.n) - 1
        if validate:
            for i, mask in enumerate(self.upper):
                if type(mask) is not int or mask < 0 or mask & ~self.full:
                    raise ValueError("Upper masks must be nonnegative integers on the support")
                if not mask & (1 << i):
                    raise ValueError("Relation is not reflexive")
                for j in bits(mask):
                    if i != j and self.upper[j] & (1 << i):
                        raise ValueError("Relation is not antisymmetric")
                    if self.upper[j] & ~mask:
                        raise ValueError("Relation is not transitive")
        lower = [0] * self.n
        for i, mask in enumerate(self.upper):
            for j in bits(mask):
                lower[j] |= 1 << i
        self.lower = tuple(lower)
        self.inc = tuple(self.full & ~(self.upper[i] | self.lower[i])
                         for i in range(self.n))

    @classmethod
    def from_relations(cls, n: int, relations: Iterable[Sequence[int]]) -> Poset:
        """Construct from strict generating relations, taking transitive closure."""
        if type(n) is not int or n < 0:
            raise ValueError("n must be a nonnegative integer")
        upper = [1 << i for i in range(n)]
        for edge in relations:
            if len(edge) != 2:
                raise ValueError("Each relation must have exactly two endpoints")
            i, j = edge
            if type(i) is not int or type(j) is not int or not (0 <= i < n and 0 <= j < n):
                raise ValueError("Relation endpoints must be integer labels in 0,...,n-1")
            if i == j:
                raise ValueError("Input relations must be strict")
            upper[i] |= 1 << j
        for k in range(n):
            for i in range(n):
                if upper[i] & (1 << k):
                    upper[i] |= upper[k]
        return cls(upper)

    @classmethod
    def _from_natural_lower(cls, strict_lower: tuple[int, ...]) -> Poset:
        """Internal constructor for the already-validated enumerator below."""
        n = len(strict_lower)
        upper = [1 << i for i in range(n)]
        for j, mask in enumerate(strict_lower):
            for i in bits(mask):
                upper[i] |= 1 << j
        return cls(upper, validate=False)

    def components(self, mask: int | None = None) -> list[int]:
        """Connected components of the incomparability graph induced on mask."""
        if mask is None:
            mask = self.full
        if mask < 0 or mask & ~self.full:
            raise ValueError("Invalid subset mask")
        result: list[int] = []
        while mask:
            seen = mask & -mask
            frontier = seen
            while frontier:
                bit = frontier & -frontier
                frontier ^= bit
                new = self.inc[bit.bit_length() - 1] & mask & ~seen
                seen |= new
                frontier |= new
            result.append(seen)
            mask &= ~seen
        return result

    def friendly(self) -> int:
        """The component formula: n minus the number of components."""
        return self.n - len(self.components())

    def friendly_dp(self) -> int:
        """Independent direct residual recursion; exponential worst-case cost."""
        @lru_cache(None)
        def rank(mask: int) -> int:
            best = 0
            for x in bits(mask):
                if self.inc[x] & mask:
                    best = max(best, 1 + rank(mask & ~self.upper[x]))
            return best
        return rank(self.full)

    def ordered_components(self, mask: int | None = None) -> list[int]:
        """Incomparability components in ascending ordinal-sum order."""
        comps = self.components(mask)
        # A representative's lower set meets exactly the earlier components.
        return sorted(comps, key=lambda c: sum(bool(self.lower[next(bits(c))] & d)
                                                for d in comps if d != c))

    def maximal_noncut(self, mask: int, protected: int | None = None) -> int:
        """Construct a maximal vertex whose deletion preserves connectivity.

        The input must induce a connected incomparability graph with >=2 vertices.
        An optional protected vertex must be minimal in the induced poset.
        This implements the lemma in the article, not trial deletion of all vertices.
        """
        if mask.bit_count() < 2 or len(self.components(mask)) != 1:
            raise ValueError("Expected a connected incomparability graph of size >=2")
        if protected is not None:
            if not (0 <= protected < self.n) or not mask & (1 << protected):
                raise ValueError("Protected vertex must belong to the subset")
            if self.lower[protected] & mask != (1 << protected):
                raise ValueError("Protected vertex must be minimal in the subset")
        x = next(v for v in bits(mask)
                 if v != protected and self.upper[v] & mask == (1 << v))
        remainder = mask & ~(1 << x)
        comps = self.components(remainder)
        if len(comps) == 1:
            return x
        # Find the last component by comparisons of representatives (a linear scan).
        last = comps[0]
        for comp in comps[1:]:
            a, b = next(bits(last)), next(bits(comp))
            if self.upper[a] & (1 << b):
                last = comp
        return next(v for v in bits(last) if self.upper[v] & last == (1 << v))

    def optimal_certificate(self, protected_roots: Sequence[int] | None = None) -> dict:
        """Produce an optimal sequence, explicit friends, and a spanning forest."""
        comps = self.ordered_components()
        if protected_roots is not None:
            if len(protected_roots) != len(comps) or len(set(protected_roots)) != len(comps):
                raise ValueError("Expected exactly one distinct protected root per component")
            if any(type(r) is not int or not (0 <= r < self.n) for r in protected_roots):
                raise ValueError("Invalid protected root label")
        steps: list[dict[str, int]] = []
        roots: list[int] = []
        for component in reversed(comps):
            protected = None
            if protected_roots is not None:
                candidates = [r for r in protected_roots if component & (1 << r)]
                if len(candidates) != 1:
                    raise ValueError("Each component requires one protected root")
                protected = candidates[0]
                if self.lower[protected] & component != (1 << protected):
                    raise ValueError("A protected root is not minimal in its component")
            local = component
            while local.bit_count() > 1:
                x = self.maximal_noncut(local, protected)
                y = next(bits(self.inc[x] & local))
                steps.append({"choice": x, "friend": y})
                local &= ~(1 << x)
            roots.append(next(bits(local)))
        return {"rank": len(steps), "steps": steps, "forest_roots": roots}

    def check_certificate(self, certificate: dict, *, require_optimal: bool = True) -> None:
        """Independently simulate each move and verify the claimed spanning forest.

        Raises ValueError for invalid input.  Sequence legality does not use the
        theorem; optimality additionally compares against the component count.
        """
        steps = certificate.get("steps")
        if not isinstance(steps, list):
            raise ValueError("Certificate steps must be a list")
        mask = self.full
        parent = list(range(self.n))
        def root(v: int) -> int:
            while parent[v] != v:
                parent[v] = parent[parent[v]]
                v = parent[v]
            return v
        for step in steps:
            if not isinstance(step, dict):
                raise ValueError("Each step must be an object")
            x, y = step.get("choice"), step.get("friend")
            if type(x) is not int or type(y) is not int or not (0 <= x < self.n and 0 <= y < self.n):
                raise ValueError("Invalid choice/friend labels")
            if not mask & (1 << x) or not mask & (1 << y):
                raise ValueError("Choice or friend has already been removed")
            if not self.inc[x] & (1 << y):
                raise ValueError("Named friend is comparable to the choice")
            rx, ry = root(x), root(y)
            if rx == ry:
                raise ValueError("The witness edges contain a cycle")
            parent[rx] = ry
            mask &= ~self.upper[x]
        if certificate.get("rank") != len(steps):
            raise ValueError("Claimed rank differs from sequence length")
        if require_optimal:
            if len(steps) != self.friendly():
                raise ValueError("Sequence has not reached the component upper bound")
            roots = certificate.get("forest_roots")
            if not isinstance(roots, list) or len(roots) != len(self.components()):
                raise ValueError("Expected one forest root per component")
            if any(type(r) is not int or not (0 <= r < self.n) for r in roots):
                raise ValueError("Invalid forest root label")
            if len({root(r) for r in roots}) != len(self.components()):
                raise ValueError("Forest roots do not represent distinct components")
            for comp in self.components():
                if len({root(v) for v in bits(comp)}) != 1:
                    raise ValueError("Witness forest fails to span an incomparability component")

    def has_least(self) -> bool:
        return self.n > 0 and any(u == self.full for u in self.upper)

    def has_greatest(self) -> bool:
        return self.n > 0 and any(d == self.full for d in self.lower)

    def dual(self) -> Poset:
        return Poset(self.lower, validate=False)

    def cartesian(self, other: Poset) -> Poset:
        m = other.n
        upper = []
        for a in range(self.n):
            for b in range(m):
                upper.append(sum(1 << (x * m + y)
                                 for x in bits(self.upper[a]) for y in bits(other.upper[b])))
        return Poset(upper, validate=False)

    def substitute(self, fibers: Sequence[Poset]) -> Poset:
        """Lexicographic substitution, allowing empty fibers."""
        if len(fibers) != self.n:
            raise ValueError("One fiber is required for each base element")
        offsets = [0]
        for fiber in fibers:
            offsets.append(offsets[-1] + fiber.n)
        upper: list[int] = []
        for a, fiber in enumerate(fibers):
            higher = sum(((1 << fibers[b].n) - 1) << offsets[b]
                         for b in bits(self.upper[a] & ~(1 << a)))
            for local in fiber.upper:
                upper.append(higher | (local << offsets[a]))
        return Poset(upper, validate=False)


def natural_lower_sets(n: int) -> Iterator[tuple[int, ...]]:
    """Every partial order compatible with the fixed label order, exactly once.

    strict_lower[j] lists the predecessors of j.  The predecessor set of a new
    final label must be an order ideal.  Every finite poset has a linear extension,
    so these cases represent all isomorphism types, usually more than once.
    """
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer")
    if n == 0:
        yield ()
    else:
        for lower in natural_lower_sets(n - 1):
            for subset in range(1 << (n - 1)):
                if all(lower[i] & subset == lower[i] for i in bits(subset)):
                    yield lower + (subset,)
