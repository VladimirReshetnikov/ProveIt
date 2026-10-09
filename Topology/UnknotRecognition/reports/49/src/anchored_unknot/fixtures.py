"""Explicitly algebraic capacity fixtures, not knot diagrams."""
from __future__ import annotations
from .grammar import Arena, Source


def power_chain(rank: int, exponent: int, residual: str = 'zero') -> Source:
    """<x_1,...,x_r | x_i^q x_(i+1)^(-1)> is Z, with optional residual."""
    if rank < 2 or exponent == 0:
        raise ValueError("rank >= 2 and nonzero exponent required")
    a = Arena()
    roots = [a.concat(a.signed_power(i, exponent), a.letter(-(i + 1))) for i in range(1, rank)]
    if residual == 'zero':
        # A retained, unreduced relator that is already a word identity.
        roots.append(a.word((1, -1, rank, -rank)))
    elif residual == 'nonzero':
        roots.append(a.letter(1))
    elif residual != 'none':
        raise ValueError("residual mode")
    return Source.from_arena(a, roots, range(1, rank + 1))


def power_star(rank: int, exponent: int, duplicate: bool = False) -> Source:
    a = Arena()
    roots = []
    for child in range(2, rank + 1):
        root = a.concat(a.signed_power(1, exponent), a.letter(-child))
        roots.append(root)
        if duplicate:
            roots.append(root)
    roots.append(a.word((1, -1)))
    return Source.from_arena(a, roots, range(1, rank + 1))


def signed_tree(parents: list[int], powers: list[int], duplicates: bool = True) -> Source:
    """Node i+2 has a smaller positive parent parents[i]."""
    if len(parents) != len(powers):
        raise ValueError("length mismatch")
    a, roots = Arena(), []
    for child, (parent, power) in enumerate(zip(parents, powers), 2):
        if not 1 <= parent < child or not power:
            raise ValueError("not a nonzero-power increasing tree")
        root = a.concat(a.signed_power(parent, power), a.letter(-child))
        roots.append(root)
        if duplicates:
            roots.append(root)
    return Source.from_arena(a, roots, range(1, len(parents) + 2))


def christoffel(p: int, q: int, a: int = 1, b: int = 2) -> tuple[int, ...]:
    """Lower mechanical path, with p occurrences of a and q of b."""
    if p < 1 or q < 1:
        raise ValueError("positive counts required")
    n = p + q
    # Exactly p steps cross an integer threshold; the path is a Christoffel
    # representative when gcd(p,q)=1. This is an explicit small-fixture helper.
    return tuple(a if ((i + 1) * p) // n > (i * p) // n else b for i in range(n))
