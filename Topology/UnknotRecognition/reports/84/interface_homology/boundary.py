"""Conditional consequences of certified PL embedding in S^3.

Deliberately NOT a recognizer, and contains no `certified=True` escape hatch.
It computes the consequent of a theorem; a caller must supply a separately
verified source-embedding/cut ancestry before using it as geometric evidence.
"""
from dataclasses import dataclass
from .model import natural


@dataclass(frozen=True)
class BoundaryConsequences:
    hypothesis: str
    betti: tuple[int, int, int, int]
    integral_torsion: tuple
    ball_under_hypothesis: bool


def s3_boundary_consequences(boundary_components: int, total_genus: int) -> BoundaryConsequences:
    natural(boundary_components, 'boundary components', 1)
    natural(total_genus, 'total boundary genus')
    return BoundaryConsequences(
        'Connected compact locally flat PL codimension-zero submanifold of S^3; '
        'boundary counts/genera independently verified. NOT VERIFIED BY THIS FUNCTION.',
        (1, total_genus, boundary_components-1, 0), (),
        boundary_components == 1 and total_genus == 0)
