"""Complete exact recognition, with an exponential—not quasipolynomial—bound."""
from __future__ import annotations

from .determinant import knot_determinant
from .diagram import PlanarDiagram
from .khovanov import ReducedComplex, ResourceLimit
from .reduction import simplify


def recognize(diagram: PlanarDiagram, *, reduce: bool = True, determinant: bool = True,
              max_resolutions: int | None = None, max_basis: int | None = None,
              check_d_squared: bool = False) -> dict:
    """Decide a classical knot, or return UNKNOWN if an optional resource cap fires.

    With both caps None the mathematical algorithm is total. The only general
    worst-case bound claimed for this implementation is 2**O(n) bit operations.
    It does NOT implement Lackenby's quasipolynomial geometric algorithm.
    """
    if not isinstance(diagram, PlanarDiagram):
        raise TypeError("Expected a validated PlanarDiagram.")
    for name, cap in (("max_resolutions", max_resolutions), ("max_basis", max_basis)):
        if cap is not None and (type(cap) is not int or cap < 1):
            raise ValueError(f"{name} must be a positive integer or None.")
    original = diagram
    diagram, trace = simplify(diagram) if reduce else (diagram, ())
    result = {
        "status": "UNKNOWN", "is_unknot": None,
        "implementation": "exact reduced-Khovanov baseline",
        "quasipolynomial_guarantee": False,
        "general_worst_case": "2^{O(n)} bit operations; exponential memory",
        "input_crossings": original.n, "remaining_crossings": diagram.n,
        "normalized_input": original.to_json(), "reduced_diagram": diagram.to_json(),
        "reduction_trace": [move.to_json() for move in trace],
    }
    if not diagram.n:
        result.update(status="UNKNOT", is_unknot=True, method="Reidemeister reduction",
                      explanation="The trace reduces the input to one crossing-free circle.")
        return result
    if determinant:
        value = knot_determinant(diagram)
        result["determinant"] = value
        if value != 1:
            result.update(status="NONTRIVIAL", is_unknot=False, method="Fox determinant",
                          explanation="The unknot has determinant one; this knot does not.")
            return result
    try:
        complex_ = ReducedComplex(diagram, max_resolutions=max_resolutions, max_basis=max_basis)
        homology = complex_.compute(check_d_squared=check_d_squared)
    except ResourceLimit as exc:
        result.update(method="resource cap", explanation=str(exc))
        return result
    if homology.total_rank < 1:
        raise ArithmeticError("A classical knot cannot have zero reduced Khovanov rank.")
    is_unknot = homology.total_rank == 1
    result.update(status="UNKNOT" if is_unknot else "NONTRIVIAL", is_unknot=is_unknot,
                  method="reduced Khovanov homology over F2", khovanov=homology.to_json(),
                  explanation="A classical knot is trivial iff its total reduced F2 rank is one.")
    return result
