"""Exact-rational reference algorithms for the continuous-framework report.

These programs execute finite observations.  They are not a proof checker,
and running them is not a substitute for the human or Lean proofs.
Only Python's standard library is required.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from typing import Callable, Mapping, Sequence


def eps(k: int) -> F:
    if k < 0:
        raise ValueError("precision must be nonnegative")
    return F(1, 2**k)


def clip(x: F, lo: F, hi: F) -> F:
    if lo > hi:
        raise ValueError("empty clipping interval")
    return max(lo, min(hi, x))


def grid(d: int, m: int) -> tuple[tuple[F, ...], ...]:
    if d < 1 or m < 0:
        raise ValueError("positive dimension and nonnegative mesh index required")
    n = 2**m
    return tuple(product((F(j, n) for j in range(n + 1)), repeat=d))


def sup_distance(x: Sequence[F], y: Sequence[F]) -> F:
    if len(x) != len(y) or not x:
        raise ValueError("nonempty tuples of equal length required")
    return max(abs(a - b) for a, b in zip(x, y))


def nearest_multiple(x: F, step: F) -> F:
    if step <= 0:
        raise ValueError("positive quantization step required")
    y = x / step + F(1, 2)
    return step * (y.numerator // y.denominator)


@dataclass(frozen=True)
class Envelope:
    points: tuple[tuple[F, ...], ...]
    values: tuple[F, ...]
    bound: F
    lipschitz: F

    def __post_init__(self) -> None:
        if not self.points or len(self.points) != len(self.values):
            raise ValueError("a nonempty table with matching length is required")
        if self.bound <= 0 or self.lipschitz < 0:
            raise ValueError("invalid range or continuity bound")
        d = len(self.points[0])
        if d < 1 or any(len(p) != d for p in self.points):
            raise ValueError("inconsistent point arities")

    def __call__(self, x: tuple[F, ...]) -> F:
        value = min(q + self.lipschitz * sup_distance(x, a)
                    for a, q in zip(self.points, self.values))
        return clip(value, -self.bound, self.bound)


def select_envelope(evaluate: Callable[[tuple[F, ...], int], F],
                    k: int, dimension: int = 1,
                    bound: int = 1, lipschitz: F = F(1),
                    exponent_bound: int = 0) -> tuple[Envelope, dict]:
    """Select one center using only the finitely many required samples.

    The CALLER supplies the sample accuracy and Lipschitz contracts.
    This function does not infer or test their universal validity.
    """
    if k < 0 or bound < 1 or exponent_bound < 0:
        raise ValueError("invalid precision or bounds")
    if not 0 <= lipschitz <= 2**exponent_bound:
        raise ValueError("the Lipschitz exponent bound is invalid")
    delta = eps(k + 2)
    m = k + 3 + exponent_bound
    points = grid(dimension, m)
    values = tuple(clip(nearest_multiple(evaluate(p, k + 3), delta),
                        F(-bound), F(bound)) for p in points)
    center = Envelope(points, values, F(bound), lipschitz)
    base = 2 * bound * 2**(k + 2) + 1
    # Report the exponent rather than allocating an enormous integer catalog.
    metadata = {"precision": k, "mesh_index": m, "sample_precision": k + 3,
                "queries": len(points), "catalog_base": base,
                "catalog_exponent": len(points),
                "proved_radius": str(delta + 2 * lipschitz * eps(m))}
    return center, metadata


def function_distance(evaluate_f: Callable[[tuple[F, ...]], F],
                      evaluate_g: Callable[[tuple[F, ...]], F],
                      dimension: int, mesh_index: int,
                      lipschitz: F, sample_error: F = F(0)) -> tuple[F, F]:
    """Return the finite supremum score and its proven error allowance."""
    if lipschitz < 0 or sample_error < 0:
        raise ValueError("nonnegative bounds required")
    value = max(abs(evaluate_f(p) - evaluate_g(p))
                for p in grid(dimension, mesh_index))
    return value, 2 * sample_error + 2 * lipschitz * eps(mesh_index)


# Formula tuples use de Bruijn indices: a newly bound variable is index zero.
# atom: ('atom', name, (indices...)); const: ('const', Fraction)
# connectives: ('min'/'max', p, q), ('not', p), ('inf'/'sup', p)
def evaluate_formula(formula: tuple, carrier: Sequence[F],
                     atoms: Mapping[str, Callable[..., F]],
                     environment: tuple[F, ...] = ()) -> F:
    if not carrier:
        raise ValueError("quantified sorts must be nonempty")
    tag = formula[0]
    if tag == "atom":
        value = atoms[formula[1]](*(environment[i] for i in formula[2]))
        if not 0 <= value <= 1:
            raise ValueError("atomic score lies outside [0,1]")
        return value
    if tag == "const":
        value = F(formula[1])
        if not 0 <= value <= 1:
            raise ValueError("formula constant lies outside [0,1]")
        return value
    if tag in ("min", "max"):
        values = [evaluate_formula(f, carrier, atoms, environment)
                  for f in formula[1:]]
        return (min if tag == "min" else max)(values)
    if tag == "not":
        return 1 - evaluate_formula(formula[1], carrier, atoms, environment)
    if tag in ("inf", "sup"):
        values = [evaluate_formula(formula[1], carrier, atoms, (x,) + environment)
                  for x in carrier]
        return (min if tag == "inf" else max)(values)
    raise ValueError(f"unknown formula constructor {tag!r}")


def tent(x: F) -> F:
    return min(x, 1 - x)


def anchored(f: Callable[[F], F]) -> Callable[[F], F]:
    return lambda x: clip(f(x), -tent(x), tent(x))


def left_sum(f: Callable[[F], F], n: int) -> F:
    if n < 1:
        raise ValueError("positive number of cells required")
    return sum((f(F(j, n)) for j in range(n)), F(0)) / n


def power_series_cutoffs(M: F, R: F, rho: F, k: int) -> dict:
    """Cutoffs from the proved geometric and derivative-tail majorants."""
    if not M > 0 or not 0 < rho < R or k < 0:
        raise ValueError("positive majorant and strict inner radius required")
    theta = rho / R
    sigma = (1 + theta) / 2
    u = theta / sigma
    b0 = M / (1 - theta)
    b1 = M / (R * (1 - u)**2 * (1 - sigma))

    def cutoff(t: F, B: F) -> tuple[int, int, int]:
        hrat = 1 / (1 - t)
        H = -(-hrat.numerator // hrat.denominator)
        # A bounded doubling routine; bit length supplies a safe finite bound.
        b = next(j for j in range(B.numerator.bit_length() + 1) if B <= 2**j)
        return H * (k + b + 1), H, b

    n0, h0, e0 = cutoff(theta, b0)
    n1, h1, e1 = cutoff(sigma, b1)
    return {"value_cutoff": n0, "derivative_cutoff": n1,
            "value_tail_bound": b0 * theta**(n0 + 1),
            "derivative_tail_bound": b1 * sigma**n1,
            "remainder_constant": M / (R**2 * (1 - theta)**3),
            "value_H": h0, "value_b": e0,
            "derivative_H": h1, "derivative_b": e1}
