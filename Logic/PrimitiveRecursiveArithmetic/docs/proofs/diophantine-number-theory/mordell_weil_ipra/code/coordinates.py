#!/usr/bin/env python3
"""Finite trace and coefficient extraction for certified height descent.

The elliptic interface assumes that the supplied actual points cover E(Q)/2E(Q).
It does not certify that assertion. A missed decomposition returns a failed
CoordinateResult, retaining the valid partial expansion and failure reason.
Successful results carry an exactly checked expansion in the supplied points
and one explicitly computed small-height terminal point.

All loops have displayed finite fuel. The generic implementation is also used
by the Z^r parity-descent tests, which exercise nontrivial coefficient updates.
"""

from dataclasses import dataclass
from typing import Callable, Generic, Optional, Sequence, TypeVar

from elliptic import EllipticCurve, Point, integer_height, point_text

G = TypeVar("G")


@dataclass(frozen=True)
class TraceStep(Generic[G]):
    iteration: int
    kind: str
    before: G
    after: G
    height_before: int
    height_after: int
    selected_index: Optional[int]
    active_steps: int
    scale: int
    representative_coefficients: tuple[int, ...]


@dataclass(frozen=True)
class CoordinateResult(Generic[G]):
    success: bool
    failure_reason: Optional[str]
    initial: G
    representatives: tuple[G, ...]
    representative_coefficients: tuple[int, ...]
    terminal: G
    terminal_coefficient: int
    threshold: int
    initial_height: int
    initial_excess: int
    fuel: int
    active_steps: int
    trace: tuple[TraceStep[G], ...]

    @property
    def coefficient_bound(self) -> int:
        return 2 * max(1, self.initial_excess)


def linear_combination(coefficients: Sequence[int], points: Sequence[G],
                       add: Callable[[G, G], G], mul: Callable[[int, G], G],
                       zero: G) -> G:
    if len(coefficients) != len(points):
        raise ValueError("coefficient and point lists have different lengths")
    total = zero
    for coefficient, point in zip(coefficients, points):
        total = add(total, mul(coefficient, point))
    return total


def reconstruct(result: CoordinateResult[G], add: Callable[[G, G], G],
                mul: Callable[[int, G], G], zero: G) -> G:
    """Reconstruct the original input from a full or partial expansion."""
    return add(mul(result.terminal_coefficient, result.terminal),
               linear_combination(result.representative_coefficients,
                                  result.representatives, add, mul, zero))


def extract_coordinates(
    initial: G, representatives: Sequence[G], threshold: int,
    height: Callable[[G], int],
    split: Callable[[G], Optional[tuple[int, G]]],
    add: Callable[[G, G], G], mul: Callable[[int, G], G], zero: G
) -> CoordinateResult[G]:
    """Extract using 2*h(Q)<=h(P)+threshold and P=2Q+R_i.

    Run exactly bit_length(max(h(initial)-threshold,0)) iterations, freezing
    the state when its height is small. Every active step checks both the
    algebraic equation and the height contract before updating coefficients.
    The partial identity initial=scale*current+sum(a_i*R_i) is checked after
    each successful update. These are concrete checks on a trace; they do
    not prove that split works on every possible input.
    """
    if not isinstance(threshold, int) or threshold < 0:
        raise ValueError("threshold must be a nonnegative integer")
    reps = tuple(representatives)
    if not reps:
        raise ValueError("the representative list must be nonempty")
    initial_height = height(initial)
    if not isinstance(initial_height, int) or initial_height < 0:
        raise ValueError("height must have natural-number values")
    excess = max(initial_height - threshold, 0)
    fuel = excess.bit_length()
    current, scale, active = initial, 1, 0
    coefficients = [0] * len(reps)
    trace = []
    failure = None
    for j in range(fuel):
        before, h_before = current, height(current)
        index = None
        if h_before <= threshold:
            kind = "frozen"
        else:
            answer = split(current)
            if answer is None:
                failure = "No supplied representative gives a rational decomposition of the current point."
                trace.append(TraceStep(j + 1, "missing_decomposition", before,
                                       current, h_before, h_before, None, active,
                                       scale, tuple(coefficients)))
                break
            index, child = answer
            if not isinstance(index, int) or not 0 <= index < len(reps):
                failure = "The splitting function returned an invalid representative index."
                break
            h_child = height(child)
            if not isinstance(h_child, int) or h_child < 0:
                failure = "The splitting function returned a point with invalid height."
                break
            if add(mul(2, child), reps[index]) != current:
                failure = "The proposed decomposition fails its exact group equation."
                break
            if 2 * h_child > h_before + threshold:
                failure = "The proposed decomposition fails the required height contraction."
                break
            kind = "active"
            coefficients[index] += scale
            scale *= 2
            active += 1
            current = child
        h_after = height(current)
        trace.append(TraceStep(j + 1, kind, before, current, h_before,
                               h_after, index, active, scale, tuple(coefficients)))
        if max(h_after - threshold, 0) > excess // (1 << (j + 1)):
            failure = "The computed excess violates the finite halving invariant."
            break
        expanded = add(mul(scale, current),
                       linear_combination(coefficients, reps, add, mul, zero))
        if expanded != initial:
            failure = "The accumulated coefficients fail their exact expansion invariant."
            break
    if failure is None and height(current) > threshold:
        failure = "The fixed-fuel iteration did not reach the small-height set."
    bound = 2 * max(1, excess)
    if failure is None and (scale > bound or any(a < 0 or a > bound for a in coefficients)):
        failure = "The coefficient bound failed."
    return CoordinateResult(failure is None, failure, initial, reps,
                            tuple(coefficients), current, scale, threshold,
                            initial_height, excess, fuel, active, tuple(trace))


def coordinates(curve: EllipticCurve, representatives: Sequence[Point],
                p: Point) -> CoordinateResult[Point]:
    """Elliptic specialization; quotient coverage remains a hypothesis."""
    curve._check(p)
    data = curve.descent_data(representatives)
    return extract_coordinates(
        p, representatives, data["C"], integer_height,
        lambda q: curve.division_by_representatives(q, representatives),
        curve.add, curve.mul, None)


def generator_list(curve: EllipticCurve, representatives: Sequence[Point]) -> list[Point]:
    """R followed by all points of H<=2**C; duplicates are intentionally retained."""
    data = curve.descent_data(representatives)
    return list(representatives) + curve.enumerate_points(1 << data["C"])


def coordinate_vector(curve: EllipticCurve, representatives: Sequence[Point],
                      result: CoordinateResult[Point],
                      generators: Optional[Sequence[Point]] = None) -> Optional[list[int]]:
    """Map the terminal point to its first index in the appended small list.

    A failed result returns None. A supplied generator list is checked for
    its representative prefix and terminal membership; its universal
    completeness is not asserted by this function. The default list comes
    from the exact bounded enumeration in generator_list.
    """
    if not result.success:
        return None
    reps = list(representatives)
    if tuple(reps) != result.representatives:
        raise ValueError("result and representative list do not match")
    gs = generator_list(curve, reps) if generators is None else list(generators)
    if gs[:len(reps)] != reps:
        raise ValueError("the generator list does not start with the representatives")
    for g in gs:
        curve._check(g)
    terminal_index = next((i for i in range(len(reps), len(gs))
                           if gs[i] == result.terminal), None)
    if terminal_index is None:
        raise ValueError("the appended generator list omits the terminal point")
    coefficients = list(result.representative_coefficients) + [0] * (len(gs) - len(reps))
    coefficients[terminal_index] += result.terminal_coefficient
    if linear_combination(coefficients, gs, curve.add, curve.mul, None) != result.initial:
        raise ArithmeticError("the mapped coordinate vector does not reconstruct the input")
    return coefficients


def result_metadata(result: CoordinateResult[G], encode: Callable[[G], object] = repr) -> dict:
    return {
        "success": result.success, "failure_reason": result.failure_reason,
        "initial": encode(result.initial),
        "representatives": [encode(r) for r in result.representatives],
        "representative_coefficients": list(result.representative_coefficients),
        "terminal": encode(result.terminal),
        "terminal_coefficient": result.terminal_coefficient,
        "threshold": result.threshold, "initial_height": result.initial_height,
        "initial_excess": result.initial_excess, "fuel": result.fuel,
        "active_steps": result.active_steps, "coefficient_bound": result.coefficient_bound,
        "trace": [
            {"iteration": t.iteration, "kind": t.kind,
             "before": encode(t.before), "after": encode(t.after),
             "height_before": t.height_before, "height_after": t.height_after,
             "selected_index": t.selected_index, "active_steps": t.active_steps,
             "scale": t.scale,
             "representative_coefficients": list(t.representative_coefficients)}
            for t in result.trace],
    }
