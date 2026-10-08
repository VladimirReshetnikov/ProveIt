"""Exact long-run extrapolation for the F2 twist macro complex.

This module depends on ``fastunknot.twist.core`` from the pinned ProveIt
checkout. It changes no global state and leaves the production scanner alone.
The output stores finite exceptional degrees plus at most one constant interval.
No step enumerates the selected exponent when it exceeds the proven threshold.
"""
from __future__ import annotations

from dataclasses import replace
from time import monotonic
from typing import Iterable

from fastunknot.twist.core import (
    Budget, ResourceLimit, Run, components, homology, validate_runs,
)


def _index(runs: tuple[Run, ...], run_index: int | None) -> int | None:
    if run_index is not None:
        if type(run_index) is not int or not 0 <= run_index < len(runs):
            raise ValueError('run_index must index one of the supplied runs')
        return run_index
    return max(range(len(runs)), key=lambda j: abs(runs[j].exponent),
               default=None)


def _validated_budget(budget: Budget | None) -> Budget:
    if budget is not None and not isinstance(budget, Budget):
        raise ValueError('budget must be a twist Budget')
    # Budget is mutable, so copy and revalidate its current fields.
    return Budget() if budget is None else replace(budget)


def expand_profile(profile: dict, *, max_terms: int = 100_000) -> dict[int, int]:
    """Expand the exact compressed profile, subject to an explicit term cap.

    An interval includes both endpoints. Exceptions must be disjoint from it.
    This function expands output only; homology computation never calls it.
    """
    if type(max_terms) is not int or max_terms < 0:
        raise ValueError('max_terms must be a nonnegative integer')
    points = profile['points']
    intervals = profile['intervals']
    count = len(points) + sum(v['end'] - v['start'] + 1 for v in intervals)
    if count > max_terms:
        raise ResourceLimit('expanded degree-profile term limit exceeded')
    result = dict(points)
    for interval in intervals:
        for h in range(interval['start'], interval['end'] + 1):
            if h in result:
                raise ArithmeticError('compressed profile contains overlapping pieces')
            result[h] = interval['dimension']
    return dict(sorted(result.items()))


def profile_dimension(profile: dict, degree: int) -> int:
    """Query one homological degree without expanding a plateau."""
    if type(degree) is not int:
        raise ValueError('degree must be an integer')
    answer = profile['points'].get(degree, 0)
    for interval in profile['intervals']:
        if interval['start'] <= degree <= interval['end']:
            answer += interval['dimension']
    return answer


def profile_rank(profile: dict) -> int:
    """Sum homology dimensions by integer arithmetic on compressed pieces."""
    return sum(profile['points'].values()) + sum(
        (v['end'] - v['start'] + 1) * v['dimension']
        for v in profile['intervals']
    )


def tail_homology(strands: int, runs: Iterable[Run], *,
                  run_index: int | None = None, budget: Budget | None = None,
                  check_d2: bool = False) -> dict:
    """Compute exact reduced homology with one unbounded twist run.

    Freeze all runs except the selected one. If their signed degree range is
    [a,b], write w=b-a and m0=w+2. Exponents of magnitude at most m0 are passed
    directly to the exact macro backend. For a longer exponent m, only m0 is
    assembled. In its central differential the domain and codomain both have
    dimension M, and eta=M-2*rank(F) is the repeated homology dimension.

    Returned degrees follow the existing macro backend's convention. Quantum
    grading is forgotten. Original component count is computed before returning;
    the shorter reference closure is allowed to have a different component count.
    ResourceLimit is propagated and is never a knot verdict.
    """
    start = monotonic()
    runs = validate_runs(strands, runs)
    cap = _validated_budget(budget)
    index = _index(runs, run_index)
    original_components = components(strands, runs)
    if index is None:
        baseline = homology(strands, runs, budget=cap, check_d2=check_d2)
        return {
            'reduced_rank': baseline['reduced_rank'],
            'degree_profile': {'points': baseline['by_degree'], 'intervals': []},
            'components': original_components,
            'method': 'direct-macro', 'tail_certificate': None,
            'reference': baseline,
            'seconds': monotonic() - start,
            'd_squared_checked': check_d2,
        }

    chosen = runs[index]
    m = abs(chosen.exponent)
    a = sum(r.exponent for j, r in enumerate(runs)
            if j != index and r.exponent < 0)
    b = sum(r.exponent for j, r in enumerate(runs)
            if j != index and r.exponent > 0)
    threshold = b - a + 2
    if m <= threshold:
        baseline = homology(strands, runs, budget=cap, check_d2=check_d2)
        return {
            'reduced_rank': baseline['reduced_rank'],
            'degree_profile': {'points': baseline['by_degree'], 'intervals': []},
            'components': original_components,
            'method': 'direct-macro', 'tail_certificate': None,
            'reference': baseline,
            'seconds': monotonic() - start,
            'd_squared_checked': check_d2,
        }

    sign = 1 if chosen.exponent > 0 else -1
    shortened = runs[:index] + (Run(chosen.generator, sign * threshold),) + runs[index + 1:]
    baseline = homology(strands, shortened, budget=cap, check_d2=check_d2)
    center = b + 1 if sign > 0 else a - 2
    dimension = baseline['chain_dimensions'][center]
    if baseline['chain_dimensions'][center + 1] != dimension:
        raise ArithmeticError('central chain dimensions disagree')
    matrix_rank = baseline['boundary_ranks'][center]
    slope = dimension - 2 * matrix_rank
    if slope < 0:
        raise ArithmeticError('central square-zero homology dimension is negative')
    delta = m - threshold
    points = {}
    if sign > 0:
        for h, d in baseline['by_degree'].items():
            points[h if h <= b + 1 else h + delta] = d
        plateau_start, plateau_end = b + 2, a + m - 1
    else:
        for h, d in baseline['by_degree'].items():
            points[h - delta if h <= a - 2 else h] = d
        plateau_start, plateau_end = b - m + 1, a - 2
    intervals = [] if not slope else [{
        'start': plateau_start, 'end': plateau_end, 'dimension': slope,
    }]
    profile = {'points': dict(sorted(points.items())), 'intervals': intervals}
    if plateau_end - plateau_start + 1 != delta:
        raise ArithmeticError('plateau length does not equal exponent increment')
    answer = profile_rank(profile)
    if answer != baseline['reduced_rank'] + delta * slope:
        raise ArithmeticError('affine-rank consistency check failed')
    certificate = {
        'run_index': index, 'generator': chosen.generator, 'sign': sign,
        'original_magnitude': m, 'reference_magnitude': threshold,
        'other_degree_min': a, 'other_degree_max': b,
        'central_map_degree': center, 'central_dimension': dimension,
        'central_map_rank': matrix_rank, 'plateau_dimension': slope,
        'plateau_start': plateau_start, 'plateau_end': plateau_end,
        'plateau_length': delta,
        'reference_components': baseline['components'],
        'original_components': original_components,
    }
    return {
        'reduced_rank': answer, 'degree_profile': profile,
        'components': original_components, 'method': 'exact-one-run-recurrence',
        'tail_certificate': certificate, 'reference': baseline,
        'seconds': monotonic() - start,
        # This refers to the finite reference complex. The recurrence is proved
        # algebraically; no unbuilt, enormous differential is explicitly checked.
        'd_squared_checked': check_d2,
        'd_squared_check_scope': 'finite reference complex',
    }


def tail_recognize(strands: int, runs: Iterable[Run], *,
                   run_index: int | None = None, budget: Budget | None = None,
                   check_d2: bool = False) -> dict:
    """Recognize the original one-component closure using exact reduced rank."""
    runs = validate_runs(strands, runs)
    if components(strands, runs) != 1:
        raise ValueError('unknot recognition requires a one-component braid closure')
    try:
        result = tail_homology(strands, runs, run_index=run_index,
                               budget=budget, check_d2=check_d2)
    except (ResourceLimit, MemoryError) as exc:
        return {
            'status': 'UNKNOWN', 'method': 'twist-tail-khovanov-F2',
            'reason': str(exc) or 'memory allocation failed',
            'unrestricted_quasipolynomial_guarantee': False,
        }
    return {
        'status': 'UNKNOT' if result['reduced_rank'] == 1 else 'KNOTTED',
        'method': 'twist-tail-khovanov-F2', 'homology': result,
        'unrestricted_quasipolynomial_guarantee': False,
    }
