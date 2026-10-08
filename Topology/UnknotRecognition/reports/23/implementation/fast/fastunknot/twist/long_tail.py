"""Exact finite-cap evaluation of one long twist over F_2.

This layer uses the verified twist macro complex already in fastunknot.  It
forgets the quantum grading, exactly as that backend does.  It does not replace
a long twist by a short braid: its output is the homology of the ORIGINAL
exponent, reconstructed from two boundary pieces and a constant interior.

For a chosen exponent of absolute value m, let L be the expanded crossing
count outside that run.  Once m >= L+2, one computation at m0=L+2 suffices.
All intervals in the compact profile have inclusive integer endpoints.
"""
from __future__ import annotations

from time import monotonic

from fastunknot.twist.core import (
    Budget, ResourceLimit, Run, _Meter, _rank, build_complex, components,
    validate_runs, verify_d_squared,
)


def _matrix_square_is_zero(columns, meter):
    """Check A^2=0 on the exact, canonically identified full slices."""
    size = len(columns)
    for column in columns:
        meter.check()
        if column.bit_length() > size:
            raise ArithmeticError("interior differential is not square")
        image = 0
        rest = column
        while rest:
            low = rest & -rest
            image ^= columns[low.bit_length() - 1]
            rest ^= low
            meter.xor()
        if image:
            raise ArithmeticError("interior differential does not square to zero")


def profile_rank(profile):
    return sum(dim for _, dim in profile["points"]) + sum(
        (piece["last"] - piece["first"] + 1) * piece["dimension"]
        for piece in profile["constant_intervals"]
    )


def degree_dimension(profile, degree):
    """Query a possibly enormous graded profile without expanding its tail."""
    if type(degree) is not int:
        raise ValueError("degree must be an integer")
    answer = sum(dim for h, dim in profile["points"] if h == degree)
    for piece in profile["constant_intervals"]:
        if piece["first"] <= degree <= piece["last"]:
            answer += piece["dimension"]
    return answer


def materialize_profile(profile, *, max_degrees=10000):
    """Return the ordinary nonzero degree dictionary, with an output guard."""
    if type(max_degrees) is not int or max_degrees < 0:
        raise ValueError("max_degrees must be a nonnegative integer")
    count = len(profile["points"]) + sum(
        piece["last"] - piece["first"] + 1
        for piece in profile["constant_intervals"]
    )
    if count > max_degrees:
        raise ResourceLimit("expanded homology output exceeds max_degrees")
    answer = dict(profile["points"])
    for piece in profile["constant_intervals"]:
        for h in range(piece["first"], piece["last"] + 1):
            if h in answer:
                raise ArithmeticError("compact profile pieces overlap")
            answer[h] = piece["dimension"]
    return dict(sorted(answer.items()))


def tail_homology(strands, runs, *, selected=None, budget=None, check_d2=False,
                  check_interior_square=True):
    """Exact reduced homology, with a finite-cap long-twist optimization.

    The selected run is zero-based.  The default chooses a longest run;
    no eligible run means the ordinary finite macro computation.  Resource
    ceilings apply to the capped computation and shared verification/rank
    work.  They do not reject the original exponent merely because it is
    large.  Bit complexity still depends on the original input/output sizes.
    """
    start = monotonic()
    runs = validate_runs(strands, runs)
    if selected is None:
        selected = max(range(len(runs)), key=lambda j: abs(runs[j].exponent),
                       default=None)
    elif type(selected) is not int or not 0 <= selected < len(runs):
        raise ValueError("selected must be a valid zero-based run index")
    meter = _Meter(budget or Budget())
    meter.check()
    crossing_count = sum(abs(run.exponent) for run in runs)
    magnitude = 0 if selected is None else abs(runs[selected].exponent)
    context_crossings = crossing_count - magnitude
    cap = context_crossings + 2
    eligible = selected is not None and magnitude >= cap
    sign = 1 if selected is None or runs[selected].exponent > 0 else -1
    capped_runs = list(runs)
    if eligible:
        capped_runs[selected] = Run(runs[selected].generator, sign * cap)
    complex_ = build_complex(strands, capped_runs, meter=meter)
    if check_d2:
        verify_d_squared(complex_, meter)
    ranks = {h: _rank(columns, meter)
             for h, columns in complex_.columns.items()}
    betti = {h: dim - ranks.get(h - 1, 0) - ranks.get(h, 0)
             for h, dim in complex_.dimensions.items()}
    if any(dim < 0 for dim in betti.values()):
        raise ArithmeticError("negative homology dimension")
    betti = {h: dim for h, dim in sorted(betti.items()) if dim}
    profile = {"points": [[h, dim] for h, dim in betti.items()],
               "constant_intervals": []}
    calibration = None
    if eligible:
        # Oriented coordinate q=sign*h makes the selected contribution +k.
        alpha = sum(min(0, sign * run.exponent)
                    for j, run in enumerate(runs) if j != selected)
        beta = sum(max(0, sign * run.exponent)
                   for j, run in enumerate(runs) if j != selected)
        if beta - alpha != context_crossings:
            raise ArithmeticError("context degree span mismatch")
        # At cap=L+2 the two full q-slices are beta+1 and beta+2.
        # The cochain differential increases h, including when sign=-1.
        source_degree = beta + 1 if sign > 0 else -(beta + 2)
        target_degree = source_degree + 1
        width = complex_.dimensions[source_degree]
        if width != complex_.dimensions[target_degree]:
            raise ArithmeticError("interior slices differ in dimension")
        if check_interior_square:
            _matrix_square_is_zero(complex_.columns[source_degree], meter)
        interior_rank = ranks[source_degree]
        interior_betti = width - 2 * interior_rank
        if interior_betti < 0:
            raise ArithmeticError("negative interior homology dimension")
        one_slice_rank = sum(betti.values()) - interior_betti
        if one_slice_rank < 1:
            raise ArithmeticError("one-full-slice rank violates the nonzero Euler bound")
        extra = magnitude - cap
        profile["points"] = sorted(
            [h if sign * h <= beta + 1 else h + sign * extra, dim]
            for h, dim in betti.items()
        )
        if extra and interior_betti:
            first_q, last_q = beta + 2, magnitude + alpha - 1
            first_h, last_h = sorted((sign * first_q, sign * last_q))
            profile["constant_intervals"] = [{
                "first": first_h, "last": last_h,
                "dimension": interior_betti,
            }]
        calibration = {
            "selected_run": selected, "sign": sign,
            "context_crossings": context_crossings,
            "context_oriented_degree_min": alpha,
            "context_oriented_degree_max": beta,
            "cap_magnitude": cap, "original_magnitude": magnitude,
            "interior_source_degree": source_degree,
            "interior_dimension": width, "interior_boundary_rank": interior_rank,
            "interior_betti": interior_betti, "inserted_slices": extra,
            "cap_reduced_rank": sum(betti.values()),
            "one_full_slice_magnitude": cap - 1,
            "one_full_slice_reduced_rank": one_slice_rank,
            "cap_by_degree": betti,
            "interior_square_checked": bool(check_interior_square),
        }
        expected_rank = sum(betti.values()) + extra * interior_betti
        if profile_rank(profile) != expected_rank:
            raise ArithmeticError("compact profile and affine rank disagree")
    meter.check()
    return {
        "reduced_rank": profile_rank(profile), "compact_by_degree": profile,
        "components": components(strands, runs),
        "method": "finite-cap-twist-khovanov-F2",
        "grading": "normalized macro homological degree; quantum grading forgotten",
        "tail_eligible": eligible,
        "tail_compressed": bool(eligible and magnitude > cap),
        "calibration": calibration,
        "stats": {**complex_.stats,
                  "original_crossings": crossing_count,
                  "built_crossings": sum(abs(run.exponent) for run in capped_runs),
                  "elimination_and_check_xors": meter.xors},
        "seconds": monotonic() - start,
        "d_squared_checked": bool(check_d2),
        "unrestricted_quasipolynomial_guarantee": False,
    }


def tail_recognize(strands, runs, **kwargs):
    """Decide one-component closures only, with explicit resource semantics."""
    runs = validate_runs(strands, runs)
    if components(strands, runs) != 1:
        raise ValueError("unknot recognition requires a one-component closure")
    try:
        result = tail_homology(strands, runs, **kwargs)
    except (ResourceLimit, MemoryError) as exc:
        return {"status": "UNKNOWN", "method": "finite-cap-twist-khovanov-F2",
                "reason": str(exc) or "memory allocation failed",
                "unrestricted_quasipolynomial_guarantee": False}
    return {"status": "UNKNOT" if result["reduced_rank"] == 1 else "KNOTTED",
            "method": result["method"], "homology": result,
            "unrestricted_quasipolynomial_guarantee": False}


def dominant_run_obstruction(strands, runs, *, selected=None):
    """Return a replayable KNOTTED certificate if m >= L+2, otherwise None.

    This is a consequence of the finite-cap theorem, not an experimental
    extrapolation.  For a context admitting a knot closure, the affine slope
    is a positive odd integer.  The affine TOTAL-rank law begins already at
    L+1, whose single full slice is sufficient for the rank sum argument.
    The two-sided graded profile still uses the L+2 cap.
    """
    runs = validate_runs(strands, runs)
    if selected is None:
        selected = max(range(len(runs)), key=lambda j: abs(runs[j].exponent),
                       default=None)
    elif type(selected) is not int or not 0 <= selected < len(runs):
        raise ValueError("selected must be a valid zero-based run index")
    if selected is None or components(strands, runs) != 1:
        return None
    magnitude = abs(runs[selected].exponent)
    context_crossings = sum(abs(run.exponent)
                            for j, run in enumerate(runs) if j != selected)
    if magnitude < context_crossings + 2:
        return None
    extra = magnitude - context_crossings - 1
    lower_bound = extra + 1 + (extra & 1)
    return {
        "status": "KNOTTED", "method": "dominant-twist-run",
        "certificate": {
            "kind": "dominant-twist-run-v1", "strands": strands,
            "run_count": len(runs), "selected_run": selected,
            "generator": runs[selected].generator,
            "signed_exponent": runs[selected].exponent,
            "context_crossings": context_crossings,
            "one_component_checked": True,
            "reduced_F2_rank_lower_bound": lower_bound,
        },
        "unrestricted_quasipolynomial_guarantee": False,
    }


def verify_dominant_run_certificate(strands, runs, certificate):
    """Replay the local numeric and permutation premises; reject tampering."""
    if not isinstance(certificate, dict):
        raise ValueError("certificate must be a dictionary")
    if certificate.get("kind") != "dominant-twist-run-v1":
        raise ValueError("unknown dominance certificate")
    for key in ("strands", "run_count", "selected_run", "generator",
                "signed_exponent", "context_crossings", "reduced_F2_rank_lower_bound"):
        if type(certificate.get(key)) is not int:
            raise ValueError("certificate numeric fields must be integers")
    if certificate.get("one_component_checked") is not True:
        raise ValueError("certificate must assert the verified knot premise")
    selected = certificate.get("selected_run")
    if type(selected) is not int:
        raise ValueError("certificate has no valid selected run")
    actual = dominant_run_obstruction(strands, runs, selected=selected)
    if actual is None or actual["certificate"] != certificate:
        raise ValueError("dominance certificate does not replay")
    return True


# Descriptive aliases used by the integration adapter.
dominant_twist_certificate = dominant_run_obstruction
verify_dominant_twist_certificate = verify_dominant_run_certificate
