"""Checked source-braid adapter for report 11's twist macro complex.

The raw degree output is converted to the original source braid's cube
grading. A source braid may be reused after isotopy of the whole diagram,
but must never be assigned to just one factor of a connected sum.
"""
from dataclasses import replace
from time import monotonic

from .diagram import Diagram
from .scan import ScanLimit
from .twist.core import Budget, ResourceLimit, homology, runs_from_word
from .twist.preflight import basis_size, generator_basis_bound


def twist_khovanov_rank(diagram: Diagram, *, budget: Budget | None = None,
                        check_d_squared: bool = False) -> dict:
    """Exact F2 ranks of a checked braid closure, after a bounded size preflight.

    The standard Budget controls the macro construction. The exact preflight
    allows at most 4096 TL matchings and 256 strands; exhausting either guard
    raises ScanLimit, never a knot verdict. Advanced raw-run homology and
    configurable preflight routines live in fastunknot.twist.
    """
    if diagram.braid_source is None:
        raise ValueError("twist homology requires a checked source braid")
    cap = Budget() if budget is None else budget
    if not isinstance(cap, Budget):
        raise ValueError("budget must be a twist Budget")
    # Budget is mutable; revalidate caller changes without mutating their object.
    cap = replace(cap)
    start = monotonic()
    deadline = None if cap.seconds is None else start + cap.seconds

    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ResourceLimit("time budget exhausted")

    try:
        check()
        strands, word = diagram.braid_source
        runs = runs_from_word(strands, word)
        check()
        # Every macro state has a nonempty reduced vector space. Avoid forming
        # a huge product when its partial product already exceeds the ceiling.
        states = 1
        if states > cap.max_states:
            raise ResourceLimit("macro state limit exceeded")
        for run in runs:
            check()
            factor = abs(run.exponent) + 1
            if factor > cap.max_states // states:
                raise ResourceLimit("macro state limit exceeded")
            states *= factor
        # The all-I state alone contains 2^(strands-1) reduced generators.
        if strands - 1 >= cap.max_basis.bit_length():
            raise ResourceLimit("all-I basis exceeds twist basis limit")
        preflight = basis_size(strands, runs, check=check)
        preflight["macro_states"] = states
        preflight["generator_basis_upper_bound"] = generator_basis_bound(strands, runs)
        if preflight["exact_basis"] > cap.max_basis:
            raise ResourceLimit("exact preflight basis exceeds twist basis limit")
        check()
        left = None if deadline is None else max(0.0, deadline - monotonic())
        kh = homology(strands, runs, budget=replace(cap, seconds=left), check_d2=check_d_squared)
        check()
    except ResourceLimit as exc:
        raise ScanLimit(str(exc)) from exc
    if kh["components"] != 1:
        raise ArithmeticError("checked source braid changed its component count")
    if kh["stats"]["basis"] != preflight["exact_basis"]:
        raise ArithmeticError("twist preflight and assembly disagree")
    positive = sum(letter > 0 for letter in word)
    # h_macro = n_positive - h_cube. Over F2 the unreduced knot homology
    # consists of two reduced copies in each homological degree.
    by_degree = dict(sorted((positive-h, 2*d) for h, d in kh["by_degree"].items()))
    return dict(rank=2*kh["reduced_rank"], reduced_rank=kh["reduced_rank"],
                by_degree=by_degree, macro_reduced_by_degree=kh["by_degree"],
                stats=kh["stats"], preflight=preflight, backend="twist",
                grading_diagram="original checked source braid",
                source_crossings=diagram.crossings, source_strands=strands,
                d_squared_checked=kh["d_squared_checked"], seconds=monotonic()-start)

