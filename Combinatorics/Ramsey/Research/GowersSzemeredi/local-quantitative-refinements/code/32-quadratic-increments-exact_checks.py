#!/usr/bin/env python3
"""Bounded exact diagnostics for Report 276; finite checks are not proofs.

Integer and Fraction arithmetic checks finite structural identities, rational
phase lifts, rounding and explicit constant budgets. No complex exponential,
floating-point root or numerical all-real recurrence certificate is computed.
The theorem-scale partition (minimum parent size 2**116 * L**38) is never
enumerated. Small quadratic partitions test its algebraic construction only.

Public diagnostics reject out-of-range inputs with runtime exceptions, also
under python -O. JSON output contains no timing, platform or random fields.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from math import gcd
import json
import re
import sys

MAX_NMAX = 12
DEFAULT_NMAX = 8
MAX_COVER_NMAX = 9
MAX_MODULUS = 512
MAX_ALL_STEP_MODULUS = 64
MAX_EXHAUSTIVE_ALL_STEP_LENGTH = 4
MAX_BUDGET_PARAMETER = 4096
MAX_RATIO_BITS = 1024
MAX_PHASE_INTEGER = 2**128 - 1
DIGIT_CAP = 64
PI_UPPER = Q(22, 7)  # Uses the analytic fact pi < 22/7; not a numerical proof.


class CheckFailure(RuntimeError):
    """A failed diagnostic, including when Python optimization is enabled."""


def _ensure(condition, message):
    if not condition:
        raise CheckFailure(message)


def _bounded_int(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in [{low}, {high}]")
    return value


def _parse_integer(value, name, low, high):
    if not isinstance(value, str) or not 1 <= len(value) <= DIGIT_CAP:
        raise ValueError(f"{name}: expected at most {DIGIT_CAP} ASCII digits")
    if re.fullmatch(r"[0-9]+", value) is None:
        raise ValueError(f"{name}: expected an ASCII decimal integer")
    canonical = value.lstrip("0") or "0"
    if len(canonical) > len(str(high)):
        raise ValueError(f"{name} exceeds the diagnostic cap")
    return _bounded_int(int(canonical), name, low, high)


def centered(value, n):
    """Integer representative in (-n/2,n/2], for 1 <= n <= 512."""
    _bounded_int(n, "modulus", 1, MAX_MODULUS)
    _bounded_int(value, "integer phase", -MAX_PHASE_INTEGER, MAX_PHASE_INTEGER)
    residue = value % n
    return residue-n if 2*residue > n else residue


def _subset(n, selected):
    if not isinstance(selected, (set, frozenset, tuple, list)) or len(selected) > n:
        raise ValueError("subset must be a bounded collection of residues")
    for x in selected:
        _bounded_int(x, "subset residue", 0, n-1)
    if len(set(selected)) != len(selected):
        raise ValueError("subset residues must be distinct")
    return frozenset(selected)


def _all_step_setup(n, length):
    good, bad = [], []
    good_steps = bad_steps = 0
    for step in range(n):
        is_good = n//gcd(n, step) >= length
        good_steps += is_good
        bad_steps += not is_good
        for start in range(n):
            points = tuple((start+j*step) % n for j in range(length))
            if is_good:
                _ensure(len(set(points)) == length, "good all-step copy is proper")
                good.append(sum(1 << point for point in points))
            else:
                _ensure(len(set(points)) < length, "bad all-step copy repeats")
                counts = Counter(points)
                # A multiset is represented by its nested multiplicity layers.
                # Intersecting these masks with A preserves repeated samples.
                bad.append(tuple(sum(1 << x for x,count in counts.items() if count >= level)
                                 for level in range(1, max(counts.values())+1)))
    _ensure(good_steps > 0, "at least one proper step for length at most N")
    _ensure(2*bad_steps <= length*(length-1), "bad-step union bound")
    return tuple(good), tuple(bad), good_steps, bad_steps


def _all_step_moments(n, mask, length, setup):
    good, bad, good_steps, bad_steps = setup
    cardinality = mask.bit_count()
    delta = Q(cardinality, n)
    good_sums = tuple((mask & copy).bit_count() for copy in good)
    bad_sums = tuple(sum((mask & layer).bit_count() for layer in copy) for copy in bad)
    _ensure(sum(good_sums) == cardinality*good_steps*length, "conditional good mean")
    _ensure(sum(bad_sums) == cardinality*bad_steps*length, "conditional bad mean when nonempty")
    good_variance = Q(sum(value*value for value in good_sums), n*good_steps*length*length)-delta*delta
    bad_variance = (Q(sum(value*value for value in bad_sums), n*bad_steps*length*length)-delta*delta
                    if bad_steps else Q(0))
    variance = Q(sum(value*value for value in good_sums+bad_sums), n*n*length*length)-delta*delta
    covariance_sum = Q(0)
    for difference in range(1, length):
        divisor = gcd(difference, n)
        counts = [0]*divisor
        for x in range(n):
            if mask & (1 << x):
                counts[x % divisor] += 1
        pair_mean = Q(divisor*sum(count*count for count in counts), n*n)
        covariance = pair_mean-delta*delta
        _ensure(covariance >= 0, "coset covariance is nonnegative")
        covariance_sum += (length-difference)*covariance
    coset_variance = delta*(1-delta)/length + 2*covariance_sum/(length*length)
    _ensure(variance == coset_variance, "direct all-step variance equals coset formula")
    _ensure(variance >= delta*(1-delta)/length, "all-step variance lower bound")
    b = Q(bad_steps, n)
    _ensure(variance == (1-b)*good_variance+b*bad_variance, "conditional variance mixture")
    _ensure(bad_variance <= delta*(1-delta), "bad-copy variance bound")
    h = Q(max(good_sums), length)-delta
    _ensure(good_variance <= delta*h, "proper-copy one-sided variance bound")
    lower = None
    if cardinality:
        lower = (1-delta)*(Q(1, length)-b)/(1-b)
        _ensure(h >= lower, "bad-step discard density increment")
        if n >= length**3:
            _ensure(lower >= (1-delta)/(2*length), "N >= L cubed simplified gain")
            _ensure(h >= (1-delta)/(2*length), "proper progression density increment")
    return {"mean": delta, "variance": variance, "coset_variance": coset_variance,
            "good_variance": good_variance, "bad_variance": bad_variance if bad_steps else None,
            "good_mean": delta, "bad_mean": delta if bad_steps else None,
            "good_steps": good_steps, "bad_steps": bad_steps, "bad_fraction": b,
            "maximum_proper_gain": h, "discard_gain_lower_bound": lower,
            "simplified_gain_applies": bool(cardinality and n >= length**3)}


def all_step_moments(n, selected, length):
    """Exact all-step multiset moments, with proper and bad copies separated.

    The density-gain conclusion requires nonempty A; the moment identities also
    cover the empty set. Conditional bad moments are None if there are no bad
    steps. No least-prime-factor restriction is imposed.
    """
    _bounded_int(n, "all-step modulus", 2, MAX_ALL_STEP_MODULUS)
    _bounded_int(length, "all-step length", 1, n)
    selected = _subset(n, selected)
    mask = sum(1 << x for x in selected)
    return _all_step_moments(n, mask, length, _all_step_setup(n, length))


def all_step_checks(nmax, full=False):
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    if type(full) is not bool:
        raise ValueError("full must be boolean")
    instances = simplified = 0
    for n in range(2, nmax+1):
        for length in range(1, min(n, MAX_EXHAUSTIVE_ALL_STEP_LENGTH)+1):
            setup = _all_step_setup(n, length)
            for mask in range(1 << n):
                result = _all_step_moments(n, mask, length, setup)
                instances += 1
                simplified += result["simplified_gain_applies"]
    rows = []
    parameters = ((27, 3), (64, 4)) if full else ((27, 3),)
    for n,length in parameters:
        families = ({0}, set(range(0, n, 2)), set(range(0, n, length)),
                    set(range(n//3)), set(range(n)))
        for selected in families:
            result = all_step_moments(n, selected, length)
            _ensure(result["simplified_gain_applies"], "larger selected case meets N >= L cubed")
            rows.append({"modulus": n, "length": length, "subset_size": len(selected),
                         "bad_steps": result["bad_steps"], "variance": str(result["variance"]),
                         "maximum_proper_gain": str(result["maximum_proper_gain"]),
                         "discard_gain_lower_bound": str(result["discard_gain_lower_bound"])})
    return {"exhaustive_nmax": nmax, "exhaustive_length_cap": MAX_EXHAUSTIVE_ALL_STEP_LENGTH,
            "exhaustive_subset_length_instances": instances,
            "nonempty_simplified_gain_instances": simplified, "larger_selected_cases": rows,
            "scope": "all a,d uniform, including d=0; X is multiset density; gain requires nonempty A"}


def cover_mass_checks(nmax):
    """Exhaust all A subset U, using a deterministic disjoint block partition.

    The blocks need not be APs: positive-mass extraction is purely algebraic.
    Separate phase checks certify the progression partitions used in the proof.
    """
    _bounded_int(nmax, "cover nmax", 2, MAX_COVER_NMAX)
    pairs = nontrivial_partitions = 0
    for n in range(2, nmax+1):
        for union_mask in range(1 << n):
            union = tuple(x for x in range(n) if union_mask & (1 << x))
            a_mask = union_mask
            while True:
                cardinality = a_mask.bit_count()
                delta, tau = Q(cardinality, n), Q(len(union), n)
                centered_values = tuple(n*((a_mask >> x) & 1)-cardinality for x in union)
                mu = Q(sum(map(abs, centered_values)), n*n)
                _ensure(mu == delta*(1+tau-2*delta), "exact normalized cover absolute mass")
                b = 1-delta
                _ensure(mu <= 2*delta*b <= 2*tau*b <= 2*b, "cover absolute-mass chain")
                total = Q(sum(centered_values), n)
                _ensure(total == delta*n*(1-tau) and total >= 0,
                       "nonnegative cover mass from A subset U")
                width = 1+(cardinality+len(union)+n) % 3
                blocks = tuple(centered_values[start:start+width]
                               for start in range(0, len(union), width))
                block_sums = tuple(map(sum, blocks))
                absolute = sum(map(abs, block_sums))
                positive = sum(max(value, 0) for value in block_sums)
                _ensure(2*positive == absolute+sum(block_sums), "positive-mass exact decomposition")
                _ensure(2*positive >= absolute, "positive mass is at least half absolute mass")
                if positive:
                    densities = tuple(Q(value, n*len(block))
                                      for value,block in zip(block_sums, blocks))
                    _ensure(max(densities) >= Q(positive, n*len(union)),
                           "positive-cell weighted averaging")
                    _ensure(max(densities) >= Q(positive, n*n),
                           "ambient-N positive-cell lower bound")
                    nontrivial_partitions += 1
                pairs += 1
                if a_mask == 0:
                    break
                a_mask = (a_mask-1) & union_mask
    return {"nmax": nmax, "all_A_subset_U_pairs": pairs,
            "positive_mass_partitions": nontrivial_partitions,
            "mu_definition": "N^(-1) sum_U |1_A-delta|",
            "mu_identity": "delta*(1+tau-2*delta)",
            "normalized_signed_mass": "delta*(1-tau)"}


def dirichlet_step(n, increment, bound):
    """Deterministically minimize centered norm among 1,...,bound."""
    _bounded_int(n, "modulus", 1, MAX_MODULUS)
    _bounded_int(increment, "increment", 0, MAX_MODULUS**2)
    _bounded_int(bound, "Dirichlet bound", 1, MAX_MODULUS)
    q = min(range(1, bound+1), key=lambda q: (abs(centered(q*increment, n)), q))
    epsilon = Q(centered(q*increment, n), n)
    _ensure(abs(epsilon) <= Q(1, bound+1), "circle-gap Dirichlet bound")
    return q, epsilon


def _chunks(chain, length):
    count, remainder = divmod(len(chain), length)
    _ensure(count >= 1, "chunkable chain")
    return tuple(tuple(chain[i*length:(i+1)*length]) for i in range(count-1)) + (
        tuple(chain[(count-1)*length:count*length+remainder]),)


def _parent(n, start, step, size):
    _bounded_int(n, "modulus", 1, MAX_MODULUS)
    _bounded_int(start, "start", 0, n-1)
    _bounded_int(step, "step", 0, n-1)
    _bounded_int(size, "parent length", 1, n)
    if size > n//gcd(n, step):
        raise ValueError("parent parameterization must be proper")
    return tuple((start+j*step) % n for j in range(size))


def phase_refinement(n, start, step, size, coefficient, offset, length):
    parent = _parent(n, start, step, size)
    _bounded_int(coefficient, "coefficient", 0, n-1)
    _bounded_int(offset, "offset", 0, n-1)
    _bounded_int(length, "cell minimum length", 1, size)
    bound = size//length
    q, epsilon = dirichlet_step(n, coefficient*step, bound)
    cells = tuple(cell for residue in range(q)
                  for cell in _chunks(tuple(range(residue, size, q)), length))
    _ensure(sorted(j for cell in cells for j in cell) == list(range(size)),
           "disjoint exact parent-index partition")
    phase_cells = []
    for indices in cells:
        values = tuple(parent[j] for j in indices)
        count = len(values)
        _ensure(length <= count <= 2*length-1, "phase cell lengths")
        _ensure(len(set(values)) == count, "phase cells proper by restriction")
        _ensure(all((y-x) % n == q*step % n for x,y in zip(values, values[1:])),
               "modular arithmetic progression cells")
        initial = -Q(coefficient*values[0]+offset, n)
        midpoint = initial-epsilon*Q(count-1, 2)
        radius = abs(epsilon)*Q(count-1, 2)
        _ensure(radius <= Q(length-1, bound+1), "reduced-lift radius bound")
        _ensure(radius < Q(length*length, size), "strict rational phase radius")
        for j,x in enumerate(values):
            actual = -Q(coefficient*x+offset, n)
            lift = initial-epsilon*j
            _ensure((actual-lift).denominator == 1, "phase agrees modulo integers")
            _ensure(abs(lift-midpoint) <= radius, "reduced midpoint controls every lift")
        phase_cells.append({"indices": indices, "points": values,
                            "midpoint_turns": midpoint, "radius_turns": radius})
    return {"q": q, "epsilon": epsilon, "bound": bound, "cells": tuple(phase_cells)}


def phase_checks(nmax):
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    instances = cells = nonunit = 0
    for n in range(2, nmax+1):
        # Exhaust every effective rational increment t/N, parent length and
        # target length using step one. Additional image tests exercise actual
        # nonunit steps, translations and affine offsets.
        for size in range(1, n+1):
            for length in range(1, size+1):
                for t in range(n):
                    result = phase_refinement(n, 0, 1, size, t, 0, length)
                    instances += 1
                    cells += len(result["cells"])
        for step in range(n):
            size = n//gcd(n, step)
            for length in sorted({1, size, max(1, size//2)}):
                result = phase_refinement(n, n-1, step, size, n-1, n-1, length)
                instances += 1
                cells += len(result["cells"])
                nonunit += gcd(n, step) > 1
    return {"refinements": instances, "cells": cells, "nonunit_step_instances": nonunit,
            "radius_units": "turns; analytic chord/arc inequality is not numerically tested"}


def midpoint_regression():
    # A proper two-point parent in Z/6Z: a=3, d=2, so raw q*a*d/N=1.
    # Both endpoint phases are 1. The raw midpoint is -1, whereas reducing
    # the increment first gives epsilon=0 and midpoint 1 exactly.
    result = phase_refinement(6, 0, 2, 2, 3, 0, 2)
    cell = result["cells"][0]
    raw_increment = Q(result["q"]*3*2, 6)
    raw_midpoint = -raw_increment*Q(len(cell["points"])-1, 2)
    reduced_midpoint = cell["midpoint_turns"]
    _ensure(result["epsilon"] == 0, "regression reduced increment is zero")
    _ensure(reduced_midpoint % 1 == 0 and raw_midpoint % 1 == Q(1, 2),
           "unreduced midpoint has exactly the opposite unit phase")
    return {"modulus": 6, "parent_points": list(cell["points"]), "coefficient": 3,
            "raw_increment_turns": str(raw_increment), "reduced_increment_turns": "0",
            "reduced_midpoint_mod_one": str(reduced_midpoint % 1),
            "unreduced_midpoint_mod_one": str(raw_midpoint % 1),
            "endpoint_phase": "+1", "reduced_midpoint_phase": "+1",
            "unreduced_midpoint_phase": "-1", "unreduced_chord_error": 2,
            "reduced_chord_error": 0}



def quadratic_refinement(n, start, step, size, a, b, c, p, coarse_length, length):
    """Construct a bounded two-stage index partition and exact phase lifts.

    All residues and lengths are bounded by 512. The supplied p is a positive
    trial step, NOT a witness supplied by a numerical all-real recurrence test.
    Each p-chain has at least coarse_length points. It is cut into chunks with
    coarse_length <= m <= 2*coarse_length-1; each chunk is refined affinely into
    lengths length,...,2*length-1. Returned radii are in turns, not chord lengths.
    This tests the construction even when the theorem's small-error assumption
    is false. A small toy instance does not instantiate its enormous size bound.
    """
    parent = _parent(n, start, step, size)
    for value, name in ((a, "quadratic coefficient"), (b, "linear coefficient"),
                        (c, "constant coefficient")):
        _bounded_int(value, name, 0, n-1)
    _bounded_int(length, "cell minimum length", 1, size)
    _bounded_int(coarse_length, "coarse minimum length", length, size)
    _bounded_int(p, "trial recurrence step", 1, size//coarse_length)
    quadratic_raw = Q(a*step*step*p*p, n)
    epsilon = Q(centered(a*step*step*p*p, n), n)
    _ensure((quadratic_raw-epsilon).denominator == 1, "integer quadratic term removed")
    coarse_chunks = tuple(chunk for residue in range(p)
                          for chunk in _chunks(tuple(range(residue, size, p)), coarse_length))
    output = []
    maximum_radius = Q(0)
    for chunk in coarse_chunks:
        j0, m = chunk[0], len(chunk)
        x0 = start+j0*step
        ell_numerator = (2*a*x0*step+b*step)*p
        constant_numerator = a*x0*x0+b*x0+c
        bound = m//length
        q, linear_epsilon = dirichlet_step(n, ell_numerator % n, bound)
        affine_cells = tuple(cell for residue in range(q)
                             for cell in _chunks(tuple(range(residue, m, q)), length))
        curvature_radius = abs(epsilon)*(m-1)**2
        for local in affine_cells:
            t0, count = local[0], len(local)
            indices = tuple(j0+p*t for t in local)
            points = tuple(parent[j] for j in indices)
            initial = -Q(constant_numerator+ell_numerator*t0, n)
            midpoint = initial-linear_epsilon*Q(count-1, 2)
            affine_radius = abs(linear_epsilon)*Q(count-1, 2)
            radius = curvature_radius+affine_radius
            maximum_radius = max(maximum_radius, radius)
            _ensure(length <= count <= 2*length-1, "quadratic cell length range")
            _ensure(len(set(points)) == count, "quadratic image cell is proper")
            _ensure(all((y-x) % n == step*p*q % n for x,y in zip(points, points[1:])),
                    "quadratic cells have modular arithmetic-progression steps")
            _ensure(affine_radius <= Q(length-1, bound+1), "affine midpoint lift radius")
            _ensure(affine_radius < Q(length*length, m), "affine rational radius budget")
            for index, (t, point) in enumerate(zip(local, points)):
                actual = -Q(a*point*point+b*point+c, n)
                affine_lift = initial-linear_epsilon*index
                reduced_lift = affine_lift-epsilon*t*t
                _ensure((actual-reduced_lift).denominator == 1,
                        "quadratic phase identity modulo integers, including wraps")
                _ensure(abs(reduced_lift-midpoint) <= radius,
                        "reduced quadratic plus affine midpoint error")
            output.append({"indices": indices, "points": points, "coarse_size": m,
                           "affine_step": q, "linear_epsilon": linear_epsilon,
                           "midpoint_turns": midpoint, "curvature_radius_turns": curvature_radius,
                           "affine_radius_turns": affine_radius, "radius_turns": radius})
    _ensure(sorted(j for cell in output for j in cell["indices"]) == list(range(size)),
            "quadratic cells partition parent indices exactly once")
    return {"p": p, "raw_quadratic_coefficient": quadratic_raw,
            "quadratic_epsilon": epsilon, "coarse_chunks": len(coarse_chunks),
            "cells": tuple(output), "maximum_radius_turns": maximum_radius,
            "scope": "bounded structural partition; theorem size hypothesis is not imposed"}


def quadratic_checks(nmax):
    """Exhaust bounded rational coefficient pairs; selected nonunit image tests."""
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    instances = cells = nonunit = zero_curvature = 0
    for n in range(2, nmax+1):
        for a in range(n):
            for b in range(n):
                for length in range(1, min(3, n)+1):
                    coarse_length = max(length, (n+1)//2)
                    for p in range(1, n//coarse_length+1):
                        result = quadratic_refinement(n, n-1, 1, n, a, b, (a+2*b) % n,
                                                      p, coarse_length, length)
                        instances += 1
                        cells += len(result["cells"])
                        zero_curvature += result["quadratic_epsilon"] == 0
        for step in range(n):
            if gcd(n, step) == 1:
                continue
            size = n//gcd(n, step)
            for length in sorted({1, min(2, size)}):
                coarse_length = max(length, (size+1)//2)
                for p in range(1, size//coarse_length+1):
                    result = quadratic_refinement(n, n-1, step, size, n-1, n-1, n-1,
                                                  p, coarse_length, length)
                    instances += 1
                    nonunit += 1
                    cells += len(result["cells"])
                    zero_curvature += result["quadratic_epsilon"] == 0
    toy = quadratic_refinement(128, 127, 1, 128, 2, 0, 0, 8, 8, 2)
    _ensure(toy["maximum_radius_turns"] == 0, "nontrivial exact-constant toy cells")
    _ensure(all(len(cell["points"]) >= 2 for cell in toy["cells"]), "non-singleton toy cells")
    return {"nmax": nmax, "refinements": instances, "cells": cells,
            "nonunit_step_instances": nonunit, "zero_reduced_curvature_instances": zero_curvature,
            "coverage": "all a,b modulo N; start N-1, step 1, size N; L=1..min(3,N); "
                        "H=max(L,ceil(N/2)); p=1..floor(N/H); c=(a+2b) mod N, plus nonunit steps",
            "exact_constant_toy": {"modulus": 128, "a": 2, "b": 0, "c": 0,
                                   "start": 127, "step": 1, "size": 128, "p": 8,
                                   "coarse_length": 8, "length": 2,
                                   "cells": len(toy["cells"]), "maximum_radius_turns": "0"},
            "theorem_scale_partition_enumerated": False,
            "error_units": "exact rational turns; chord/arc estimate is analytic, not numerically tested"}


def curvature_regression():
    """An integer quadratic coefficient must be removed before bounding lifts."""
    result = quadratic_refinement(6, 0, 2, 3, 3, 0, 0, 1, 3, 3)
    _ensure(result["raw_quadratic_coefficient"] == 2, "raw curvature regression coefficient")
    _ensure(result["quadratic_epsilon"] == 0, "integer curvature reduces to zero")
    _ensure(result["maximum_radius_turns"] == 0, "reduced curvature error is zero")
    raw_radius = result["raw_quadratic_coefficient"]*(3-1)**2
    _ensure(raw_radius == 8, "unreduced curvature lift loses eight full turns")
    return {"modulus": 6, "parent_points": [0, 2, 4], "quadratic_coefficient": 3,
            "raw_quadratic_coefficient_turns": "2", "reduced_quadratic_coefficient_turns": "0",
            "unreduced_lift_radius_turns": str(raw_radius), "reduced_lift_radius_turns": "0",
            "explanation": "all three phases equal 1; integer multiples of t^2 change no unit phase"}


def recurrence_witness(n, coefficient, r):
    """Find an exact rational witness for coefficient/n by searching p <= n.

    This bounded grid diagnostic is not an algorithm certifying all real theta.
    Rationality gives the trivial fallback p=n. The theorem's unconditional
    upper bound is 1024*r**5; no unconditional R**4 bound is claimed.
    """
    _bounded_int(n, "rational phase denominator", 1, MAX_MODULUS)
    _bounded_int(coefficient, "rational phase numerator", 0, n-1)
    _bounded_int(r, "recurrence parameter", 2, MAX_BUDGET_PARAMETER)
    p = next(p for p in range(1, n+1) if abs(centered(coefficient*p*p, n))*r < n)
    norm = Q(abs(centered(coefficient*p*p, n)), n)
    _ensure(norm < Q(1, r), "strict rational-grid recurrence")
    _ensure(p <= 1024*r**5, "rational witness respects unconditional theorem bound")
    return {"p": p, "norm": norm, "unconditional_bound": 1024*r**5,
            "searched_at_most": n}


def recurrence_checks(nmax):
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    cases = 0
    maximum = 0
    for n in range(1, nmax+1):
        for coefficient in range(n):
            for r in range(2, 13):
                result = recurrence_witness(n, coefficient, r)
                cases += 1
                maximum = max(maximum, result["p"])
    strict = recurrence_witness(2, 1, 2)
    _ensure(strict["p"] == 2, "equality at distance 1/R is not a strict recurrence")
    return {"rational_grid_cases": cases, "denominator_max": nmax,
            "r_values": list(range(2, 13)), "largest_first_witness": maximum,
            "strict_boundary_regression": {"theta": "1/2", "r": 2, "p": 2},
            "unconditional_theorem_bound": "1024*R^5",
            "conditional_contradiction_witness_bound": "p < 512*R^4, only under the no-return hypothesis",
            "all_real_certificate": False}


def budget_constants(length, r=2):
    """Exact finite budget evaluation; L,R are integers in 2..4096.

    Neither astronomical parent indices nor phases at that scale are generated.
    The logarithm estimate and pi bounds are analytic inputs from the proof.
    """
    _bounded_int(length, "budget length", 2, MAX_BUDGET_PARAMETER)
    _bounded_int(r, "recurrence budget parameter", 2, MAX_BUDGET_PARAMETER)
    h = 64*length**3
    refinement_r = 256*length*h*h
    t = 1024*refinement_r**5
    parent_minimum = t*h
    _ensure(refinement_r == 2**20*length**7, "refinement R identity")
    _ensure(t == 2**110*length**35, "refinement T identity")
    _ensure(parent_minimum == 2**116*length**38, "quadratic parent-size identity")
    curvature_turns = Q(4*h*h, refinement_r)
    affine_turns = Q(length*length, h)
    _ensure(curvature_turns == affine_turns == Q(1, 64*length), "two equal phase budgets")
    chord_upper = 2*PI_UPPER*(curvature_turns+affine_turns)
    _ensure(chord_upper < Q(1, 4*length), "rational majorant for combined chord error")
    _ensure(3*17**39 > 2**158, "exponent-39 coefficient dominates quadratic parent threshold")
    _ensure(17**39*16 >= 55*2**156, "Bernoulli lower bound exact integer check")
    # If log(2T) < 8R, this polynomial comparison bounds the logarithm term.
    recurrence_t = 1024*r**5
    _ensure(recurrence_t >= 4096*r**3, "R>=2 polynomial recurrence budget")
    _ensure(recurrence_t > 256*r*r*(8*r), "budget assuming analytic logarithm bound")
    maximum_conditional_p = 2*(4*r*r)*(64*r*r-1)
    _ensure(maximum_conditional_p < 512*r**4 < recurrence_t,
            "conditional contradiction witness lies in the excluded range")
    _ensure(Q(maximum_conditional_p, recurrence_t) < Q(1, 2*r),
            "conditional witness has strict recurrence error budget")
    return {"length": length, "H": h, "R": refinement_r, "T": t,
            "minimum_parent_size": parent_minimum,
            "curvature_radius_majorant_turns": curvature_turns,
            "affine_radius_majorant_turns": affine_turns,
            "combined_chord_majorant_using_pi_lt_22_over_7": chord_upper,
            "recurrence_r": r, "unconditional_recurrence_T": recurrence_t,
            "maximum_conditional_contradiction_p": maximum_conditional_p}


def target_length(n, m):
    """Return ceil((n/m)**(1/39)/17), with exact integer comparisons.

    Inputs satisfy 1 <= m <= n and each has at most 1024 bits. No floating-point
    root is used; these inputs are ratios, not a request to enumerate residues.
    """
    if type(n) is not int or type(m) is not int or not 1 <= m <= n:
        raise ValueError("target ratio requires integers 1 <= m <= n")
    if max(n.bit_length(), m.bit_length()) > MAX_RATIO_BITS:
        raise ValueError("target ratio inputs exceed the 1024-bit diagnostic cap")
    low, high = 1, 1 << ((n.bit_length()+38)//39)
    while low < high:
        middle = (low+high)//2
        if m*(17*middle)**39 >= n:
            high = middle
        else:
            low = middle+1
    length = low
    _ensure(m*(17*length)**39 >= n, "ceiling upper defining inequality")
    _ensure(length == 1 or m*(17*(length-1))**39 < n, "ceiling lower defining inequality")
    return length


def constant_and_rounding_checks():
    lengths = (2, 3, 4, 8, 16, 64, 256, 4096)
    rows = []
    for length in lengths:
        result = budget_constants(length, length)
        rows.append({"length": length, "minimum_parent_size": str(result["minimum_parent_size"]),
                     "parent_size_decimal_digits": len(str(result["minimum_parent_size"])),
                     "H": str(result["H"]), "R": str(result["R"]), "T": str(result["T"]),
                     "combined_chord_majorant": str(result["combined_chord_majorant_using_pi_lt_22_over_7"])})
    recurrence_parameters = tuple(range(2, 65))+(128, 1024, 4096)
    for r in recurrence_parameters:
        budget_constants(2, r)
    rounding_cases = 0
    for k in tuple(range(1, 33))+(64, 256, 4096):
        for m in (1, 2, 17):
            for offset in (-1, 0, 1):
                n = m*(17*k)**39+offset
                length = target_length(n, m)
                _ensure(length == (k+1 if offset == 1 else k), "exact-root boundary ceiling")
                if length >= 2:
                    _ensure(n*2**39 > m*(17*length)**39, "strict L<2x rounding inequality")
                    _ensure(n > m*length**3, "variance size threshold from exponent 39")
                    _ensure(3*n > 8*m*length*(2**116*length**38),
                            "large-correlation parent-size budget after rounding")
                rounding_cases += 1
    _ensure(target_length(1, 1) == 1, "effective singleton length at S=1")
    _ensure(target_length(17**39, 1) == 1, "singleton endpoint included")
    _ensure(Q(25, 39) > Q(1, 2), "old-exponent comparison exponent")
    _ensure(8 > Q(17, 8)**2, "sqrt(8) exceeds 17/8 without evaluating a square root")
    _ensure(2**2*2**9 == 2048, "degree-two source polynomial constant")
    return {"budget_rows": rows, "recurrence_parameter_samples": list(recurrence_parameters),
            "rounding_boundary_cases": rounding_cases+2,
            "rounding_method": "integer bisection comparing m*(17*L)^39 with n",
            "exact_coefficient_checks": {"3*17^39": str(3*17**39), "2^158": str(2**158),
                                         "source_K_degree_two": 2048},
            "analytic_inputs_not_numerically_proved": ["pi < 22/7", "log(2*1024*R^5) < 8R for R>=2",
                                                       "monotonicity of positive real powers"],
            "theorem_scale_partition_enumerated": False}


def assembly_checks(nmax):
    """Finite exact checks of the two-branch scalar gain/error implications."""
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    low = high = 0
    for n in range(2, nmax+1):
        for cardinality in range(1, n):
            delta = Q(cardinality, n)
            b = 1-delta
            for union_size in range(cardinality, n+1):
                tau = Q(union_size, n)
                mu = delta*(1+tau-2*delta)
                for numerator in (1, 2, 3, 4):
                    alpha = mu*Q(numerator, 4)
                    _ensure(alpha/3 < b, "singleton density gain")
                    for length in range(2, 9):
                        if alpha <= 3*b/(2*length):
                            _ensure(b/(2*length) >= alpha/3, "low-correlation gain implication")
                            low += 1
                        else:
                            _ensure(tau > Q(3, 4*length), "high-correlation cover density")
                            _ensure(mu/(4*length) <= b/(2*length) < alpha/3,
                                    "high-correlation normalized error budget")
                            high += 1
    return {"low_branch_scalar_cases": low, "high_branch_scalar_cases": high,
            "scope": "exact scalar implications; no complex-valued correlation premise is tested"}


def quadratic_difference_counts(n, coefficient, length):
    """Exact formal expansion of a quadratic sum's squared modulus.

    Return residue histograms for sum over i,j of e(a*(i^2-j^2)/N), without
    evaluating e. Compare the direct ordered pairs with the diagonal and two
    orientations of each positive difference u. N<=512 and length<=64.
    """
    _bounded_int(n, "differencing denominator", 1, MAX_MODULUS)
    _bounded_int(coefficient, "differencing numerator", 0, n-1)
    _bounded_int(length, "differencing sum length", 1, 64)
    direct = [0]*n
    grouped = [0]*n
    grouped[0] = length
    for i in range(1, length+1):
        for j in range(1, length+1):
            direct[coefficient*(i*i-j*j) % n] += 1
    for difference in range(1, length):
        for j in range(1, length-difference+1):
            residue = coefficient*(2*j*difference+difference*difference) % n
            grouped[residue] += 1
            grouped[-residue % n] += 1
    _ensure(direct == grouped, "exact quadratic differencing phase histogram")
    _ensure(sum(direct) == length*length, "all ordered quadratic phase pairs counted")
    _ensure(all(direct[r] == direct[-r % n] for r in range(n)), "conjugate-pair symmetry")
    return {"direct_counts": tuple(direct), "difference_counts": tuple(grouped),
            "ordered_pairs": length*length}


def quadratic_differencing_checks(nmax):
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    instances = 0
    for n in range(2, nmax+1):
        for coefficient in range(n):
            for length in range(1, n+1):
                quadratic_difference_counts(n, coefficient, length)
                instances += 1
    return {"phase_histogram_identities": instances, "nmax": nmax,
            "coverage": "every coefficient modulo N and every sum length 1..N",
            "scope": "formal residue counts only; quadratic complex sums are not numerically evaluated"}


def coset_pair_moment(n, selected, difference):
    """Direct pair expectation versus coset-density formula, for N<=64.

    The averaging is over all x,d in Z/NZ, including d=0. The difference is
    1,...,N-1; no primality or invertibility assumption is used.
    """
    _bounded_int(n, "coset modulus", 2, MAX_ALL_STEP_MODULUS)
    _bounded_int(difference, "index difference", 1, n-1)
    selected = _subset(n, selected)
    divisor = gcd(difference, n)
    counts = tuple(sum(x in selected for x in range(residue, n, divisor))
                   for residue in range(divisor))
    direct_count = sum((x+difference*d) % n in selected for x in selected for d in range(n))
    direct = Q(direct_count, n*n)
    coset = Q(divisor*sum(count*count for count in counts), n*n)
    delta = Q(len(selected), n)
    _ensure(direct == coset, "direct ordered pair count equals coset formula")
    _ensure(coset >= delta*delta, "all-moduli pair covariance is nonnegative")
    return {"pair_expectation": direct, "coset_expectation": coset,
            "covariance": coset-delta*delta, "coset_count": divisor,
            "subgroup_size": n//divisor, "coset_subset_counts": counts}


def coset_and_bad_step_checks(nmax):
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    pair_cases = nonunit_pairs = kernel_cases = bad_cases = 0
    for n in range(2, nmax+1):
        for difference in range(1, n):
            kernel = {d for d in range(n) if difference*d % n == 0}
            _ensure(len(kernel) == gcd(difference, n) <= difference, "multiplication kernel size")
            kernel_cases += 1
            for mask in range(1 << n):
                selected = frozenset(x for x in range(n) if mask & (1 << x))
                coset_pair_moment(n, selected, difference)
                pair_cases += 1
                nonunit_pairs += gcd(difference, n) > 1
        for length in range(1, n+1):
            union = {d for d in range(n) if any(j*d % n == 0 for j in range(1, length))}
            by_order = {d for d in range(n) if n//gcd(n, d) < length}
            _ensure(union == by_order, "bad directions equal union of multiplication kernels")
            _ensure(2*len(union) <= length*(length-1), "bad-direction union bound")
            if n >= length**3:
                _ensure(Q(len(union), n) < Q(1, 2*length), "strict simplified bad-fraction bound")
            bad_cases += 1
    return {"exhaustive_nmax": nmax, "all_subset_difference_cases": pair_cases,
            "nonunit_difference_cases": nonunit_pairs, "kernel_size_cases": kernel_cases,
            "bad_direction_length_cases": bad_cases,
            "scope": "all subsets and every nonzero index difference; all lengths 1..N for bad directions"}


def run_checks(nmax=None, full=False):
    """Run deterministic bounded diagnostics (default nmax=8, full nmax=12)."""
    if type(full) is not bool:
        raise ValueError("full must be boolean")
    if nmax is None:
        nmax = MAX_NMAX if full else DEFAULT_NMAX
    _bounded_int(nmax, "nmax", 2, MAX_NMAX)
    return {"report": 276, "arithmetic": "integers and exact fractions only",
            "finite_diagnostics_not_proofs": True,
            "parameters": {"nmax": nmax, "full": full, "hard_nmax_cap": MAX_NMAX},
            "all_step_moments": all_step_checks(nmax, full),
            "coset_and_bad_steps": coset_and_bad_step_checks(nmax),
            "cover_mass": cover_mass_checks(min(nmax, MAX_COVER_NMAX)),
            "affine_phase_partitions": phase_checks(nmax),
            "quadratic_phase_partitions": quadratic_checks(nmax),
            "quadratic_differencing": quadratic_differencing_checks(nmax),
            "midpoint_regression": midpoint_regression(),
            "curvature_regression": curvature_regression(),
            "rational_recurrence_samples": recurrence_checks(nmax),
            "constant_and_rounding_budgets": constant_and_rounding_checks(),
            "scalar_assembly": assembly_checks(nmax),
            "limitations": ["Finite checks establish only the displayed bounded identities and regressions.",
                            "No floating-point complex exponential, root, trigonometric or logarithm check is used.",
                            "No all-real recurrence or density-increment theorem is proved by this program.",
                            "The enormous theorem-scale partitions are never enumerated.",
                            "The unconditional recurrence bound is 1024*R^5; the R^4 witness is conditional on contradiction.",
                            "No Lean verification, global Ramsey/Szemeredi improvement or priority claim is made."]}


def main(argv=None):
    """CLI: --nmax 2..12 and/or --full; write deterministic sorted JSON."""
    if argv is None:
        argv = sys.argv[1:]
    if not isinstance(argv, (tuple, list)) or len(argv) > 3 or any(
            not isinstance(value, str) or len(value) > DIGIT_CAP for value in argv):
        raise ValueError("CLI accepts at most three arguments of at most 64 characters")
    parser = argparse.ArgumentParser(description=__doc__)
    def nmax_value(value):
        try:
            return _parse_integer(value, "nmax", 2, MAX_NMAX)
        except ValueError as exc:
            raise argparse.ArgumentTypeError(str(exc)) from exc
    parser.add_argument("--nmax", type=nmax_value, default=None,
                        help="maximum exhaustive modulus, 2..12; default 8, or 12 with --full")
    parser.add_argument("--full", action="store_true",
                        help="default to nmax=12 and add five selected N=64, L=4 all-step cases")
    args = parser.parse_args(argv)
    print(json.dumps(run_checks(args.nmax, args.full), sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
