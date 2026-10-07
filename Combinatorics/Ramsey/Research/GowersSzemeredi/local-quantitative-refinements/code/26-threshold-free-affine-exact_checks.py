#!/usr/bin/env python3
"""Bounded exact diagnostics for Report 275; finite checks are not proofs.

Only integer and Fraction arithmetic is used. In particular, rational phase
lifts are checked instead of numerical exponentials or floating-point roots.
The diagnostics do not test arbitrary correlation hypotheses, prove the density
increment theorem, certify Lean code, or close the Section 16 interface.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from math import gcd, isqrt, prod
import json
import re

MAX_NMAX = 12
MAX_COVER_NMAX = 9
DEFAULT_NMAX = 8
MAX_MODULUS = 512
MAX_MOMENT_MODULUS = 16
MAX_ALL_STEP_MODULUS = 64
MAX_EXHAUSTIVE_ALL_STEP_LENGTH = 4
MAX_DIMENSION = 4
DIGIT_CAP = 64


class CheckFailure(RuntimeError):
    """A failed diagnostic, including when Python optimization is enabled."""


def ensure(condition, message):
    if not condition:
        raise CheckFailure(message)


def bounded_int(value, name, low, high):
    if type(value) is not int or not low <= value <= high:
        raise ValueError(f"{name} must be an integer in [{low}, {high}]")
    return value


def parse_integer(value, name, low, high):
    if not isinstance(value, str) or not 1 <= len(value) <= DIGIT_CAP:
        raise ValueError(f"{name}: expected at most {DIGIT_CAP} ASCII digits")
    if re.fullmatch(r"[0-9]+", value) is None:
        raise ValueError(f"{name}: expected an ASCII decimal integer")
    canonical = value.lstrip("0") or "0"
    if len(canonical) > len(str(high)):
        raise ValueError(f"{name} exceeds the diagnostic cap")
    return bounded_int(int(canonical), name, low, high)


def least_prime_factor(n):
    bounded_int(n, "modulus", 2, MAX_MODULUS)
    return next((d for d in range(2, isqrt(n)+1) if n % d == 0), n)


def centered(value, n):
    """Canonical integer in (-N/2,N/2], with positive half-period tie."""
    bounded_int(n, "modulus", 1, MAX_MODULUS)
    bounded_int(value, "integer phase", -MAX_MODULUS**3, MAX_MODULUS**3)
    residue = value % n
    return residue-n if 2*residue > n else residue


def _subset(n, selected):
    if not isinstance(selected, (set, frozenset, tuple, list)) or len(selected) > n:
        raise ValueError("subset must be a bounded collection of residues")
    for x in selected:
        bounded_int(x, "subset residue", 0, n-1)
    if len(set(selected)) != len(selected):
        raise ValueError("subset residues must be distinct")
    return frozenset(selected)


def pair_counts(n, length, j, k):
    """Counts ordered image pairs; no unit-difference assumption is imposed."""
    bounded_int(n, "moment modulus", 2, MAX_MOMENT_MODULUS)
    bounded_int(length, "length", 1, n)
    bounded_int(j, "first index", 0, length-1)
    bounded_int(k, "second index", 0, length-1)
    if j == k:
        raise ValueError("distinct indices required")
    return Counter(((a+j*d) % n, (a+k*d) % n)
                   for a in range(n) for d in range(1, n))


def ensemble_moments(n, selected, length):
    """Exact moments over all starts and nonzero steps, including nonproper copies.

    Allowing length > spf demonstrates why the exact nonzero-step variance
    identity needs its index restriction; the all-step argument removes that
    restriction from the main theorem.
    """
    bounded_int(n, "moment modulus", 2, MAX_MOMENT_MODULUS)
    bounded_int(length, "length", 1, n)
    selected = _subset(n, selected)
    sums = []
    proper = 0
    for a in range(n):
        for d in range(1, n):
            points = tuple((a+j*d) % n for j in range(length))
            proper += len(set(points)) == length
            sums.append(sum(x in selected for x in points))
    count = n*(n-1)
    mean = Q(sum(sums), count*length)
    variance = Q(sum(s*s for s in sums), count*length*length)-mean*mean
    return {"mean": mean, "variance": variance, "maximum": Q(max(sums), length),
            "proper_copies": proper, "copies": count}


def variance_checks(nmax):
    bounded_int(nmax, "nmax", 2, MAX_NMAX)
    subsets = index_pairs = copies = 0
    rows = []
    for n in range(2, nmax+1):
        spf = least_prime_factor(n)
        for length in range(1, spf+1):
            for j in range(length):
                for k in range(j+1, length):
                    pairs = pair_counts(n, length, j, k)
                    ensure(len(pairs) == n*(n-1), "full ordered-distinct-pair support")
                    ensure(all(x != y and c == 1 for (x,y), c in pairs.items()),
                           "unit-difference pair bijection")
                    index_pairs += 1
            masks = []
            for a in range(n):
                for d in range(1, n):
                    points = tuple((a+j*d) % n for j in range(length))
                    ensure(len(set(points)) == length, "capped affine copy is proper")
                    masks.append(sum(1 << x for x in points))
            copies += len(masks)
            for mask in range(1 << n):
                cardinality = mask.bit_count()
                sums = tuple((mask & copy).bit_count() for copy in masks)
                # The diagonal term is L(N-1)|A|. Each ordered distinct pair
                # contributes once for each ordered pair of distinct indices.
                square_from_pairs = (length*(n-1)*cardinality
                                     + length*(length-1)*cardinality*(cardinality-1))
                ensure(sum(sums) == length*(n-1)*cardinality, "first moment count")
                ensure(sum(s*s for s in sums) == square_from_pairs,
                       "direct second moment equals pair-count second moment")
                delta = Q(cardinality, n)
                variance = Q(square_from_pairs, n*(n-1)*length*length)-delta*delta
                formula = delta*(1-delta)*Q(n-length, length*(n-1))
                ensure(variance == formula, "exact affine-copy variance")
                h = Q(max(sums), length)-delta
                ensure(variance <= delta*h, "one-sided moment inequality")
                if delta:
                    ensure(h >= (1-delta)*Q(n-length, length*(n-1)),
                           "variance-to-density lower bound")
                subsets += 1
        rows.append({"modulus": n, "least_prime_factor": spf,
                     "checked_lengths": list(range(1, spf+1))})
    return {"subset_length_instances": subsets, "index_pair_bijections": index_pairs,
            "affine_copies_across_lengths": copies, "coverage": rows}




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
                ensure(len(set(points)) == length, "good all-step copy is proper")
                good.append(sum(1 << point for point in points))
            else:
                ensure(len(set(points)) < length, "bad all-step copy repeats")
                counts = Counter(points)
                # A multiset is represented by its nested multiplicity layers.
                # Intersecting these masks with A preserves repeated samples.
                bad.append(tuple(sum(1 << x for x,count in counts.items() if count >= level)
                                 for level in range(1, max(counts.values())+1)))
    ensure(good_steps > 0, "at least one proper step for length at most N")
    ensure(2*bad_steps <= length*(length-1), "bad-step union bound")
    return tuple(good), tuple(bad), good_steps, bad_steps


def _all_step_moments(n, mask, length, setup):
    good, bad, good_steps, bad_steps = setup
    cardinality = mask.bit_count()
    delta = Q(cardinality, n)
    good_sums = tuple((mask & copy).bit_count() for copy in good)
    bad_sums = tuple(sum((mask & layer).bit_count() for layer in copy) for copy in bad)
    ensure(sum(good_sums) == cardinality*good_steps*length, "conditional good mean")
    ensure(sum(bad_sums) == cardinality*bad_steps*length, "conditional bad mean when nonempty")
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
        ensure(covariance >= 0, "coset covariance is nonnegative")
        covariance_sum += (length-difference)*covariance
    coset_variance = delta*(1-delta)/length + 2*covariance_sum/(length*length)
    ensure(variance == coset_variance, "direct all-step variance equals coset formula")
    ensure(variance >= delta*(1-delta)/length, "all-step variance lower bound")
    b = Q(bad_steps, n)
    ensure(variance == (1-b)*good_variance+b*bad_variance, "conditional variance mixture")
    ensure(bad_variance <= delta*(1-delta), "bad-copy variance bound")
    h = Q(max(good_sums), length)-delta
    ensure(good_variance <= delta*h, "proper-copy one-sided variance bound")
    lower = None
    if cardinality:
        lower = (1-delta)*(Q(1, length)-b)/(1-b)
        ensure(h >= lower, "bad-step discard density increment")
        if n >= length**3:
            ensure(lower >= (1-delta)/(2*length), "N >= L cubed simplified gain")
            ensure(h >= (1-delta)/(2*length), "proper progression density increment")
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
    bounded_int(n, "all-step modulus", 2, MAX_ALL_STEP_MODULUS)
    bounded_int(length, "all-step length", 1, n)
    selected = _subset(n, selected)
    mask = sum(1 << x for x in selected)
    return _all_step_moments(n, mask, length, _all_step_setup(n, length))


def all_step_checks(nmax, full=False):
    bounded_int(nmax, "nmax", 2, MAX_NMAX)
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
            ensure(result["simplified_gain_applies"], "larger selected case meets N >= L cubed")
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
    bounded_int(nmax, "cover nmax", 2, MAX_COVER_NMAX)
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
                ensure(mu == delta*(1+tau-2*delta), "exact normalized cover absolute mass")
                total = Q(sum(centered_values), n)
                ensure(total == delta*n*(1-tau) and total >= 0,
                       "nonnegative cover mass from A subset U")
                width = 1+(cardinality+len(union)+n) % 3
                blocks = tuple(centered_values[start:start+width]
                               for start in range(0, len(union), width))
                block_sums = tuple(map(sum, blocks))
                absolute = sum(map(abs, block_sums))
                positive = sum(max(value, 0) for value in block_sums)
                ensure(2*positive == absolute+sum(block_sums), "positive-mass exact decomposition")
                ensure(2*positive >= absolute, "positive mass is at least half absolute mass")
                if positive:
                    densities = tuple(Q(value, n*len(block))
                                      for value,block in zip(block_sums, blocks))
                    ensure(max(densities) >= Q(positive, n*len(union)),
                           "positive-cell weighted averaging")
                    ensure(max(densities) >= Q(positive, n*n),
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


def composite_cap_regression():
    moments = ensemble_moments(4, {0, 2}, 3)
    claimed_without_cap = Q(1, 2)*Q(1, 2)*Q(4-3, 3*(4-1))
    ensure(moments["variance"] == Q(11, 108), "composite regression variance")
    ensure(moments["variance"] != claimed_without_cap, "uncapped formula is false")
    ensure(moments["proper_copies"] < moments["copies"], "nonproper uncapped copies exist")
    pairs = pair_counts(4, 3, 0, 2)
    ensure(any(x == y for x,y in pairs), "nonunit index difference creates diagonal pairs")
    return {"modulus": 4, "length": 3, "subset": [0, 2],
            "actual_variance": str(moments["variance"]),
            "incorrect_uncapped_formula": str(claimed_without_cap),
            "proper_copies": moments["proper_copies"], "copies": moments["copies"]}


def dirichlet_step(n, increment, bound):
    """Deterministically minimize centered norm among 1,...,bound."""
    bounded_int(n, "modulus", 1, MAX_MODULUS)
    bounded_int(increment, "increment", 0, MAX_MODULUS**2)
    bounded_int(bound, "Dirichlet bound", 1, MAX_MODULUS)
    q = min(range(1, bound+1), key=lambda q: (abs(centered(q*increment, n)), q))
    epsilon = Q(centered(q*increment, n), n)
    ensure(abs(epsilon) <= Q(1, bound+1), "circle-gap Dirichlet bound")
    return q, epsilon


def _chunks(chain, length):
    count, remainder = divmod(len(chain), length)
    ensure(count >= 1, "chunkable chain")
    return tuple(tuple(chain[i*length:(i+1)*length]) for i in range(count-1)) + (
        tuple(chain[(count-1)*length:count*length+remainder]),)


def _parent(n, start, step, size):
    bounded_int(n, "modulus", 1, MAX_MODULUS)
    bounded_int(start, "start", 0, n-1)
    bounded_int(step, "step", 0, n-1)
    bounded_int(size, "parent length", 1, n)
    if size > n//gcd(n, step):
        raise ValueError("parent parameterization must be proper")
    return tuple((start+j*step) % n for j in range(size))


def phase_refinement(n, start, step, size, coefficient, offset, length):
    parent = _parent(n, start, step, size)
    bounded_int(coefficient, "coefficient", 0, n-1)
    bounded_int(offset, "offset", 0, n-1)
    bounded_int(length, "cell minimum length", 1, size)
    bound = size//length
    q, epsilon = dirichlet_step(n, coefficient*step, bound)
    cells = tuple(cell for residue in range(q)
                  for cell in _chunks(tuple(range(residue, size, q)), length))
    ensure(sorted(j for cell in cells for j in cell) == list(range(size)),
           "disjoint exact parent-index partition")
    phase_cells = []
    for indices in cells:
        values = tuple(parent[j] for j in indices)
        count = len(values)
        ensure(length <= count <= 2*length-1, "phase cell lengths")
        ensure(len(set(values)) == count, "phase cells proper by restriction")
        ensure(all((y-x) % n == q*step % n for x,y in zip(values, values[1:])),
               "modular arithmetic progression cells")
        initial = -Q(coefficient*values[0]+offset, n)
        midpoint = initial-epsilon*Q(count-1, 2)
        radius = abs(epsilon)*Q(count-1, 2)
        ensure(radius <= Q(length-1, bound+1), "reduced-lift radius bound")
        ensure(radius < Q(length*length, size), "strict rational phase radius")
        for j,x in enumerate(values):
            actual = -Q(coefficient*x+offset, n)
            lift = initial-epsilon*j
            ensure((actual-lift).denominator == 1, "phase agrees modulo integers")
            ensure(abs(lift-midpoint) <= radius, "reduced midpoint controls every lift")
        phase_cells.append({"indices": indices, "points": values,
                            "midpoint_turns": midpoint, "radius_turns": radius})
    return {"q": q, "epsilon": epsilon, "bound": bound, "cells": tuple(phase_cells)}


def phase_checks(nmax):
    bounded_int(nmax, "nmax", 2, MAX_NMAX)
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
    ensure(result["epsilon"] == 0, "regression reduced increment is zero")
    ensure(reduced_midpoint % 1 == 0 and raw_midpoint % 1 == Q(1, 2),
           "unreduced midpoint has exactly the opposite unit phase")
    return {"modulus": 6, "parent_points": list(cell["points"]), "coefficient": 3,
            "raw_increment_turns": str(raw_increment), "reduced_increment_turns": "0",
            "reduced_midpoint_mod_one": str(reduced_midpoint % 1),
            "unreduced_midpoint_mod_one": str(raw_midpoint % 1),
            "endpoint_phase": "+1", "reduced_midpoint_phase": "+1",
            "unreduced_midpoint_phase": "-1", "unreduced_chord_error": 2,
            "reduced_chord_error": 0}


def _epsilon(value):
    if type(value) not in (int, Q):
        raise ValueError("epsilon must be an exact integer or Fraction")
    value = Q(value)
    if not 0 < value <= 1 or max(value.numerator.bit_length(), value.denominator.bit_length()) > 64:
        raise ValueError("epsilon must lie in (0,1] with at most 64-bit numerator and denominator")
    return value


def rectify_box(n, step, axes, epsilon):
    """Bounded construction; products are counted, never materialized."""
    bounded_int(n, "modulus", 1, MAX_MODULUS)
    bounded_int(step, "common modular step", 0, n-1)
    if not isinstance(axes, (tuple, list)) or not 1 <= len(axes) <= MAX_DIMENSION:
        raise ValueError("axes must contain one to four (start, length) pairs")
    for axis in axes:
        if not isinstance(axis, (tuple, list)) or len(axis) != 2:
            raise ValueError("each axis must be a (start, length) pair")
    parents = tuple(_parent(n, start, step, size) for start,size in axes)
    epsilon = _epsilon(epsilon)
    dimension, minimum = len(axes), min(map(len, parents))
    # floor(epsilon*sqrt(minimum)/(3*k)), entirely in integer arithmetic.
    length = 1+isqrt(minimum*epsilon.numerator**2 // (9*dimension**2*epsilon.denominator**2))
    bound = isqrt(minimum)
    if length == 1:
        q, delta, sign = 1, 1, 1
    else:
        q, reduced = dirichlet_step(n, step, bound)
        delta = abs(reduced.numerator*n//reduced.denominator)
        sign = 1 if reduced > 0 else -1
        ensure(delta > 0, "properness rules out zero rectification increment")
    output = []
    for parent in parents:
        pieces = []
        if length == 1:
            pieces = [(x,) for x in parent]
        else:
            for residue in range(q):
                chain = list(parent[residue::q])
                if sign < 0:
                    chain.reverse()
                piece = [chain[0]]
                for point in chain[1:]:
                    ensure((point-piece[-1]) % n == delta, "positive oriented modular step")
                    if point < piece[-1]:
                        pieces.append(tuple(piece))
                        piece = [point]
                    else:
                        piece.append(point)
                pieces.append(tuple(piece))
            ensure(len(pieces) <= Q(len(parent), bound+1)+2*q, "wrap piece count")
        chunks = tuple(chunk for piece in pieces if len(piece) >= length
                       for chunk in _chunks(piece, length))
        retained = tuple(x for chunk in chunks for x in chunk)
        ensure(len(set(retained)) == len(retained), "axis chunks are disjoint")
        ensure(set(retained) <= set(parent), "retained axis is a parent subset")
        ensure(all(length <= len(chunk) <= 2*length-1 for chunk in chunks), "ordinary chunk widths")
        ensure(all(y-x == delta for chunk in chunks for x,y in zip(chunk, chunk[1:])),
               "ordinary integer common step")
        ensure(Q(len(parent)-len(retained), len(parent)) <= epsilon/dimension, "per-axis deletion budget")
        output.append({"chunks": chunks, "retained": len(retained), "original": len(parent)})
    original_mass = prod(len(parent) for parent in parents)
    retained_mass = prod(axis["retained"] for axis in output)
    lost = Q(original_mass-retained_mass, original_mass)
    ensure(lost <= epsilon, "ambient product exceptional-mass bound")
    return {"length": length, "q": q, "delta": delta, "axes": tuple(output),
            "original_mass": original_mass, "retained_mass": retained_mass,
            "loss_fraction": lost, "epsilon": epsilon}


def box_checks(full=False):
    if type(full) is not bool:
        raise ValueError("full must be boolean")
    cases = [(1, 0, ((0, 1),), Q(1)), (12, 4, ((11, 3), (2, 3)), Q(1, 2)),
             (41, 13, ((39, 20),), Q(1)), (97, 31, ((96, 40), (5, 47)), Q(1)),
             (97, 66, ((3, 40), (82, 42)), Q(1))]
    if full:
        cases.extend([(257, 73, ((255, 160), (127, 150)), Q(1, 2)),
                      (127, 93, ((125, 90), (1, 87), (59, 81)), Q(1)),
                      (128, 6, ((127, 40), (21, 50)), Q(1))])
    rows = []
    for n,step,axes,epsilon in cases:
        result = rectify_box(n, step, axes, epsilon)
        rows.append({"modulus": n, "step": step, "dimension": len(axes),
                     "axis_lengths": [size for _,size in axes], "epsilon": str(epsilon),
                     "minimum_output_width": result["length"], "common_integer_step": result["delta"],
                     "original_mass": result["original_mass"], "retained_mass": result["retained_mass"],
                     "loss_fraction": str(result["loss_fraction"])})
    ensure(any(row["minimum_output_width"] >= 2 for row in rows), "nontrivial rectification coverage")
    return {"cases": rows, "scope": "ambient product mass, not Section 16 base-set loss or an exact full partition"}


def run_checks(nmax=None, full=False):
    if type(full) is not bool:
        raise ValueError("full must be boolean")
    if nmax is None:
        nmax = MAX_NMAX if full else DEFAULT_NMAX
    bounded_int(nmax, "nmax", 2, MAX_NMAX)
    return {"report": 275, "arithmetic": "integers and exact fractions only",
            "finite_diagnostics_not_proofs": True,
            "parameters": {"nmax": nmax, "full": full, "hard_nmax_cap": MAX_NMAX},
            "variance": variance_checks(nmax), "all_step_moments": all_step_checks(nmax, full),
            "cover_mass": cover_mass_checks(min(nmax, MAX_COVER_NMAX)),
            "composite_cap_regression": composite_cap_regression(),
            "phase_partitions": phase_checks(nmax), "midpoint_regression": midpoint_regression(),
            "box_rectification": box_checks(full),
            "limitations": ["No general correlation or density-increment theorem is established by finite enumeration.",
                            "No numerical complex exponential, irrational root, or chord/arc evaluation is used.",
                            "No Lean verification, Section 16 integration, final Ramsey/Szemeredi bound, or novelty claim."]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    def nmax_value(value):
        try:
            return parse_integer(value, "nmax", 2, MAX_NMAX)
        except ValueError as exc:
            raise argparse.ArgumentTypeError(str(exc)) from exc
    parser.add_argument("--nmax", type=nmax_value, default=None,
                        help=f"maximum exhaustive modulus, 2..{MAX_NMAX}; default {DEFAULT_NMAX}, or {MAX_NMAX} with --full")
    parser.add_argument("--full", action="store_true",
                        help="extend the default modulus to 12, add N=64 all-step cases and three bounded box cases")
    args = parser.parse_args(argv)
    print(json.dumps(run_checks(args.nmax, args.full), sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
