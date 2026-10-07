#!/usr/bin/env python3
"""Finite supporting checks for logarithmic component selection.

Exact checks use rational abstract logarithmic coordinates, integer cyclic
fibres, and finite probability distributions. A separate explicitly numerical
section uses actual natural logarithms. These computations check mechanisms
and constants; the mathematical proofs establish the infinite parameter claims.

Run: python verify_selection.py --output selection_checks.json
Only the Python standard library is required. The random seed is fixed.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path
import random


SEED = 20261006
ETA = F(1, 2**21)


def intersection_length(a, b, c, d):
    return max(F(0), min(b, d) - max(a, c))


def interval_probability(y, halfwidth, domain):
    return intersection_length(y-halfwidth, y+halfwidth, *domain) / (
        domain[1]-domain[0])


def exact_window_probabilities():
    membership_checks = boundary_checks = core_equalities = clipped_cases = 0
    positive_boundary_cases = 0
    max_boundary_ratio = F(0)
    for h, a, b in itertools.product((F(1, 4), F(1, 2)),
                                     (F(-2), F(-3)), (F(-3), F(-5))):
        iq, ir = (a-h, h), (b-h, h)
        p = 4*h*h / ((iq[1]-iq[0])*(ir[1]-ir[0]))
        us = sorted({F(0), a, a/2, a-2*h, a-h, a-3*h,
                     a+h/3, -h/3, a-h/3})
        vs = sorted({F(0), b, b/2, b-2*h, b-h, b-3*h,
                     b+h/3, -h/3, b-h/3})
        for u, v in itertools.product(us, vs):
            outer = interval_probability(u, h, iq)*interval_probability(v, h, ir)
            assert 0 <= outer <= p
            membership_checks += 1
            if u >= a and v >= b:
                assert outer == p
                core_equalities += 1
            elif 0 < outer < p:
                clipped_cases += 1
            for dq, dr in itertools.product((h/32, h/8, h/2, h), repeat=2):
                inner = (interval_probability(u, h-dq, iq)
                         * interval_probability(v, h-dr, ir))
                boundary = outer-inner
                beta = (dq+dr)/h
                assert 0 <= boundary <= p*beta
                boundary_checks += 1
                if boundary > 0:
                    positive_boundary_cases += 1
                    max_boundary_ratio = max(max_boundary_ratio, boundary/(p*beta))
    assert clipped_cases > 0 and positive_boundary_cases > 0

    # Integrate the three-term selection functional exactly by partitioning
    # the centre rectangle into all cells of constant membership.
    rng = random.Random(SEED)
    functional_cases = functional_cells = 0
    smallest_maximum_over_guarantee = None
    for case in range(4):
        h, a, b = F(1, 2), F(-2), F(-3)
        iq, ir = (a-h, h), (b-h, h)
        dq, dr = F(1, 64), F(1, 32)
        beta = (dq+dr)/h
        p = 4*h*h/((iq[1]-iq[0])*(ir[1]-ir[0]))
        eta = F(1, 2**12)
        points = []
        for _ in range(5):
            points.append((F(-rng.randrange(0, 9), 4),
                           F(-rng.randrange(0, 13), 4),
                           F(rng.randrange(4, 9)),
                           eta*rng.randrange(0, 40)))
        points.extend([(a-h/2, b, F(1), 20*eta),
                       (a, b-h/2, F(1), 30*eta)])
        total = sum(w for _, _, w, _ in points)
        core = sum(w for u, v, w, _ in points if u >= a and v >= b)
        assert core >= total/2
        assert sum(w*e for _, _, w, e in points) <= 60*eta*total
        axes = []
        for coordinate, margin, domain in ((0, dq, iq), (1, dr, ir)):
            breaks = {domain[0], domain[1]}
            for point in points:
                t = point[coordinate]
                for width in (h, h-margin):
                    for edge in (t-width, t+width):
                        if domain[0] < edge < domain[1]:
                            breaks.add(edge)
            axes.append(sorted(breaks))
        integral, maximum = F(0), None
        for lq, rq in zip(axes[0], axes[0][1:]):
            for lr, rr in zip(axes[1], axes[1][1:]):
                cq, cr = (lq+rq)/2, (lr+rr)/2
                sw = ew = qv = F(0)
                for u, v, weight, error in points:
                    if abs(u-cq) <= h and abs(v-cr) <= h:
                        ew += weight*error
                        if u >= a and v >= b:
                            sw += weight
                        if abs(u-cq) >= h-dq or abs(v-cr) >= h-dr:
                            qv += weight
                objective = sw-ew/(480*eta)-qv/(8*beta)
                integral += objective*(rq-lq)*(rr-lr)
                maximum = objective if maximum is None else max(maximum, objective)
                functional_cells += 1
        expectation = integral/((iq[1]-iq[0])*(ir[1]-ir[0]))
        assert expectation >= p*total/4
        assert maximum >= expectation
        ratio = maximum/(p*total/4)
        smallest_maximum_over_guarantee = (ratio if smallest_maximum_over_guarantee
                                         is None else min(ratio, smallest_maximum_over_guarantee))
        functional_cases += 1
    return {"status": "passed", "arithmetic": "exact fractions",
            "membership_checks": membership_checks,
            "core_probability_equalities": core_equalities,
            "clipped_noncore_cases": clipped_cases,
            "boundary_probability_checks": boundary_checks,
            "positive_boundary_cases": positive_boundary_cases,
            "maximum_boundary_to_union_bound_ratio": str(max_boundary_ratio),
            "functional_cases": functional_cases,
            "integrated_constant_membership_cells": functional_cells,
            "smallest_maximum_over_guarantee": str(smallest_maximum_over_guarantee),
            "scope": "Abstract rational logarithmic coordinates; selection probabilities, weighted boundary expectation, and positive functional. The coordinate weights in these abstract tests are not asserted to come from a cyclic domain."}


def circular_autocorrelation(counts):
    n = len(counts)
    return [sum(counts[t]*counts[(t+r) % n] for t in range(n)) for r in range(n)]


def exact_fibre_boundary_checks():
    profiles = [(521, 10000, 10, None), (1021, 20000, 13, None),
                (521, 10000, 10, 180)]
    windows = escape_checks = interior_points = proper_windows = 0
    nonempty_proper_boundaries = actual_shift_exits = 0
    max_ratio = F(0)
    examples = []
    for n, base, step, cap in profiles:
        dist = [min(i, n-i) for i in range(n)]
        counts = [base+step*(min(x, cap) if cap else x) for x in dist]
        m = 2*base
        alpha = F(sum(counts), m*n)
        sigma = F(max(abs(counts[(i+1) % n]-counts[i]) for i in range(n)), m)
        assert sigma <= alpha*alpha/128
        q = circular_autocorrelation(counts)
        qmax = m*sum(counts)
        u, v = [F(x, qmax) for x in q], [F(x, m) for x in counts]
        for i in range(n):
            assert abs(u[(i+1) % n]-u[i]) <= sigma
        # Rational multiplicative buffers dominate the proof's logarithmic
        # buffers, avoiding all irrational accept/reject decisions here.
        kq, kr = 1+128*sigma/alpha, 1+128*sigma/(alpha*alpha)
        assert kq*kq < 2 and kr*kr < 2
        q_lowers = (min(u)*F(2, 3), max(u)*F(2, 3))
        thresholds = [min(v)+(max(v)-min(v))*F(j, 8) for j in range(1, 8)]
        r_lowers = thresholds+[t/2 for t in thresholds]
        for lq, lr in itertools.product(q_lowers, r_lowers):
            selected = {i for i in range(n) if lq <= u[i] <= 2*lq
                        and lr <= v[i] <= 2*lr}
            if not selected:
                continue
            inner = {i for i in selected if lq*kq < u[i] < 2*lq/kq
                     and lr*kr < v[i] < 2*lr/kr}
            boundary = selected-inner
            wsize = sum(counts[i] for i in selected)
            vsize = sum(counts[i] for i in boundary)
            qw = sum(counts[i]*q[i] for i in selected)
            qv = sum(counts[i]*q[i] for i in boundary)
            assert vsize*qw <= 2*qv*wsize
            if qv:
                max_ratio = max(max_ratio, F(vsize*qw, qv*wsize))
            if 0 < len(selected) < n:
                proper_windows += 1
            if inner and boundary:
                nonempty_proper_boundaries += 1
                if len(examples) < 3:
                    examples.append({"n": n, "alpha": str(alpha),
                                     "sigma": str(sigma), "selected_fibres": len(selected),
                                     "inner_fibres": len(inner), "boundary_fibres": len(boundary)})
            for d in (-1, 0, 1):
                for i in inner:
                    assert (i-d) % n in selected
                    escape_checks += 1
                actual_shift_exits += sum((i-d) % n not in selected for i in selected)
            interior_points += len(inner)
            windows += 1
    assert proper_windows and nonempty_proper_boundaries and actual_shift_exits
    return {"status": "passed", "arithmetic": "integer correlations and exact fractions",
            "profiles": len(profiles), "windows": windows,
            "proper_windows": proper_windows,
            "windows_with_both_inner_and_boundary_fibres": nonempty_proper_boundaries,
            "weighted_boundary_comparisons": windows,
            "maximum_cardinality_ratio_over_mass_ratio": str(max_ratio),
            "interior_fibre_instances": interior_points,
            "shifted_inner_fibre_escape_checks": escape_checks,
            "actual_selected_fibre_exits_before_boundary_removal": actual_shift_exits,
            "examples": examples,
            "scope": "Physical finite cyclic domains and multiplicative windows of ratio two; exact buffers conservatively dominate the logarithmic buffers. These profiles check the escape mechanism, not the tiny final homomorphism error assumption."}


def exact_modal_checks():
    n = 32
    distributions = [(a, b, n-a-b) for a in range(n+1) for b in range(n+1-a)]
    agreements = near_perfect = mixed_near_perfect = 0
    for p in distributions:
        mode = max(range(3), key=p.__getitem__)
        for q in distributions:
            dot = sum(a*b for a, b in zip(p, q))
            disagreements = n*n-dot
            assert p[mode]*(n-q[mode]) <= disagreements
            agreements += 1
            if 32*dot >= 31*n*n:
                assert 32*p[mode] >= 31*n
                assert sum(x == p[mode] for x in p) == 1
                assert 31*n*(n-q[mode]) <= 32*disagreements
                assert 31*(n-q[mode]) <= n
                near_perfect += 1
                mixed_near_perfect += int(max(p) < n or max(q) < n)
    assert near_perfect and mixed_near_perfect
    return {"status": "passed", "arithmetic": "exact integer comparisons",
            "alphabet_size": 3, "probability_denominator": n,
            "distributions": len(distributions), "ordered_distribution_pairs": agreements,
            "pairs_with_agreement_at_least_31_over_32": near_perfect,
            "nonconstant_near_perfect_pairs": mixed_near_perfect,
            "scope": "Mode existence, uniqueness, and the edge-failure bound from an averaged anchor agreement."}


def exact_transport_checks():
    pushforward_checks = path_checks = nonzero_error_paths = nontrivial_outside_paths = 0
    bounds_below_one = 0
    for n in (5, 7, 9):
        counts = [40+(i % 3)*5 for i in range(n)]
        for selected in (set(range(n)), set(range(n-1))):
            wsize = sum(counts[i] for i in selected)
            for corruption in (False, True):
                labels = []
                for i, count in enumerate(counts):
                    distribution = Counter({i: count})
                    if corruption and i == 1:
                        distribution[i] -= 1
                        distribution[(i+1) % n] += 1
                    labels.append(distribution)
                shifts = (-1, 0, 1)
                edge_error, outside = {}, {}
                for d in shifts:
                    out = F(0)
                    incoming = [F(0)]*n
                    error = F(0)
                    for i in selected:
                        j = (i+d) % n
                        incoming[j] += F(counts[i], wsize)
                        if j not in selected:
                            out += F(counts[i], wsize)
                        for label, count in labels[i].items():
                            correct = F(labels[j].get((label+d) % n, 0), counts[j])
                            error += F(count, wsize)*(1-correct)
                    for j in selected:
                        assert incoming[j]/counts[j] <= F(2, wsize)
                        pushforward_checks += 1
                    assert out == F(sum(counts[i] for i in selected
                                        if (i+d) % n not in selected), wsize)
                    edge_error[d], outside[d] = error, out
                for d1, d2, d3, d4 in itertools.product(shifts, repeat=4):
                    if (d1+d2-d3-d4) % n:
                        continue
                    success = F(0)
                    for i in selected:
                        j1, j3, endpoint = (i+d1) % n, (i+d3) % n, (i+d1+d2) % n
                        if j1 not in selected or j3 not in selected:
                            continue
                        for label, count in labels[i].items():
                            p1 = F(labels[j1].get((label+d1) % n, 0), counts[j1])
                            p3 = F(labels[j3].get((label+d3) % n, 0), counts[j3])
                            pv = F(labels[endpoint].get((label+d1+d2) % n, 0), counts[endpoint])
                            success += F(count, wsize)*p1*p3*pv
                    bound = (edge_error[d1]+edge_error[d3]+2*edge_error[d2]
                             +2*edge_error[d4]+outside[d1]+outside[d3])
                    assert 1-success <= bound
                    if bound < 1:
                        assert success > 0
                        bounds_below_one += 1
                    path_checks += 1
                    nonzero_error_paths += int(any(edge_error[d] > 0 for d in (d1,d2,d3,d4)))
                    nontrivial_outside_paths += int(outside[d1]+outside[d3] > 0)
    assert nonzero_error_paths and nontrivial_outside_paths and bounds_below_one
    return {"status": "passed", "arithmetic": "exact fractions on finite labelled fibres",
            "pushforward_point_mass_bounds": pushforward_checks,
            "coupled_two_path_checks": path_checks,
            "paths_with_positive_label_error": nonzero_error_paths,
            "paths_with_positive_outside_mass": nontrivial_outside_paths,
            "bounds_strictly_below_one": bounds_below_one,
            "scope": "A single shared endpoint is used on both paths; the checked union bound has coefficients 1,1,2,2 on the four edge-error means."}


def exact_constants():
    # log(2)=2*atanh(1/3); the displayed positive geometric remainder bound
    # supplies a rational bracket rather than a floating comparison.
    terms = 14
    lo = 2*sum((F(1, (2*k+1)*3**(2*k+1)) for k in range(terms)), F(0))
    hi = lo+F(9, 4*(2*terms+1)*3**(2*terms+1))
    assert F(69, 100) < lo < hi < F(7, 10)
    assert hi-lo < F(1, 10**14)
    holes = 122880*ETA
    assert holes == F(15, 256) < F(1, 16)
    assert F(6, 31)+2*ETA < 1
    assert F(27, 31)/16 > F(1, 20)
    assert F(5, 8)**3 < F(1, 4)
    assert 3*holes+2*F(3, 8) < 1
    assert F(5, 8)-2*holes > F(1, 2)
    order15_budget = (30+210*F(1, 2**27))*(F(1, 31)+ETA)
    assert order15_budget == F(4222187282107575, 4362862139015168) < 1
    parameter_cases = 0
    for alpha in (F(1, 1000000), F(1, 100), F(1, 10), F(1, 2), F(1)):
        for ell in (lo, hi):
            sigma = ETA*ell*alpha**2/(2048*(1+alpha))
            assert sigma <= ETA*alpha**2
            assert sigma <= alpha**2/128
            dq_over_h = 128*sigma/(alpha*ell)
            dr_over_h = 128*sigma/(alpha**2*ell)
            assert dq_over_h < 1 and dr_over_h < 1
            assert dq_over_h+dr_over_h == ETA/16
            tau = 32*sigma/alpha**2
            assert tau < F(1, 2**27)
            lam2 = sigma*alpha**2/4
            assert lam2 == ell*alpha**4/(2**34*(1+alpha))
            rank = 4/(sigma*alpha)
            assert rank == 2**34*(1+alpha)/(ell*alpha**3)
            rho_pi = sigma/4
            assert 2*rho_pi+2*lam2/alpha**2 == sigma
            zeta_pi = rho_pi/(6*rank)
            assert zeta_pi == sigma*sigma*alpha/96
            assert zeta_pi == ell**2*alpha**5/(3*2**69*(1+alpha)**2)
            parameter_cases += 1
    return {"status": "passed", "arithmetic": "exact fractions and a proved rational logarithm bracket",
            "eta": str(ETA), "direction_hole_bound": str(holes),
            "coupled_path_failure_bound": str(F(6, 31)+2*ETA),
            "retained_row_fraction": "27/31",
            "pullback_overlap_lower_bound_relative_to_B": str(F(5, 8)-2*holes),
            "pullback_error_budget_relative_to_B_prime": "1/2",
            "extension_union_bound": str(3*holes+2*F(3, 8)),
            "order15_path_budget": str(order15_budget),
            "order15_budget_slack": str(1-order15_budget),
            "difference_map_guaranteed_order": 15//2,
            "log2_bracket": [str(lo), str(hi)],
            "log2_bracket_width": str(hi-lo),
            "parameter_cases": parameter_cases}


def exact_prefix_checks():
    prefix_checks = paths = long_couplings = positive_failure = bounds_below_one = 0
    for n in (5, 7, 9):
        counts = [40+(i % 3)*5 for i in range(n)]
        labels = []
        for i, count in enumerate(counts):
            distribution = Counter({i: count})
            if i == 1:
                distribution[i] -= 1
                distribution[(i+1) % n] += 1
            labels.append(distribution)
        for selected in (set(range(n)), set(range(n-1))):
            size = sum(counts[i] for i in selected)
            minimum = min(counts[i] for i in selected)
            shifts = (-1, 0, 1)
            variation = max(abs(counts[(i+d) % n]-counts[i])
                            for i in range(n) for d in shifts)
            tau = F(variation, minimum)
            e, eta = F(0), F(0)
            for d in shifts:
                err = F(0)
                for i in selected:
                    target = (i+d) % n
                    for value, multiplicity in labels[i].items():
                        correct = F(labels[target].get((value+d) % n, 0), counts[target])
                        err += F(multiplicity, size)*(1-correct)
                e = max(e, err)
                eta = max(eta, F(sum(counts[i] for i in selected
                                    if (i+d) % n not in selected), size))
            for k in (2, 3, 5, 7):
                sequences = [tuple(1 for _ in range(k)),
                             tuple((1, -1, 0)[j % 3] for j in range(k))]
                for directions in sequences:
                    law = {(i, value): F(multiplicity, size)
                           for i in selected for value, multiplicity in labels[i].items()}
                    prefix = 0
                    for j, d in enumerate(directions, start=1):
                        updated = {}
                        for (i, value), mass in law.items():
                            target, next_value = (i+d) % n, (value+d) % n
                            if target in selected:
                                probability = F(labels[target].get(next_value, 0), counts[target])
                                if probability:
                                    key = (target, next_value)
                                    updated[key] = updated.get(key, F(0))+mass*probability
                        law = updated
                        prefix += d
                        for (i, value), mass in law.items():
                            source = (i-prefix) % n
                            exact_domination = (F(counts[source], size*counts[i])
                                                if source in selected else F(0))
                            density = mass/labels[i][value]
                            assert density <= exact_domination
                            assert density <= (1+j*tau)/size
                            prefix_checks += 1
                        budget = (j+tau*j*(j-1)/2)*(e+eta)
                        assert 1-sum(law.values(), F(0)) <= budget
                    failure = 1-sum(law.values(), F(0))
                    positive_failure += int(failure > 0)
                    paths += 1

                first = sequences[1]
                second = tuple(reversed(first))
                success = F(0)
                for i in selected:
                    endpoint = (i+sum(first)) % n
                    if endpoint not in selected:
                        continue
                    for value, multiplicity in labels[i].items():
                        probability = F(multiplicity, size)
                        for directions in (first, second):
                            prefix = 0
                            for d in directions[:-1]:
                                prefix += d
                                index = (i+prefix) % n
                                if index not in selected:
                                    probability = F(0)
                                    break
                                probability *= F(labels[index].get((value+prefix) % n, 0), counts[index])
                        probability *= F(labels[endpoint].get((value+sum(first)) % n, 0), counts[endpoint])
                        success += probability
                coupled_budget = (2*k+tau*k*(k-1))*(e+eta)
                assert 1-success <= coupled_budget
                if coupled_budget < 1:
                    assert success > 0
                    bounds_below_one += 1
                long_couplings += 1
    assert positive_failure and bounds_below_one
    return {"status": "passed", "arithmetic": "exact finite probability sublaws",
            "tested_path_lengths": [2, 3, 5, 7], "stopped_paths": paths,
            "prefix_point_mass_comparisons": prefix_checks,
            "paths_with_positive_failure": positive_failure,
            "shared_endpoint_long_path_couplings": long_couplings,
            "long_coupled_bounds_below_one": bounds_below_one,
            "scope": "Unnormalized surviving prefix laws; tests include killing on label failure and exit. Order fifteen itself is checked through the exact rational parameter criterion, not exhaustive fifteen-step path enumeration."}


def actual_logarithm_checks():
    profiles = [[2, 3, 4, 5, 4, 3, 2],
                [1, 2, 4, 6, 5, 3, 1, 2, 3, 5, 4],
                [8, 8, 9, 10, 11, 10, 9, 8, 9, 10, 9, 8, 8]]
    tol = 2e-9
    probability_tol = 5e-15
    max_integral_error = max_probability_violation = 0.0
    cell_count = 0
    output = []
    for counts in profiles:
        n, m = len(counts), max(counts)
        alpha = sum(counts)/(m*n)
        corr = circular_autocorrelation(counts)
        candidates = []
        for pivot in range(n):
            if counts[pivot] >= alpha**2*m/2:
                qr = [corr[(r-pivot) % n] for r in range(n)]
                candidates.append((sum(counts[r]*qr[r] for r in range(n)), qr))
        s, q = max(candidates, key=lambda pair: pair[0])
        assert s+1e-10 >= alpha**3*m**3*n**2/4
        u = [x/(m*sum(counts)) for x in q]
        v = [x/m for x in counts]
        weights = [counts[i]*q[i]/s for i in range(n)]
        h = math.log(2)/2
        a, b = math.log(alpha/16), math.log(alpha*alpha/16)
        iq, ir = (a-h, h), (b-h, h)
        sigma = float(ETA)*math.log(2)*alpha**2/(2048*(1+alpha))
        dq, dr = 64*sigma/alpha, 64*sigma/(alpha*alpha)
        beta = (dq+dr)/h
        p = 4*h*h/((iq[1]-iq[0])*(ir[1]-ir[0]))
        logs = [(math.log(x), math.log(y)) for x, y in zip(u, v)]
        core = [u[i] >= alpha/16 and v[i] >= alpha**2/16 for i in range(n)]

        def prob(t, width, domain):
            return max(0.0, min(domain[1], t+width)-max(domain[0], t-width))/(domain[1]-domain[0])

        analytic = 0.0
        axes = []
        for coordinate, delta, domain in ((0, dq, iq), (1, dr, ir)):
            edges = {domain[0], domain[1]}
            for point in logs:
                for width in (h, h-delta):
                    for edge in (point[coordinate]-width, point[coordinate]+width):
                        if domain[0] < edge < domain[1]:
                            edges.add(edge)
            axes.append(sorted(edges))
        for i, (uq, vr) in enumerate(logs):
            outer = prob(uq, h, iq)*prob(vr, h, ir)
            inner = prob(uq, h-dq, iq)*prob(vr, h-dr, ir)
            boundary = outer-inner
            assert outer <= p+probability_tol and boundary <= p*beta+probability_tol
            if core[i]:
                assert abs(outer-p) < probability_tol
            max_probability_violation = max(max_probability_violation, outer-p, boundary-p*beta)
            analytic += weights[i]*((outer if core[i] else 0)-boundary/(8*beta))
        integral, best = 0.0, -math.inf
        for lq, rq in zip(axes[0], axes[0][1:]):
            for lr, rr in zip(axes[1], axes[1][1:]):
                cq, cr = (lq+rq)/2, (lr+rr)/2
                sw = qv = 0.0
                for i, (uq, vr) in enumerate(logs):
                    if abs(uq-cq) <= h and abs(vr-cr) <= h:
                        if core[i]:
                            sw += weights[i]
                        if abs(uq-cq) >= h-dq or abs(vr-cr) >= h-dr:
                            qv += weights[i]
                value = sw-qv/(8*beta)
                integral += value*(rq-lq)*(rr-lr)
                best = max(best, value)
                cell_count += 1
        integrated = integral/((iq[1]-iq[0])*(ir[1]-ir[0]))
        error = abs(integrated-analytic)
        max_integral_error = max(max_integral_error, error)
        assert error <= tol
        assert integrated+tol >= p/4 and best+tol >= p/4
        output.append({"n": n, "alpha": alpha, "p": p,
                       "beta": beta, "integrated_normalized_functional": integrated,
                       "guaranteed_normalized_functional": p/4,
                       "best_cell_normalized_functional": best,
                       "integration_vs_probability_error": error})
    return {"status": "passed", "arithmetic": "IEEE double for actual natural logarithms",
            "absolute_tolerance": tol, "profiles": len(profiles),
            "probability_absolute_tolerance": probability_tol,
            "integrated_cells": cell_count,
            "maximum_integration_error": max_integral_error,
            "maximum_positive_probability_violation": max(0.0, max_probability_violation),
            "examples": output,
            "scope": "Supporting checks of the actual log windows and integrated selection functional at eta=2^-21. The fibre profiles in this numerical section are not assumed invariant at the tiny chosen sigma; this section does not test the full homomorphism theorem."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="selection_checks.json")
    args = parser.parse_args()
    result = {"seed": SEED,
              "purpose": "Supporting finite mechanism checks; no claim of formal proof or exhaustive testing of the structure theorem.",
              "window_probabilities_and_functional": exact_window_probabilities(),
              "physical_fibre_boundaries": exact_fibre_boundary_checks(),
              "modal_distributions": exact_modal_checks(),
              "coupled_transport": exact_transport_checks(),
              "surviving_prefix_laws": exact_prefix_checks(),
              "constants": exact_constants(),
              "actual_logarithms": actual_logarithm_checks()}
    Path(args.output).write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": "passed", "output": str(Path(args.output).resolve()),
                      "sections": list(result)[2:]}, indent=2))


if __name__ == "__main__":
    main()
