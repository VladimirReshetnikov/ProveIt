#!/usr/bin/env python3
"""Cache conditional-potential row sums in deterministic packet balancing.

This is a semantics-preserving optimization of the actual incoming
eth_asymmetric_packet_balancing_2026-10-26/code/balanced_packing.py.
The original is preserved byte-for-byte as reference_balanced_packing.py.
For Q labels and N columns, evaluating all candidate labels now takes
O(N Q**2) rational arithmetic operations, rather than O(N Q**3).
Exact rational bit lengths and returned certificates are unchanged.
"""
from fractions import Fraction
from reference_balanced_packing import _adjacency


def balance_pair_labels(adjacency, label_count, smoothness=8, keep_certificate=True):
    if type(label_count) is not int or label_count < 1:
        raise ValueError("label_count must be a positive integer")
    if type(smoothness) is not int or smoothness < 2:
        raise ValueError("smoothness must be an integer at least two")
    adj, ncols = _adjacency(adjacency)
    nrows = len(adj)
    row_degrees = [sum(row) for row in adj]
    col_degrees = [sum(adj[i][j] for i in range(nrows)) for j in range(ncols)]
    M = sum(row_degrees)
    R = max(row_degrees, default=0)
    C = max(col_degrees, default=0)
    potential_C = max(1, C)
    Q = label_count
    q = Fraction(smoothness * potential_C + 1, smoothness * potential_C)
    powers = [Fraction(1)]
    for _ in range(M):
        powers.append(powers[-1] * q)

    row_loads = [0] * Q
    row_labels = []
    for degree in row_degrees:
        label = min(range(Q), key=lambda a: (row_loads[a], a))
        row_labels.append(label)
        row_loads[label] += degree

    weights = [[0] * ncols for _ in range(Q)]
    for i, row in enumerate(adj):
        for j, value in enumerate(row):
            weights[row_labels[i]][j] += value
    if any(value > C for row in weights for value in row):
        raise ArithmeticError("Column weight exceeded the column-degree bound")
    factors = [[Fraction(Q - 1, Q) + powers[value] / Q for value in row]
               for row in weights]
    future = []
    for row in factors:
        value = Fraction(1)
        for factor in row:
            value *= factor
        future.append(value)

    loads = [[0] * Q for _ in range(Q)]
    # B[a,b]=q**loads[a,b], S[a]=sum_b B[a,b].  Keeping these exact values
    # avoids summing the same unchanged Q-1 terms for every candidate label.
    cell_powers = [[Fraction(1)] * Q for _ in range(Q)]
    row_sums = [Fraction(Q)] * Q
    current = Q * sum(future, Fraction(0))
    initial = current
    column_labels = []
    certificates = []
    for j in range(ncols):
        next_future = [future[a] / factors[a][j] for a in range(Q)]
        deltas = [powers[weights[a][j]] - 1 for a in range(Q)]
        base = sum((next_future[a] * row_sums[a] for a in range(Q)), Fraction(0))
        coefficients = [next_future[a] * deltas[a] for a in range(Q)]
        scores = [base + sum((coefficients[a] * cell_powers[a][b]
                            for a in range(Q)), Fraction(0)) for b in range(Q)]
        if sum(scores, Fraction(0)) / Q != current:
            raise ArithmeticError("Conditional-expectation averaging identity failed")
        selected = min(range(Q), key=lambda b: (scores[b], b))
        if scores[selected] > current:
            raise ArithmeticError("Conditional expectation increased")
        if keep_certificate:
            certificates.append({
                "column": j, "selected_label": selected,
                "before": str(current), "after": str(scores[selected]),
                "candidate_scores": [str(score) for score in scores],
            })
        column_labels.append(selected)
        for a in range(Q):
            increment = cell_powers[a][selected] * deltas[a]
            cell_powers[a][selected] += increment
            row_sums[a] += increment
            loads[a][selected] += weights[a][j]
        future = next_future
        current = scores[selected]

    final_potential = sum((powers[value] for row in loads for value in row), Fraction(0))
    if current != final_potential or current > initial:
        raise ArithmeticError("Final potential certificate failed")
    # A separate recomputation checks both maintained cache invariants.
    if any(cell_powers[a][b] != powers[loads[a][b]]
           for a in range(Q) for b in range(Q)):
        raise ArithmeticError("Cached cell power is inconsistent")
    if any(row_sums[a] != sum(cell_powers[a], Fraction(0)) for a in range(Q)):
        raise ArithmeticError("Cached row sum is inconsistent")
    if any(Q * value > M + Q * R for value in row_loads):
        raise ArithmeticError("Greedy row bound failed")
    return {
        "row_labels": row_labels, "column_labels": column_labels,
        "row_loads": row_loads, "pair_loads": loads,
        "edges": M, "maximum_degree": max(R, C),
        "maximum_row_degree": R, "maximum_column_degree": C,
        "potential_column_bound": potential_C,
        "label_count": Q, "smoothness": smoothness,
        "potential_base": str(q), "initial_expected_potential": str(initial),
        "final_potential": str(final_potential),
        "max_pair_load": max((value for row in loads for value in row), default=0),
        "checked_assignment_steps": ncols, "steps": certificates,
    }
