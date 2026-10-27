"""Incremental exact implementation of the matching-potential derandomizer.

Maintains one product per matching/ordered label pair.  The returned dictionary
agrees exactly with eth_matching_refinement/code/refinement.py:label_graph.
No approximation, random choice, or new analytic packing assumption is used.
"""
from __future__ import annotations
from fractions import Fraction as F


def color_matchings(edges):
    """The same first-fit coloring, with set membership instead of edge scans."""
    groups, left_sets, right_sets = [], [], []
    for edge in edges:
        left, right = edge
        for i, group in enumerate(groups):
            if left not in left_sets[i] and right not in right_sets[i]:
                group.append(edge)
                left_sets[i].add(left)
                right_sets[i].add(right)
                break
        else:
            groups.append([edge])
            left_sets.append({left})
            right_sets.append({right})
    return groups


def packing_data(edges, labels, lam):
    if type(labels) is not int or labels < 1 or type(lam) is not int or lam < 1:
        raise ValueError('labels and lambda must be positive integers')
    groups = color_matchings(edges)
    if not groups:
        return [], 0, []
    tau = (8 * len(groups) * labels * labels - 1).bit_length()
    thresholds = [-(-((lam + 1) * len(g)) // (lam * labels * labels)) + 2 * lam * tau
                  for g in groups]
    return groups, tau, thresholds


def label_graph_incremental(edges, labels=2, lam=4):
    """Identical labels and exact trace with O(M Q^2 + V Q) field operations.

    M is the number of edges (multiplicity included), V incident vertices,
    Q=labels. Greedy coloring costs O(M K) elementary membership tests for K
    matchings; input sorting and exact-integer bit costs are separate.
    """
    edges = list(edges)
    groups, tau, thresholds = packing_data(edges, labels, lam)
    incident = {}
    for group_index, group in enumerate(groups):
        for left, right in group:
            vl, vr = ('L', left), ('R', right)
            incident.setdefault(vl, []).append((group_index, vr))
            incident.setdefault(vr, []).append((group_index, vl))
    vertices = sorted(incident)
    both_free = 1 + F(1, lam * labels * labels)
    one_free = 1 + F(1, lam * labels)
    neither_free = 1 + F(1, lam)
    products = []
    initial = F(0)
    for group, threshold in zip(groups, thresholds):
        value = neither_free ** (-threshold) * both_free ** len(group)
        products.append([[value] * labels for _ in range(labels)])
        initial += labels * labels * value
    current = initial
    assignment, trace = {}, []
    for vertex in vertices:
        base = current
        scores = [F(0)] * labels
        changed_slices = []
        is_left = vertex[0] == 'L'
        for group_index, neighbor in incident[vertex]:
            neighbor_label = assignment.get(neighbor)
            if neighbor_label is None:
                opposite_labels = range(labels)
                old_factor, new_factor = both_free, one_free
            else:
                opposite_labels = (neighbor_label,)
                old_factor, new_factor = one_free, neither_free
            table = products[group_index]
            for opposite in opposite_labels:
                old_values = ([table[candidate][opposite] for candidate in range(labels)]
                              if is_left else list(table[opposite]))
                quotients = [value / old_factor for value in old_values]
                base += sum(quotients, F(0)) - sum(old_values, F(0))
                for candidate, value in enumerate(quotients):
                    scores[candidate] += value * (new_factor - 1)
                    if is_left:
                        table[candidate][opposite] = value
                    else:
                        table[opposite][candidate] = value
                changed_slices.append((group_index, opposite, new_factor))
        values = [base + score for score in scores]
        if sum(values, F(0)) != labels * current:
            raise ArithmeticError('Conditional expectation identity failed')
        chosen = min(range(labels), key=lambda candidate: (values[candidate], candidate))
        if values[chosen] > current:
            raise ArithmeticError('Potential increased')
        for group_index, opposite, new_factor in changed_slices:
            if is_left:
                products[group_index][chosen][opposite] *= new_factor
            else:
                products[group_index][opposite][chosen] *= new_factor
        assignment[vertex] = chosen
        current = values[chosen]
        trace.append(current)
    loads = [[0] * labels for _ in range(labels)]
    for left, right in edges:
        loads[assignment['L', left]][assignment['R', right]] += 1
    final_from_products = sum((value for table in products for row in table for value in row), F(0))
    if final_from_products != current:
        raise ArithmeticError('Maintained products disagree with the final potential')
    return dict(assignment=assignment, loads=loads, groups=groups, tau=tau,
                thresholds=thresholds, initial=initial, final=current, trace=trace)
