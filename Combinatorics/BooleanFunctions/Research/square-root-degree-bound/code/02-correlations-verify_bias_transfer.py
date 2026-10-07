#!/usr/bin/env python3
"""Exact finite regression examples for the bias-transfer argument.

This script is not a proof of the general theorem. It checks all eight
choices of adjacent quantile gadgets for two three-variable Boolean
functions by independently evaluating all 2**12 source assignments.
All arithmetic is rational, including normalized biased Fourier
coefficients: the selected source and target Bernoulli biases have
rational standard deviations. The source bias is common within each
four-bit block and differs between blocks.

The two examples deliberately exercise positive, negative, and zero
target derivatives, nontrivial tie splitting, and correlation between a
gadget's mean and its singleton sum. Every conditional-expectation
step is compared with an independent average of truth-table results.
"""
from fractions import Fraction as F
from itertools import product
from math import isqrt, lcm, prod
import json

SIGN_VALUES = (-1, 1)


def rational_sqrt(x):
    a, b = isqrt(x.numerator), isqrt(x.denominator)
    assert a * a == x.numerator and b * b == x.denominator
    return F(a, b)


def sigma(p):
    return 2 * rational_sqrt(p * (1 - p))


def point_probability(x, biases):
    return prod((p if bit == 1 else 1 - p for bit, p in zip(x, biases)), start=F(1))


def truth_singletons(table, biases):
    """Direct biased Fourier definition, independent of polynomial code."""
    n = len(biases)
    values = [F(0)] * n
    mean = F(0)
    for x, fx in table.items():
        probability = point_probability(x, biases)
        mean += probability * fx
        for i, (bit, p) in enumerate(zip(x, biases)):
            values[i] += probability * fx * (bit - (2 * p - 1)) / sigma(p)
    return mean, values


def multilinear_coefficients(table):
    n = len(next(iter(table)))
    return {
        mask: F(sum(fx * prod((x[i] for i in range(n) if mask >> i & 1), start=1)
                    for x, fx in table.items()), 2 ** n)
        for mask in range(2 ** n)
    }


def polynomial_value(coefficients, means):
    return sum((coefficient * prod((means[j] for j in range(len(means))
                                   if mask >> j & 1), start=F(1))
                for mask, coefficient in coefficients.items()), F(0))


def derivative(coefficients, i, means):
    return sum((coefficient * prod((means[j] for j in range(len(means))
                                   if j != i and mask >> j & 1), start=F(1))
                for mask, coefficient in coefficients.items() if mask >> i & 1), F(0))


def function_degree(values):
    """Unnormalized integer Walsh transform of a complete sign truth table."""
    transformed = list(values)
    width = 1
    while width < len(transformed):
        for offset in range(0, len(transformed), 2 * width):
            for j in range(offset, offset + width):
                u, v = transformed[j], transformed[j + width]
                transformed[j], transformed[j + width] = u + v, u - v
        width *= 2
    return max((mask.bit_count() for mask, coefficient in enumerate(transformed)
                if coefficient), default=0)


def quantile_pair(m, source_p, target_q, orientation):
    points = list(product(SIGN_VALUES, repeat=m))
    # Equal Hamming-score strings are ordered individually, not merged.
    order = sorted(range(len(points)), key=lambda k: (-orientation * sum(points[k]), points[k]))
    probabilities = [point_probability(x, [source_p] * m) for x in points]
    cumulative = F(0)
    cutoff = 0
    while cutoff < len(points) and cumulative + probabilities[order[cutoff]] < target_q:
        cumulative += probabilities[order[cutoff]]
        cutoff += 1
    assert cutoff < len(points)
    probabilities_of_events = (cumulative, cumulative + probabilities[order[cutoff]])
    assert probabilities_of_events[0] <= target_q <= probabilities_of_events[1]
    gap = probabilities_of_events[1] - probabilities_of_events[0]
    assert gap <= max(source_p, 1 - source_p) ** m
    high_weight = (target_q - probabilities_of_events[0]) / gap
    weights = (1 - high_weight, high_weight)
    assert all(weight > 0 for weight in weights)  # Both choices are exercised here.
    gadgets = []
    for how_many, event_probability in zip((cutoff, cutoff + 1), probabilities_of_events):
        included = set(order[:how_many])
        outputs = [1 if k in included else -1 for k in range(len(points))]
        mean, singletons = truth_singletons(dict(zip(points, outputs)), [source_p] * m)
        singleton_sum = sum(singletons, F(0))
        assert mean == 2 * event_probability - 1
        assert orientation * singleton_sum > 0
        assert 0 < event_probability < 1
        # Each pair consists of monotone events with the selected orientation.
        for k, x in enumerate(points):
            for j in range(m):
                if x[j] == -1:
                    y = x[:j] + (1,) + x[j + 1:]
                    assert orientation * (outputs[points.index(y)] - outputs[k]) >= 0
        gadgets.append({
            'outputs': outputs, 'probability': event_probability,
            'mean': mean, 'singletons': singletons, 'A': singleton_sum,
            'degree': function_degree(outputs), 'prefix_size': how_many,
        })
    average_mean = sum((w * g['mean'] for w, g in zip(weights, gadgets)), F(0))
    average_A = sum((w * g['A'] for w, g in zip(weights, gadgets)), F(0))
    covariance = sum((w * g['mean'] * g['A'] for w, g in zip(weights, gadgets)), F(0)) - average_mean * average_A
    assert average_mean == 2 * target_q - 1
    assert covariance != 0
    return {
        'source_p': source_p, 'target_q': target_q, 'orientation': orientation,
        'weights': weights, 'gadgets': gadgets, 'mean': average_mean,
        'average_A': average_A, 'mean_A_covariance': covariance,
        'boundary_weight': sum(points[order[cutoff]]), 'atom_gap': gap,
    }


def prepare_source_grid(m, source_ps):
    """Use a common integer denominator for independent truth-table sums."""
    n = len(source_ps)
    block_points = list(product(SIGN_VALUES, repeat=m))
    source_biases = [p for p in source_ps for _ in range(m)]
    total_probability_denominator = prod(p.denominator for p in source_biases)
    standardized = [((F(bit) - (2 * p - 1)) / sigma(p))
                    for p in source_biases for bit in SIGN_VALUES]
    phi_denominator = lcm(*(x.denominator for x in standardized))
    rows = []
    for block_indices in product(range(2 ** m), repeat=n):
        x = tuple(bit for k in block_indices for bit in block_points[k])
        weight = prod(p.numerator if bit == 1 else p.denominator - p.numerator
                      for bit, p in zip(x, source_biases))
        phi_numerators = [int((F(bit) - (2 * p - 1)) / sigma(p) * phi_denominator)
                          for bit, p in zip(x, source_biases)]
        rows.append((block_indices, weight, phi_numerators))
    assert sum(row[1] for row in rows) == total_probability_denominator
    return rows, total_probability_denominator, phi_denominator


def oriented_majority(x):
    return 1 if x[0] - x[1] + x[2] > 0 else -1


def conditional_selector(x):
    return x[0] if x[2] == 1 else -x[1]


def run_example(name, outer_function):
    n, m = 3, 4
    targets = (F(1, 5), F(4, 5), F(1, 2))
    sources = (F(1, 2), F(1, 5), F(4, 5))
    table = {x: outer_function(x) for x in product(SIGN_VALUES, repeat=n)}
    coefficients = multilinear_coefficients(table)
    outer_degree = max(mask.bit_count() for mask, value in coefficients.items() if value)
    target_means = [2 * q - 1 for q in targets]
    target_mean, target_coefficients = truth_singletons(table, targets)
    target_derivatives = [derivative(coefficients, i, target_means) for i in range(n)]
    assert target_mean == polynomial_value(coefficients, target_means)
    assert target_coefficients == [sigma(q) * d for q, d in zip(targets, target_derivatives)]
    assert any(d > 0 for d in target_derivatives)
    assert any(d < 0 for d in target_derivatives)
    pairs = [quantile_pair(m, p, q, 1 if d >= 0 else -1)
             for p, q, d in zip(sources, targets, target_derivatives)]
    rows, probability_denominator, phi_denominator = prepare_source_grid(m, sources)
    results = {}
    for choices in product((0, 1), repeat=n):
        selected = [pair['gadgets'][choice] for pair, choice in zip(pairs, choices)]
        means = [g['mean'] for g in selected]
        counts = [0] * (n * m)
        mean_numerator = 0
        composed_values = []
        for indices, weight, phi_numerators in rows:
            y = tuple(g['outputs'][index] for g, index in zip(selected, indices))
            value = table[y]
            composed_values.append(value)
            mean_numerator += weight * value
            for j, phi in enumerate(phi_numerators):
                counts[j] += weight * value * phi
        direct_coefficients = [F(count, probability_denominator * phi_denominator) for count in counts]
        direct_mean = F(mean_numerator, probability_denominator)
        direct_S = sum(direct_coefficients, F(0))
        current_derivatives = [derivative(coefficients, i, means) for i in range(n)]
        chain_coefficients = [current_derivatives[i] * a
                              for i, g in enumerate(selected) for a in g['singletons']]
        chain_S = sum((g['A'] * d for g, d in zip(selected, current_derivatives)), F(0))
        assert direct_coefficients == chain_coefficients
        assert direct_mean == polynomial_value(coefficients, means)
        assert direct_S == chain_S
        degree = function_degree(composed_values)
        assert degree <= m * outer_degree
        choice_weight = prod((pair['weights'][c] for pair, c in zip(pairs, choices)), start=F(1))
        results[choices] = {
            'weight': choice_weight, 'direct_signed_singleton_sum': direct_S,
            'direct_singletons': direct_coefficients, 'degree': degree,
            'mean': direct_mean, 'block_means': means,
            'block_singleton_sums': [g['A'] for g in selected],
        }
    average = sum((r['weight'] * r['direct_signed_singleton_sum'] for r in results.values()), F(0))
    theoretical_average = sum((pair['average_A'] * d for pair, d in zip(pairs, target_derivatives)), F(0))
    assert sum((r['weight'] for r in results.values()), F(0)) == 1
    assert average == theoretical_average
    assert average > 0

    def conditional_truth(prefix):
        matching = [(c, r) for c, r in results.items() if c[:len(prefix)] == prefix]
        mass = sum((r['weight'] for _, r in matching), F(0))
        return sum((r['weight'] * r['direct_signed_singleton_sum'] for _, r in matching), F(0)) / mass

    def conditional_formula(prefix):
        means = [pair['gadgets'][prefix[i]]['mean'] if i < len(prefix) else pair['mean']
                 for i, pair in enumerate(pairs)]
        As = [pair['gadgets'][prefix[i]]['A'] if i < len(prefix) else pair['average_A']
              for i, pair in enumerate(pairs)]
        return sum((a * derivative(coefficients, i, means) for i, a in enumerate(As)), F(0))

    for length in range(n + 1):
        for prefix in product((0, 1), repeat=length):
            assert conditional_truth(prefix) == conditional_formula(prefix)
    prefix = ()
    greedy = []
    previous = average
    for i in range(n):
        branch_values = [conditional_formula(prefix + (choice,)) for choice in (0, 1)]
        choice = 0 if branch_values[0] >= branch_values[1] else 1
        prefix += (choice,)
        current = branch_values[choice]
        assert current >= previous
        greedy.append({'step': i + 1, 'branch_values': branch_values,
                       'selected': choice, 'conditional_expectation': current})
        previous = current
    final = results[prefix]['direct_signed_singleton_sum']
    assert final == previous and final >= average
    target_L1 = sum((abs(c) for c in target_coefficients), F(0))
    individual_positive_floor = min(
        min(pair['orientation'] * g['A'] for g in pair['gadgets']) / sigma(q)
        for pair, q in zip(pairs, targets))
    assert average >= individual_positive_floor * target_L1
    assert all(pair['mean_A_covariance'] != 0 for pair in pairs)
    return {
        'name': name,
        'target_biases': targets, 'source_block_biases': sources,
        'block_size': m, 'source_bits': n * m,
        'source_assignments_per_gadget_choice': len(rows),
        'gadget_choice_count': len(results),
        'outer_degree': outer_degree,
        'target_derivatives': target_derivatives,
        'target_normalized_singletons': target_coefficients,
        'target_L1': target_L1,
        'gadget_pairs': [{k: v for k, v in pair.items() if k != 'gadgets'} | {
            'gadgets': [{k: v for k, v in g.items() if k != 'outputs'} for g in pair['gadgets']]
        } for pair in pairs],
        'all_choices': [{'choices': choices, **r} for choices, r in results.items()],
        'average_signed_singleton_sum': average,
        'formula_average_signed_singleton_sum': theoretical_average,
        'actual_gadget_floor': individual_positive_floor,
        'actual_gadget_floor_times_target_L1': individual_positive_floor * target_L1,
        'greedy_steps': greedy,
        'greedy_choices': prefix,
        'greedy_signed_singleton_sum': final,
        'greedy_at_least_average': final >= average,
        'all_chain_and_conditional_expectation_checks_passed': True,
    }


def to_json(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): to_json(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [to_json(v) for v in value]
    return value


if __name__ == '__main__':
    examples = [run_example('oriented_majority', oriented_majority),
                run_example('conditional_selector', conditional_selector)]
    assert examples[0]['target_derivatives'] == [F(1, 2), F(-1, 2), F(8, 25)]
    assert examples[0]['average_signed_singleton_sum'] == F(41109, 25000)
    assert examples[1]['target_derivatives'] == [F(1, 2), F(-1, 2), F(0)]
    assert examples[0]['greedy_choices'] == (1, 0, 1)
    print(json.dumps(to_json({
        'arithmetic': 'exact rational; Python standard library',
        'scope': 'finite regression examples, not a proof of the universal theorem',
        'examples': examples,
    }), indent=2))
