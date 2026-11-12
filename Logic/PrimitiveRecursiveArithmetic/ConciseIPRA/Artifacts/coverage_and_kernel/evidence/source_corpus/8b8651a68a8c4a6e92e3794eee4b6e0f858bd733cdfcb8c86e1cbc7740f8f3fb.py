"""Deterministic finite diagnostics for the positive-iteration zero theorem.

Requires only Python's standard library.  Run:
    python3 verify_zero_profiles.py
    python3 verify_zero_profiles.py --output zero_profiles.json

The evaluator computes natural-number values directly; it never consults
the separately implemented structural zero-profile extractor.  This is a
finite transcription check, not a machine-checked proof of the theorem.

Terms use de Bruijn variable indices: ('v', i), ('z',), ('s', term), and
('r', count, seed, body).  The body sees the old state at index zero;
outer variables are shifted by one.  'r' applies the body count+1 times.
"""

import argparse
from dataclasses import dataclass
from functools import lru_cache
import itertools
import json
from pathlib import Path


ZERO = ('z',)


def var(index):
    return ('v', index)


def succ(term):
    return ('s', term)


def rec(count, seed, body):
    return ('r', count, seed, body)


@lru_cache(maxsize=None)
def terms_of_size(size, arity):
    """Every well-scoped term of this node count, in deterministic order."""
    if size == 1:
        return (ZERO,) + tuple(var(index) for index in range(arity))
    result = [succ(term) for term in terms_of_size(size - 1, arity)]
    for count_size in range(1, size - 2):
        for seed_size in range(1, size - count_size - 1):
            body_size = size - 1 - count_size - seed_size
            if body_size < 1:
                continue
            for count, seed, body in itertools.product(
                terms_of_size(count_size, arity),
                terms_of_size(seed_size, arity),
                terms_of_size(body_size, arity + 1),
            ):
                result.append(rec(count, seed, body))
    return tuple(result)


@dataclass
class Evaluation:
    calls: int = 0
    iterations: int = 0
    maximum_value: int = 0


class BudgetExceeded(Exception):
    pass


def evaluate(term, environment, stats, budget):
    """Direct positive iteration, independent of the profile calculation."""
    stats.calls += 1
    if stats.calls > budget:
        raise BudgetExceeded
    tag = term[0]
    if tag == 'z':
        answer = 0
    elif tag == 'v':
        answer = environment[term[1]]
    elif tag == 's':
        answer = evaluate(term[1], environment, stats, budget) + 1
    elif tag == 'r':
        count = evaluate(term[1], environment, stats, budget)
        answer = evaluate(term[2], environment, stats, budget)
        stats.iterations += count + 1
        if count + 1 > budget - stats.calls:
            raise BudgetExceeded
        for _ in range(count + 1):
            answer = evaluate(term[3], (answer,) + environment, stats, budget)
    else:
        raise ValueError('Unknown term constructor')
    stats.maximum_value = max(stats.maximum_value, answer)
    return answer


def zero_profile(term):
    """None means never zero; a set means its listed variables all vanish."""
    tag = term[0]
    if tag == 'z':
        return frozenset()
    if tag == 'v':
        return frozenset((term[1],))
    if tag == 's':
        return None
    if tag != 'r':
        raise ValueError('Unknown term constructor')
    body = zero_profile(term[3])
    if body is None:
        return None
    passive = frozenset(index - 1 for index in body if index != 0)
    if 0 not in body:
        return passive
    seed = zero_profile(term[2])
    return None if seed is None else passive | seed


def profile_predicts_zero(profile, environment):
    return profile is not None and all(environment[index] == 0 for index in profile)


def node_count(term):
    if term[0] in ('z', 'v'):
        return 1
    return 1 + sum(node_count(child) for child in term[1:])


def iterator_depth(term):
    if term[0] in ('z', 'v'):
        return 0
    return int(term[0] == 'r') + max(iterator_depth(child) for child in term[1:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()

    maximum_size = 7
    arity = 2
    budget = 100000
    environments = tuple(itertools.product(range(4), repeat=arity))
    exhaustive = tuple(
        term
        for size in range(1, maximum_size + 1)
        for term in terms_of_size(size, arity)
    )
    named = {
        'count_reused_as_passive_body_parameter': rec(var(0), ZERO, var(1)),
        'count_reused_in_seed': rec(var(0), var(0), var(0)),
        'nonzero_seed_discarded_by_zero_body': rec(var(0), succ(ZERO), ZERO),
        'nonzero_seed_discarded_by_passive_body': rec(var(0), succ(ZERO), var(2)),
        'binary_unbounded_positive_addition': rec(var(0), var(1), succ(var(0))),
        'nested_body_with_shared_outer_counter': rec(
            var(0), var(1), rec(var(1), var(0), succ(var(0)))
        ),
        'three_nested_bodies_with_captured_parameters': rec(
            var(0), var(1),
            rec(var(1), var(0), rec(var(2), var(0), succ(var(0))))
        ),
        'nested_body_preserves_original_outer_seed': rec(
            var(0), var(1), rec(var(0), var(2), rec(var(0), var(3), var(0)))
        ),
    }
    extra_terms = tuple(term for term in named.values() if term not in exhaustive)
    all_terms = exhaustive + extra_terms
    tested = 0
    skipped = []
    total_calls = 0
    total_iterations = 0
    max_calls = 0
    max_value = 0
    seen_profiles = set()
    for term_index, term in enumerate(all_terms):
        profile = zero_profile(term)
        if profile is not None and len(profile) > 1:
            raise AssertionError(('Singleton-profile strengthening failed', term, profile))
        seen_profiles.add(None if profile is None else tuple(sorted(profile)))
        for environment in environments:
            stats = Evaluation()
            try:
                value = evaluate(term, environment, stats, budget)
            except BudgetExceeded:
                skipped.append({'term_index': term_index, 'valuation': environment})
                continue
            expected = profile_predicts_zero(profile, environment)
            if (value == 0) != expected:
                raise AssertionError((term, environment, value, profile))
            tested += 1
            total_calls += stats.calls
            total_iterations += stats.iterations
            max_calls = max(max_calls, stats.calls)
            max_value = max(max_value, stats.maximum_value)

    unary_samples = tuple(range(3))
    possible_unary_patterns = (
        [False] * 3,
        [True] * 3,
        [value == 0 for value in unary_samples],
    )
    forbidden = {}
    for name, values in {
        'predecessor': [0, 0, 1],
        'zero_test': [1, 0, 0],
    }.items():
        pattern = [value == 0 for value in values]
        if pattern in possible_unary_patterns:
            raise AssertionError('Forbidden unary profile was not separated')
        forbidden[name] = {'arguments': list(unary_samples), 'values': values,
                           'zero_pattern': pattern,
                           'matches_any_permitted_unary_profile': False}
    binary_samples = tuple(itertools.product(range(2), repeat=2))
    addition_values = [left + right for left, right in binary_samples]
    addition_pattern = [value == 0 for value in addition_values]
    permitted_binary_patterns = [
        [False] * len(binary_samples), [True] * len(binary_samples),
        [value[0] == 0 for value in binary_samples],
        [value[1] == 0 for value in binary_samples],
    ]
    if addition_pattern in permitted_binary_patterns:
        raise AssertionError('Addition profile was not separated')
    forbidden['addition'] = {
        'arguments': binary_samples, 'values': addition_values,
        'zero_pattern': addition_pattern,
        'matches_any_permitted_binary_profile': False,
    }

    report = {
        'status': 'PASS' if not skipped else 'INCOMPLETE: evaluation budget skips',
        'scope': 'Finite independent evaluation/profile comparison; not a formal proof.',
        'generator': {
            'free_variables': arity, 'maximum_exhaustive_node_count': maximum_size,
            'exhaustive_terms': len(exhaustive),
            'counts_by_size': {str(size): len(terms_of_size(size, arity))
                               for size in range(1, maximum_size + 1)},
            'additional_distinct_named_terms': len(extra_terms),
            'total_distinct_terms': len(all_terms),
            'maximum_iterator_nesting': max(map(iterator_depth, all_terms)),
        },
        'valuations': {
            'range_per_free_variable': [0, 1, 2, 3],
            'valuations_per_term': len(environments),
            'planned': len(all_terms) * len(environments),
            'tested': tested, 'skipped': len(skipped), 'skip_details': skipped,
        },
        'evaluation': {
            'recursive_call_budget_per_valuation': budget,
            'total_recursive_calls': total_calls,
            'maximum_recursive_calls_per_valuation': max_calls,
            'total_iterator_updates': total_iterations,
            'maximum_observed_numerical_value': max_value,
        },
        'observed_profiles': sorted(
            ['never zero' if profile is None else
             'always zero' if not profile else 'x%d=0' % profile[0]
             for profile in seen_profiles]
        ),
        'named_cases': {
            name: {'term': term, 'node_count': node_count(term),
                   'iterator_nesting': iterator_depth(term),
                   'profile': None if zero_profile(term) is None else sorted(zero_profile(term))}
            for name, term in named.items()
        },
        'explicit_forbidden_profiles': forbidden,
    }
    encoded = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded, encoding='utf-8')
    print(encoded, end='')
    if skipped:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
