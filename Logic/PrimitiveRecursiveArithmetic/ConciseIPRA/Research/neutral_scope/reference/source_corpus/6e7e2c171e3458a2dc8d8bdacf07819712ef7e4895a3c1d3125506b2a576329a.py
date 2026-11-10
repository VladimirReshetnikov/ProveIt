"""Finite illustration of the explicitly proved N^2 separator.

This checks witnesses, not the induction schema or a universal theorem.
The mathematical proof is in progressive_boolean_obstruction.tex.
"""
import itertools
import json

ZERO = (0, 0)
ONE = (1, 1)
MIXED = (0, 1)


def successor(pair):
    return tuple(value + 1 for value in pair)


def equation(control, outer, inner):
    return all((int(y == 0) if t == 0 else z) == 0
               for t, y, z in zip(control, outer, inner))


def inner_progress(control, outer, samples):
    return all(not equation(control, outer, inner)
               or equation(control, outer, successor(inner))
               for inner in samples)


def outer_progress(control, samples):
    return all(not inner_progress(control, outer, samples)
               or inner_progress(control, successor(outer), samples)
               for outer in samples)


samples = list(itertools.product(range(5), repeat=2))
results = {
    'sample_box': '0 <= coordinate <= 4; successors evaluated directly',
    'F_zero_on_sample': outer_progress(ZERO, samples),
    'F_one_on_sample': outer_progress(ONE, samples),
    'F_mixed_on_sample': outer_progress(MIXED, samples),
    'inner_at_zero': inner_progress(MIXED, ZERO, samples),
    'inner_at_successor_zero': inner_progress(MIXED, ONE, samples),
    'equation_after_outer_step_before_inner_step': equation(MIXED, ONE, ZERO),
    'equation_after_both_steps': equation(MIXED, ONE, ONE),
    'status': 'Finite illustration only; see written universal proof.'
}
assert results['F_zero_on_sample'] and results['F_one_on_sample']
assert not results['F_mixed_on_sample']
assert results['inner_at_zero'] and not results['inner_at_successor_zero']
assert results['equation_after_outer_step_before_inner_step']
assert not results['equation_after_both_steps']
print(json.dumps(results, indent=2))
