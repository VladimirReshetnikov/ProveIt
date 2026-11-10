"""Finite numerical audit of the B + equality-bit bounded simulation macros.

This executes the actual displayed macros, not their claimed closed forms.
Primitive numerical operations in the tested grammar are ZERO, EQ and B:
    B_h(0) = 1 + h(0, 0)
    B_h(n+1) = h(n, B_h(n)).
Successor and every other tested numerical operation are macros built from B.
Python arithmetic in the separate oracle section is independent reference code.
Python loops, cache keys, counters, assertions and bookkeeping are metatheoretic
interpreter/test infrastructure; they are not added numerical term primitives.

The callbacks supplied to B describe fixed finite bodies with passive numerical
parameters. No universal object-level evaluator, external initialized recursor,
raw addition, raw multiplication, minimum, or predecessor is used in the macro
section. Caching reuses previously evaluated pure macro applications, never a
closed-form arithmetic replacement. This is finite testing, not proof checking,
not a metatheorem formalization, and not evidence about arbitrary nonstandard
models or induction preservation.
"""
from functools import cache
import argparse
import json
from pathlib import Path
import platform
import sys
import time


class EvaluationBudgetExceeded(RuntimeError):
    pass


STATS = {'B_calls': 0, 'B_transitions': 0, 'body_calls': 0,
         'largest_counter': 0, 'largest_state': 0}
CASE_START = 0
CASE_LIMIT = 2_000_000


def B(n, body):
    """The sole recursion primitive, interpreted literally, including its seed."""
    if type(n) is not int or n < 0:
        raise ValueError('B requires a natural counter')
    STATS['B_calls'] += 1
    STATS['largest_counter'] = max(STATS['largest_counter'], n)
    STATS['body_calls'] += 1
    state = 1 + body(0, 0)  # The successor in the primitive B seed equation.
    STATS['largest_state'] = max(STATS['largest_state'], state)
    for old_counter in range(n):
        STATS['B_transitions'] += 1
        if STATS['B_transitions'] - CASE_START > CASE_LIMIT:
            raise EvaluationBudgetExceeded('per-case B-transition budget')
        STATS['body_calls'] += 1
        state = body(old_counter, state)
        if type(state) is not int or state < 0:
            raise ValueError('A numerical update returned a non-natural value')
        STATS['largest_state'] = max(STATS['largest_state'], state)
    return state


def EQ(a, b):
    """The allowed primitive numerical equality characteristic."""
    return int(a == b)


# BEGIN MACRO SECTION: numerical definitions use only B, EQ and earlier macros.
@cache
def S(x):
    return B(0, lambda u, v: x)


@cache
def D(n, a):
    return B(n, lambda u, v: a)


@cache
def W(n):
    return B(n, lambda u, v: u)


@cache
def P(n):
    return W(D(n, n))


@cache
def Z(n):
    return D(n, 0)


@cache
def G(n, a):
    return P(P(B(a, lambda u, v: D(Z(n), v))))


def L(n, body):
    """Inherited zero-start macro, evaluated through B and G, not a seed-0 loop."""
    return B(S(n), lambda r, s: G(r, body(P(r), s)))


@cache
def J(a, bit):
    return B(Z(bit), lambda u, v: a)


@cache
def occurrence_count(n, y):
    return L(n, lambda r, v: J(v, EQ(r, y)))


@cache
def leq(x, y):
    return occurrence_count(S(y), x)


@cache
def difference(x, y):
    return L(x, lambda u, v: J(v, occurrence_count(S(u), y)))


@cache
def minimum(a, b):
    return difference(a, difference(a, b))


@cache
def double(b):
    return L(b, lambda u, v: S(S(v)))


@cache
def bounded_add(bound, a, c):
    """Exact a+c when both a and c are at most the supplied bound."""
    return difference(difference(double(bound), difference(bound, a)),
                      difference(bound, c))


@cache
def selector(bound, control, a, c):
    """Choose a at control zero, c otherwise, on a,c <= bound."""
    return bounded_add(bound, G(Z(control), a), G(control, c))


@cache
def capped_sum(bound, a, c):
    return minimum(bounded_add(bound, minimum(a, bound), minimum(c, bound)),
                   bound)


@cache
def capped_product(bound, a, c):
    # This is a B-term for min(a*c,bound), not unrestricted multiplication.
    return L(a, lambda u, v: capped_sum(bound, v, c))


@cache
def clipped_recursion(n, a, bound, body):
    """New R_b macro. L is itself expanded into its tied-seed B construction."""
    return L(S(n), lambda r, s: selector(
        bound, r, minimum(a, bound), minimum(body(P(r), s), bound)))
# END MACRO SECTION.


def build_updates(bound):
    """Fixed B-term update bodies, with their separate arithmetic oracles.

    Sum and product inputs are capped inside their representable B-term bodies.
    After the outer cap these induce exactly the ordinary sum and product
    recurrences. In particular, no unrestricted binary product term is assumed.
    """
    one = S(0)
    return {
        'counter_plus_state': (
            lambda n, state: bounded_add(bound, minimum(n, bound),
                                         minimum(state, bound)),
            lambda n, state: n + state),
        'successor_counter_times_state': (
            lambda n, state: capped_product(bound, S(n), state),
            lambda n, state: (n + 1) * state),
        'conditional_step': (
            lambda n, state: selector(
                bound, EQ(n, one), minimum(P(state), bound),
                minimum(S(S(state)), bound)),
            lambda n, state: state + 2 if n == 1 else max(state - 1, 0)),
    }


def oracle_recursion(n, a, bound, update):
    """Independent ordinary arithmetic oracle; never called by a B macro."""
    state = min(a, bound)
    for old_counter in range(n):
        state = min(update(old_counter, state), bound)
    return state


def run():
    global CASE_START
    started = time.perf_counter()
    rows = []
    groups = {}

    def check(group, arguments, compute, expected):
        global CASE_START
        CASE_START = STATS['B_transitions']
        before = dict(STATS)
        try:
            actual = compute()
            status = 'pass' if actual == expected else 'fail'
            row = dict(group=group, arguments=arguments, status=status,
                       actual=actual, expected=expected)
        except EvaluationBudgetExceeded as exc:
            row = dict(group=group, arguments=arguments, status='skipped',
                       reason=str(exc), expected=expected)
        row['B_transitions'] = STATS['B_transitions'] - before['B_transitions']
        row['B_calls'] = STATS['B_calls'] - before['B_calls']
        rows.append(row)
        groups.setdefault(group, {'pass': 0, 'fail': 0, 'skipped': 0})[row['status']] += 1
        if row['status'] == 'fail':
            raise AssertionError(row)

    for n in range(9):
        check('successor', [n], lambda n=n: S(n), n + 1)
        check('predecessor', [n], lambda n=n: P(n), max(n - 1, 0))
        check('zero_characteristic', [n], lambda n=n: Z(n), int(n == 0))
    for control in range(5):
        for a in range(7):
            check('gate', [control, a], lambda control=control, a=a: G(control, a),
                  a if control else 0)
    zero_start_bodies = {
        'zero': (lambda n, state: 0, lambda n: 0),
        'successor': (lambda n, state: S(state), lambda n: n),
        'counter': (lambda n, state: n, lambda n: max(n - 1, 0)),
        'single_pulse': (lambda n, state: J(state, EQ(n, S(S(0)))),
                         lambda n: int(n > 2)),
    }
    for name, (body, oracle) in zero_start_bodies.items():
        for n in range(7):
            check('zero_start_' + name, [n], lambda n=n, body=body: L(n, body),
                  oracle(n))
    for a in range(7):
        for bit in (0, 1):
            check('conditional_increment', [a, bit], lambda a=a, bit=bit: J(a, bit),
                  a + bit)
    for x in range(6):
        for y in range(6):
            check('less_or_equal', [x, y], lambda x=x, y=y: leq(x, y), int(x <= y))
            check('difference', [x, y], lambda x=x, y=y: difference(x, y), max(x - y, 0))
            check('minimum', [x, y], lambda x=x, y=y: minimum(x, y), min(x, y))
    for bound in range(5):
        check('doubling', [bound], lambda bound=bound: double(bound), 2 * bound)
        for a in range(bound + 1):
            for c in range(bound + 1):
                check('bounded_addition', [bound, a, c],
                      lambda bound=bound, a=a, c=c: bounded_add(bound, a, c), a + c)
    for bound in range(4):
        for control in range(3):
            for a in range(bound + 1):
                for c in range(bound + 1):
                    check('bounded_selector', [bound, control, a, c],
                          lambda bound=bound, control=control, a=a, c=c:
                              selector(bound, control, a, c), c if control else a)
        for a in range(5):
            for c in range(5):
                check('capped_sum', [bound, a, c],
                      lambda bound=bound, a=a, c=c: capped_sum(bound, a, c),
                      min(a + c, bound))
                check('capped_product', [bound, a, c],
                      lambda bound=bound, a=a, c=c: capped_product(bound, a, c),
                      min(a * c, bound))
        for name, (body, oracle) in build_updates(bound).items():
            for a in range(5):
                for n in range(5):
                    expected = oracle_recursion(n, a, bound, oracle)
                    check('clipped_recursion_' + name, [n, a, bound],
                          lambda n=n, a=a, bound=bound, body=body:
                              clipped_recursion(n, a, bound, body), expected)
                    if n:
                        check('clipped_recurrence_' + name, [n, a, bound],
                              lambda n=n, a=a, bound=bound, body=body:
                                  clipped_recursion(n, a, bound, body),
                              min(body(n - 1, clipped_recursion(n - 1, a, bound, body)),
                                  bound))
    cached = [S, D, W, P, Z, G, J, occurrence_count, leq, difference,
              minimum, double, bounded_add, selector, capped_sum, capped_product,
              clipped_recursion]
    return {
        'scope': 'Finite standard-natural-number evaluation; not proof verification.',
        'python': platform.python_version(),
        'primitive_basis': ['zero', 'numerical equality bit', 'tied-seed B'],
        'budget_per_case_B_transitions': CASE_LIMIT,
        'test_ranges': {
            'S_P_Z_inputs': '0..8', 'gate_control': '0..4', 'gate_value': '0..6',
            'L_counters': '0..6', 'J_value': '0..6', 'J_bits': [0, 1],
            'comparison_difference_minimum_inputs': '0..5',
            'addition_bounds': '0..4', 'addition_inputs': '0..bound',
            'selector_bounds': '0..3', 'selector_controls': '0..2',
            'selector_inputs': '0..bound', 'capped_sum_product_bounds': '0..3',
            'capped_sum_product_inputs': '0..4', 'R_bounds': '0..3',
            'R_seeds': '0..4', 'R_counters': '0..4'},
        'checks': len(rows), 'passed': sum(r['status'] == 'pass' for r in rows),
        'failed': sum(r['status'] == 'fail' for r in rows),
        'skipped': sum(r['status'] == 'skipped' for r in rows),
        'groups': groups, 'interpreter_statistics': dict(STATS),
        'cache_statistics': {f.__name__: f.cache_info()._asdict() for f in cached},
        'elapsed_seconds': round(time.perf_counter() - started, 6),
        'rows': rows,
        'limitations': [
            'Only the explicitly listed finite standard-number ranges were evaluated.',
            'No induction, whole-domain interpretation composite, or soundness metatheorem was machine checked.',
            'Product is implemented by a capped B-term; its outer-capped recurrence equals ordinary product.',
            'No search for new axioms or proof-checker-size claim is made by these tests.'
        ]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('bounded_simulation_results.json'))
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    summary = {k: result[k] for k in ('scope', 'checks', 'passed', 'failed', 'skipped',
                                     'interpreter_statistics', 'elapsed_seconds')}
    print(json.dumps(summary, indent=2))
    if result['failed'] or result['skipped']:
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
