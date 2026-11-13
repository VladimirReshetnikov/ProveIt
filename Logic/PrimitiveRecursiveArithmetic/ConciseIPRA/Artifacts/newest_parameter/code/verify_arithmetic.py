#!/usr/bin/env python3
"""Arithmetic regressions for the parameter-only iPRA presentation.

This is NOT a proof-assistant formalization of the bi-interpretation.
Part 1 evaluates the displayed finite scalar-iterator definitions literally,
with memoized prefixes for three fixed iterators. No closed-form predecessor,
parity, remainder, ramp, or comparator formula is used in evaluation.
Part 2 checks symbolic zero/successor branches of the critical equational
case lemmas by replaying first-order rewrite traces. Its fixed rewrite
schemas are defining equations of the abbreviations in the paper.
"""

from functools import lru_cache
import json
from pathlib import Path


SUCCESSOR_CALLS = 0
ITERATION_STEPS = 0
PREFIXES = {}


def S(n):
    global SUCCESSOR_CALLS
    SUCCESSOR_CALLS += 1
    return n + 1


def I(n, a, step):
    global ITERATION_STEPS
    for _ in range(n):
        a = step(a)
        ITERATION_STEPS += 1
    return a


def fixed_iterator(key, n, a, step):
    """Cache a prefix, preserving each literal scalar update."""
    global ITERATION_STEPS
    values = PREFIXES.setdefault(key, [a])
    while len(values) <= n:
        values.append(step(values[-1]))
        ITERATION_STEPS += 1
    return values[n]


def C(n, a, b):
    return I(n, a, lambda _: b)


@lru_cache(None)
def Z(n):
    return C(n, 1, 0)


def add(a, b):
    return I(b, a, S)


def twice(a):
    return add(a, a)


def thrice(a):
    return add(add(a, a), a)


def N(n):
    return fixed_iterator('N', n, 0, Z)


def j(u):
    return add(Z(u), twice(N(u)))


def M(n):
    return fixed_iterator('M', n, 0, j)


def G(n):
    return fixed_iterator('G', n, 0, lambda u: add(add(u, M(u)), 1))


@lru_cache(None)
def H(u):
    return C(N(u), G(u), u)


@lru_cache(None)
def E(x):
    return I(x, 1, twice)


@lru_cache(None)
def L(x, y):
    return N(I(y, E(x), H))


def W(t, m):
    return I(t, 0, lambda u: C(L(S(u), m), u, S(u)))


def P(m):
    return I(m, 0, lambda u: C(L(S(S(u)), m), u, S(u)))


def numerical_checks():
    count = 0

    def equal(a, b):
        nonlocal count
        assert a == b, (a, b)
        count += 1

    for n in range(13):
        equal(add(N(n), Z(N(n))), 1)
        equal(Z(Z(N(n))), N(n))
        equal(N(add(n, 2)), N(n))
        equal(N(twice(n)), 0)
        equal(N(S(twice(n))), 1)
        equal(N(thrice(n)), N(n))
        equal(M(G(n)), N(n))
        equal(G(twice(n)), thrice(n))
        equal(G(thrice(n)), add(thrice(G(n)), N(n)))
        equal(H(twice(n)), thrice(n))
        equal(H(thrice(n)), thrice(H(n)))
    for g in range(8):
        for v in range(8):
            equal(M(add(add(g, Z(v)), 1)), C(v, j(j(M(g))), j(M(g))))
            equal(C(v, j(j(Z(v))), j(Z(v))), Z(Z(v)))
    for x in range(7):
        equal(L(0, x), 1)
        equal(L(S(x), 0), 0)
        equal(L(S(x), x), 0)
        equal(W(x, x), x)
        equal(W(S(x), x), x)
        for y in range(7):
            equal(L(S(x), S(y)), L(x, y))
            equal(W(S(x), S(y)), S(W(x, y)))
    values = [P(n) for n in range(8)]
    equal(values[0], 0)
    for n in range(7):
        equal(values[n + 1], n)
    return {'equalities_checked': count, 'predecessor_inputs': list(range(8)),
            'predecessor_outputs': values, 'iteration_steps': ITERATION_STEPS,
            'successor_calls': SUCCESSOR_CALLS,
            'memoized_prefix_lengths': {k: len(v) for k, v in PREFIXES.items()}}


# A term is a variable string, integer 0, or a list [function, arguments...].
def s(x):
    return ['S', x]


def plus(a, b):
    return ['add', a, b]


def c(n, a, b):
    return ['C', n, a, b]


def z(n):
    return ['Z', n]


def nf(n):
    return ['N', n]


def jf(n):
    return ['j', n]


def mf(n):
    return ['M', n]


one = s(0)
# These are all definitional instances of I(0,a;h)=a and
# I(Sn,a;h)=h(I(n,a;h)), after expanding the displayed abbreviations.
RULES = {
    'add_zero': (plus('$a', 0), '$a'),
    'add_succ': (plus('$a', s('$b')), s(plus('$a', '$b'))),
    'select_zero': (c(0, '$a', '$b'), '$a'),
    'select_succ': (c(s('$n'), '$a', '$b'), '$b'),
    'zero_test_zero': (z(0), one),
    'zero_test_succ': (z(s('$n')), 0),
    'parity_zero': (nf(0), 0),
    'parity_succ': (nf(s('$n')), z(nf('$n'))),
    'cycle_zero': (mf(0), 0),
    'cycle_succ': (mf(s('$n')), jf(mf('$n'))),
    'cycle_step_definition': (jf('$n'), plus(z('$n'), plus(nf('$n'), nf('$n')))),
}


def instantiate(term, env):
    if isinstance(term, str):
        return env.get(term, term)
    if isinstance(term, list):
        return [term[0]] + [instantiate(x, env) for x in term[1:]]
    return term


def match(pattern, term, env):
    if isinstance(pattern, str) and pattern.startswith('$'):
        if pattern in env:
            return env[pattern] == term
        env[pattern] = term
        return True
    if isinstance(pattern, list):
        return (isinstance(term, list) and len(pattern) == len(term)
                and pattern[0] == term[0]
                and all(match(a, b, env) for a, b in zip(pattern[1:], term[1:])))
    return pattern == term


def root_rewrite(term, rule_name):
    pattern, replacement = RULES[rule_name]
    env = {}
    if not match(pattern, term, env):
        raise ValueError('rewrite pattern does not match')
    return instantiate(replacement, env)


def rewrite_at(term, path, rule_name):
    if not path:
        return root_rewrite(term, rule_name)
    if not isinstance(term, list) or not 1 <= path[0] < len(term):
        raise ValueError('invalid rewrite address')
    result = list(term)
    result[path[0]] = rewrite_at(term[path[0]], path[1:], rule_name)
    return result


def normalize_trace(term, address=()):
    """Untrusted trace generator; every trace is replayed separately."""
    trace = []
    if isinstance(term, list):
        term = list(term)
        for index in range(1, len(term)):
            term[index], child_trace = normalize_trace(term[index], address + (index,))
            trace.extend(child_trace)
    for name in RULES:
        try:
            rewritten = root_rewrite(term, name)
        except ValueError:
            continue
        trace.append({'path': list(address), 'rule': name})
        result, tail = normalize_trace(rewritten, address)
        return result, trace + tail
    return term, trace


def check_equation_certificate(certificate):
    """Small replay checker: a pair of rewrite chains with one endpoint."""
    endpoints = []
    for side in ('lhs', 'rhs'):
        term = certificate[side]
        for step in certificate[side + '_trace']:
            term = rewrite_at(term, step['path'], step['rule'])
        endpoints.append(term)
    if endpoints[0] != endpoints[1]:
        raise ValueError('rewrite chains do not meet')


def symbolic_checks():
    v, g, a, b, cc, d = 'v', 'g', 'a', 'b', 'c', 'd'
    lemmas = [
        ('zero_test_partition', plus(z(v), z(z(v))), one),
        ('triple_zero_test', z(z(z(v))), z(v)),
        ('ramp_shift', mf(plus(plus(g, z(v)), one)),
         c(v, jf(jf(mf(g))), jf(mf(g)))),
        ('ramp_cycle', c(v, jf(jf(z(v))), jf(z(v))), z(z(v))),
        ('selector_addition', c(v, plus(a, b), plus(cc, d)),
         plus(c(v, a, cc), c(v, b, d))),
        ('selector_diagonal_zero', c(v, v, 0), 0),
        ('selector_successor', c(v, s(a), s(b)), s(c(v, a, b))),
    ]
    certificates = []
    for name, lhs, rhs in lemmas:
        for branch, replacement in [('zero', 0), ('successor', s('w'))]:
            left = instantiate(lhs, {'v': replacement})
            right = instantiate(rhs, {'v': replacement})
            _, left_trace = normalize_trace(left)
            _, right_trace = normalize_trace(right)
            cert = {'lemma': name, 'branch': branch, 'lhs': left, 'rhs': right,
                    'lhs_trace': left_trace, 'rhs_trace': right_trace}
            check_equation_certificate(cert)
            certificates.append(cert)
    # Prove that the replay checker rejects a damaged certificate.
    bad = dict(certificates[0])
    bad['rhs'] = s(one)
    bad['rhs_trace'] = []
    try:
        check_equation_certificate(bad)
    except ValueError:
        pass
    else:
        raise AssertionError('damaged symbolic certificate was accepted')
    return certificates


def main():
    output = Path(__file__).resolve().parent.parent / 'evidence'
    output.mkdir(exist_ok=True)
    certs = symbolic_checks()
    numeric = numerical_checks()
    summary = {
        'status': 'PASS',
        'scope': 'Finite direct evaluations and symbolic equation-case branches only; '
                 'not a formal verification of the full arithmetic or bi-interpretation.',
        'symbolic_case_lemmas': len(certs) // 2,
        'symbolic_branches': len(certs),
        'symbolic_rewrite_steps': sum(len(c['lhs_trace']) + len(c['rhs_trace']) for c in certs),
        'damaged_symbolic_certificate_rejected': True,
        'numeric': numeric,
    }
    (output / 'arithmetic_certificates.json').write_text(json.dumps(certs, indent=2) + '\n')
    (output / 'arithmetic_verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
