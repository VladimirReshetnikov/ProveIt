#!/usr/bin/env python3
"""Decide tag halting for appendants that are powers of a common word."""
from collections import deque
from itertools import product
from math import gcd
from pathlib import Path
import json


def words(max_length, nonempty=False):
    return [tuple(w) for n in range(int(nonempty), max_length + 1)
            for w in product((0, 1), repeat=n)]


def decide(w, beta, v, exponents):
    assert beta >= 1 and v and all(k >= 0 for k in exponents)
    m = len(v)
    j0 = (len(w) + beta - 1) // beta

    def symbol(j):
        pos = beta*j
        return w[pos] if pos < len(w) else v[(pos-len(w)) % m]

    length = len(w)
    for j in range(j0):
        if length < beta:
            return j, 'prefix', None
        length += m*exponents[symbol(j)] - beta
    period = m // gcd(m, beta)
    increments = [m*exponents[symbol(j0+r)]-beta for r in range(period)]
    partial = [0]
    for d in increments:
        partial.append(partial[-1]+d)
    drift = partial[-1]
    if drift >= 0:
        for r in range(period):
            if length + partial[r] < beta:
                return j0+r, 'first_period', drift
        return None, 'nonnegative_drift', drift
    candidates = []
    for r in range(period):
        k = max(0, (length+partial[r]-beta)//(-drift)+1)
        candidates.append(period*k+r)
    return j0+min(candidates), 'negative_drift', drift


def execute(w, beta, appendants, limit):
    queue = deque(w)
    for j in range(limit+1):
        if len(queue) < beta:
            return j
        if j == limit:
            return None
        symbol = queue[0]
        for _ in range(beta):
            queue.popleft()
        queue.extend(appendants[symbol])
    raise AssertionError('unreachable')


def verify():
    cases = halts = nonhalting = zero_drift = negative_drift = 0
    max_halt = 0
    branches = {}
    for v in words(3, nonempty=True):
        for exponents in product(range(3), repeat=2):
            appendants = tuple(v*k for k in exponents)
            for beta in range(1, 5):
                for w in words(3):
                    result, branch, drift = decide(w, beta, v, exponents)
                    branches[branch] = branches.get(branch, 0)+1
                    limit = result if result is not None else 100
                    observed = execute(w, beta, appendants, limit)
                    assert observed == result
                    if result is None:
                        nonhalting += 1
                        zero_drift += drift == 0
                    else:
                        halts += 1
                        max_halt = max(max_halt, result)
                        negative_drift += branch == 'negative_drift'
                    cases += 1
    examples = []
    for w, beta, v, powers in [((1,), 1, (1, 0), (0, 1)),
                              ((1, 0, 0), 2, (1, 0, 0), (0, 1)),
                              ((0, 1, 1, 0), 2, (1,), (0, 0))]:
        result, branch, drift = decide(w, beta, v, powers)
        assert execute(w, beta, tuple(v*k for k in powers),
                       result if result is not None else 200) == result
        examples.append(dict(initial=''.join(map(str, w)), beta=beta,
            common_word=''.join(map(str, v)), powers=powers,
            halting_time=result, branch=branch, drift=drift))
    return dict(
        status='PASS_COMMON_WORD_TAG_HALTING_DECISION',
        cases=cases, exact_predicted_halts=halts,
        predicted_nonhalting_finite_regressions=nonhalting,
        nonhalting_regression_steps=100,
        zero_drift_nonhalting_cases=zero_drift,
        negative_drift_exact_halts=negative_drift,
        maximum_finite_halting_time=max_halt, decision_branches=branches,
        deletion_numbers=[1, 2, 3, 4], common_word_max_length=3,
        exponent_range=[0, 1, 2], initial_max_length=3, examples=examples,
        proof='../1980/EXPLORATION_COMMON_WORD_TAG_HALTING.md',
        scope='Exact general decision algorithm proved in the note. Finite runs support the implementation; absence of later halting uses the periodic-drift proof. No result for arbitrary tag appendants or new universal operation count is claimed.')


if __name__ == '__main__':
    result = verify()
    Path(__file__).with_suffix('.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result['status'])
    print({k: v for k, v in result.items() if k not in ('proof', 'scope')})
