#!/usr/bin/env python3
"""Finite checks for the translated residue-EXIT itinerary lemma.

Rules are n=m*q+r -> a*q+b, or EXIT. No cutoff classifies nonhalting.
The full unbounded argument is in EXPLORATION_TRANSLATED_COLLATZ_INPUT.md.
"""
from itertools import product
from pathlib import Path
import json
import random


def trace(program, n, limit):
    modulus = len(program)
    itinerary = []
    states = [n]
    for _ in range(limit + 1):
        quotient, residue = divmod(n, modulus)
        itinerary.append(residue)
        rule = program[residue]
        if rule is None:
            return itinerary, states, True
        if len(states) > limit:
            return itinerary, states, False
        a, b = rule
        n = a * quotient + b
        assert n >= 0
        states.append(n)
    raise AssertionError('unreachable')


def verify():
    rules = [None] + list(product(range(3), repeat=2))
    programs = list(product(rules, repeat=2))
    rng = random.Random(20260914)
    for m in (3, 4, 5, 6):
        for _ in range(30):
            program = [rng.choice(rules) for _ in range(m)]
            program[rng.randrange(m)] = None
            programs.append(tuple(program))
    halted_seeds = paired_runs = polynomial_pairs = skipped_prefixes = 0
    translated_branches = 0
    for program in programs:
        modulus = len(program)
        # a*q+b = (a*n + (m*b-a*r))/m on n=m*q+r.
        translated_branches += sum(rule is not None and modulus * rule[1] - rule[0] * r != 0
                                   for r, rule in enumerate(program))
        for n0 in range(1, 49):
            itinerary, states, halted = trace(program, n0, 40)
            if not halted:
                skipped_prefixes += 1
                continue
            halted_seeds += 1
            t = len(states) - 1
            M = modulus ** (t + 1)
            for z in (1, 2, 5):
                shifted_itinerary, shifted_states, shifted_halted = trace(program, n0 + M * z, t)
                assert shifted_halted and shifted_itinerary == itinerary
                for j, (original, shifted) in enumerate(zip(states, shifted_states)):
                    difference = shifted - original
                    assert difference >= 0 and difference % modulus ** (t + 1 - j) == 0
                paired_runs += 1
        for F in (lambda x: x, lambda x: x*x+1, lambda x: 3*x+7):
            for x0 in range(1, 9):
                n0 = F(x0)
                itinerary, states, halted = trace(program, n0, 40)
                if not halted:
                    continue
                t = len(states)-1
                M = modulus ** (t+1)
                for z in (1, 3):
                    next_n = F(x0+M*z)
                    assert next_n >= n0 and (next_n-n0) % M == 0
                    shifted_itinerary, _, shifted_halted = trace(program, next_n, t)
                    assert shifted_halted and shifted_itinerary == itinerary
                    polynomial_pairs += 1
    point_target_cases = 0
    for n0 in range(1, 4097):
        n = n0
        while n % 2 == 0:
            n //= 2
        reaches_one = n == 1
        assert reaches_one == (n0 & (n0 - 1) == 0)
        point_target_cases += 1
    assert translated_branches > 0 and halted_seeds > 0 and polynomial_pairs > 0
    return {'status': 'PASS_FINITE_CORROBORATION_OF_GENERAL_OBSTRUCTION',
            'proof': '../1980/EXPLORATION_TRANSLATED_COLLATZ_INPUT.md',
            'programs': len(programs), 'nonzero_translated_branches': translated_branches,
            'halting_seeds': halted_seeds, 'preserved_itinerary_pairs': paired_runs,
            'polynomial_loader_pairs': polynomial_pairs, 'point_target_cases': point_target_cases,
            'unclassified_prefixes': skipped_prefixes, 'prefix_limit': 40,
            'scope': 'Residue-only EXIT with nonnegative affine slopes; point-target example lies outside the obstruction.',
            'nontermination_claim': 'None: cutoff runs are skipped and never classified as nonhalting.',
            'universality_claim': 'None.'}


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2))
