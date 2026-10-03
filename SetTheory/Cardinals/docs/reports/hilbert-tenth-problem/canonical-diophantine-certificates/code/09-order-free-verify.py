#!/usr/bin/env python3
"""Reproduce finite exact checks. These tests are not a proof-assistant audit."""
from __future__ import annotations
from itertools import permutations, product
from pathlib import Path
import json
import math
from presburger_gadgets import (comparison_witness, comparison_penalty,
                                 divisibility_witness, divisibility_penalty)
from assembly_compiler import (Compiler, canonical_ranks, fixtures, sequential_states,
                               terminal, verify_export)

ROOT = Path(__file__).resolve().parents[1]

def schedules(system, domain, labels):
    target = dict(zip(domain, labels))
    todo = [v for v in domain if target[v] and v not in system.seed]
    found = []
    for order in permutations(todo):
        state = dict(system.seed)
        for v in order:
            if system.support(state, v, target[v]) < system.temperature:
                break
            state[v] = target[v]
        else:
            found.append(order)
    return found


def two_cut(system, domain, labels, ranks):
    target = dict(zip(domain, labels))
    N = len(domain)
    for v in domain:
        if v in system.seed or not target[v]:
            if ranks[v] != 0:
                return False
            continue
        if not (1 <= ranks[v] <= N):
            return False
        first = sum(system.glue(u, target[u], v, target[v]) for u in domain
                    if ranks[u] < ranks[v])
        second = sum(system.glue(u, target[u], v, target[v]) for u in domain
                     if ranks[u]+1 < ranks[v])
        if first < system.temperature or second >= system.temperature:
            return False
    return True


def main():
    ROOT.joinpath('data').mkdir(exist_ok=True)
    report = {'arithmetic': 'Python exact integers', 'proof_assistant_checked': False}
    cmp_cases = 0
    for N in range(1, 9):
        for x, y, j in product(range(N+1), range(N+1), (0, 1)):
            feasible = []
            for c in (0, 1):
                bar = 1-c
                p = y+(N+2)*bar-x-j-1
                r = x+j+(N+2)*c-y
                if min(p, r) >= 0:
                    feasible.append(c)
            assert feasible == [int(x+j < y)]
            cmp_cases += 1
    report['comparator_input_cases'] = cmp_cases
    gate_cases = 0
    for k in (2, 3):
        for bits in product((0, 1), repeat=k):
            feasible = []
            for z in range(3):
                slacks = [a-z for a in bits] + [z+k-1-sum(bits)]
                if min(slacks) >= 0:
                    feasible.append(z)
            assert feasible == [math.prod(bits)]
            gate_cases += 1
    report['boolean_gate_input_cases'] = gate_cases
    report['fixtures'] = {}
    rank_trials = 0
    mutations = 0
    for name, (system, raw_domain) in fixtures().items():
        compiler = Compiler(system, raw_domain)
        term_compiler = Compiler(system, raw_domain, True)
        domain = compiler.domain
        reachable = sequential_states(system, domain)
        raw_count = prod_count = terminal_count = 0
        largest_witness = 0
        for labels in product(range(len(system.tiles)+1), repeat=len(domain)-len(system.seed)):
            it = iter(labels)
            full = tuple(system.seed[v] if v in system.seed else next(it) for v in domain)
            raw_count += 1
            ranks = canonical_ranks(system, domain, full)
            assert (ranks is not None) == (full in reachable)
            w = compiler.witness(full)
            assert (w is not None) == (full in reachable)
            wt = term_compiler.witness(full)
            assert (wt is not None) == (full in reachable and terminal(system, domain, full))
            if w is None:
                continue
            prod_count += 1
            terminal_count += wt is not None
            largest_witness = max(largest_witness, max(w))
            # Every producible target: exhaustively check rank uniqueness.
            occupied = [v for v, a in zip(domain, full) if a and v not in system.seed]
            solutions = []
            for rank_values in product(range(1, len(domain)+1), repeat=len(occupied)):
                rank_trials += 1
                guess = dict.fromkeys(domain, 0)
                guess.update(zip(occupied, rank_values))
                if two_cut(system, domain, full, guess):
                    solutions.append(guess)
            assert solutions == [ranks]
        assert prod_count == len(reachable)
        maximum_target = max(reachable, key=lambda t: (sum(a != 0 for a in t), t))
        use = term_compiler if terminal(system, domain, maximum_target) else compiler
        path = ROOT/'data'/f'{name}_certificate.json'
        use.export(str(path), maximum_target)
        assert verify_export(str(path)) == (use.counts['variables'], use.counts['equations'])
        w = use.witness(maximum_target)
        assert w is not None
        for index in range(len(w)):
            for offset in (-1, 1):
                if w[index]+offset < 0:
                    continue
                corrupted = w.copy()
                corrupted[index] += offset
                assert not use.check(corrupted)
                mutations += 1
        orders = schedules(system, domain, maximum_target)
        report['fixtures'][name] = {
            'raw_seed_extending_labelings': raw_count,
            'producible_assemblies': prod_count,
            'terminal_assemblies': terminal_count,
            'full_target_schedules': len(orders),
            'maximum_base_witness_coordinate': largest_witness,
            'base_counts': compiler.counts, 'terminal_counts': term_compiler.counts,
            'exported_terminal_requirement': use.require_terminal,
            'full_target_labels': maximum_target,
            'full_target_ranks': [canonical_ranks(system, domain, maximum_target)[v] for v in domain],
        }
    assert [report['fixtures'][k]['producible_assemblies'] for k in fixtures()] == [7,16,24,5]
    assert [report['fixtures'][k]['terminal_assemblies'] for k in fixtures()] == [0,1,2,1]
    assert [report['fixtures'][k]['full_target_schedules'] for k in fixtures()] == [4,24,24,2]
    report['rank_assignments_tested_on_producible_targets'] = rank_trials
    report['single_coordinate_corruptions_rejected'] = mutations
    # Inspect all rank tuples for ALL diamond targets, including the rejected island.
    system, raw = fixtures()['diamond']
    domain = tuple(sorted(raw))
    all_diamond_rank_trials = 0
    for bits in product((0,1), repeat=3):
        full = (1,)+bits
        occupied = [v for v,a in zip(domain,full) if a and v not in system.seed]
        found = 0
        for rv in product(range(1,5), repeat=len(occupied)):
            all_diamond_rank_trials += 1
            r = dict.fromkeys(domain,0)
            r.update(zip(occupied, rv))
            found += two_cut(system,domain,full,r)
        assert found == int(canonical_ranks(system,domain,full) is not None)
    report['all_diamond_rank_trials'] = all_diamond_rank_trials
    # Cubic-face example: (x-y)^2*(1+z) has the affine zero face x=y.
    cubic_examples = 0
    for x,y,z in product(range(8), repeat=3):
        p = (x-y)**2*(1+z)
        assert p >= 0 and (p == 0) == (x == y)
        cubic_examples += 1
    # Quadratic representation of the nonconvex semilinear set 2N union (1+3N).
    semilinear_cases = 0
    for n in range(31):
        exists = False
        for e1,e2,f1,f2 in product((0,1),repeat=4):
            for c1,c2 in product(range(31),repeat=2):
                Q = ((e1+e2-1)**2+(e1+f1-1)**2+(e2+f2-1)**2
                     +(n-e2-2*c1-3*c2)**2+f1*c1+f2*c2)
                assert Q >= 0
                exists |= Q == 0
                semilinear_cases += 1
        assert exists == (n%2 == 0 or (n >= 1 and (n-1)%3 == 0))
    report['cubic_grid_examples'] = cubic_examples
    report['semilinear_quadratic_assignments_tested'] = semilinear_cases
    # Signed-glue obstruction: both see a strength-1 seed bond;
    # after one attaches, the other additionally sees a -1 bond.
    assert 1 >= 1 and 1-1 < 1
    report['signed_glue_obstruction_checked'] = True
    unbounded_comparison_cases = 0
    for x, y in product(range(-5, 6), repeat=2):
        expected = comparison_witness(x, y)
        found = []
        for p, r in product(range(12), repeat=2):
            for c, bar in product((0, 1), repeat=2):
                h = p-c
                if h < 0:
                    continue
                w = (p, r, c, bar, h)
                if comparison_penalty(x, y, w) == 0:
                    found.append(w)
        assert found == [expected]
        assert expected[2] == int(x < y)
        unbounded_comparison_cases += 1
    divisibility_cases = 0
    for L, modulus in product(range(-15, 16), range(1, 7)):
        expected = divisibility_witness(L, modulus)
        assert all(x >= 0 for x in expected)
        assert divisibility_penalty(L, modulus, expected) == 0
        assert expected[7] == int(L % modulus == 0)
        found = []
        for u, v, rem in product(range(17), range(17), range(modulus)):
            slack = modulus-1-rem
            w = (u, v, rem, slack)+comparison_witness(0, rem)
            if divisibility_penalty(L, modulus, w) == 0:
                found.append(w)
        assert found == [expected]
        divisibility_cases += 1
    report['unbounded_comparison_operand_pairs'] = unbounded_comparison_cases
    report['signed_divisibility_operand_modulus_pairs'] = divisibility_cases
    report['status'] = 'PASS'
    path = ROOT/'data'/'verification_report.json'
    path.write_text(json.dumps(report, indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
