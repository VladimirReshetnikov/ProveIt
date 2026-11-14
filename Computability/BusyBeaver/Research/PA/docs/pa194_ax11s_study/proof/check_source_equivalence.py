#!/usr/bin/env python3
"""Independent literal source check for the AX11/AX11S affected block.

The report supplies the all-natural counter-induction proof. This script
checks its exact program binding and finite arithmetic corroborations;
the finite runs are not promoted to a universal theorem.
"""
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def need(claim, message):
    if not claim:
        raise AssertionError(message)


def run_block(program, t, h, x):
    registers = [17, t, 23, 29, 31, h, x, 37, 41]
    other = registers.copy()
    pc, steps = 3660, 0
    bound = 9 * (t + h + x) + 10
    while pc not in (10, 11):
        need(steps < bound, ('bound', t, h, x, pc, steps))
        instruction = program[pc]
        if instruction[0] == 'inc':
            _, r, pc = instruction
            registers[r] += 1
        elif instruction[0] == 'dec':
            _, r, zero, nonzero = instruction
            if registers[r]:
                registers[r] -= 1
                pc = nonzero
            else:
                pc = zero
        elif instruction[0] == 'jump':
            pc = instruction[1]
        else:
            raise AssertionError(('unexpected instruction', pc, instruction))
        steps += 1
    need(registers[1] == h and registers[5:7] == [0, 0], 'exit registers')
    need(all(registers[i] == other[i] for i in (0, 2, 3, 4, 7, 8)), 'frame')
    need((pc == 10) == (t + h + x == 1), 'guard')
    return pc, registers, steps


def compare_cost(a, b):
    if a == b:
        return 3 * a + 2
    return 2 * a + b + 4 if a > b else 3 * b + 2


def edges(instruction):
    if instruction[0] in ('inc', 'dec'):
        return instruction[2:]
    if instruction[0] == 'jump':
        return instruction[1:]
    return []


def main():
    paths = [ROOT / 'reference/ax11/instructions.json',
             ROOT / 'machine/instructions.json']
    old, new = [json.loads(p.read_text()) for p in paths]
    need(len(old) == 3672 and len(new) == 3669, 'lengths')
    need(old[:3667] == new[:3667], 'common prefix')
    need(old[3667:] == [['dec', 6, 3670, 3668], ['inc', 5, 3669],
                       ['jump', 3667], ['inc', 6, 3671], ['jump', 0]], 'old trailer')
    need(new[3667:] == [['inc', 5, 3668], ['jump', 0]], 'new trailer')
    need(old[3660:3667] == [['dec', 1, 3663, 3661], ['inc', 6, 3662],
                           ['jump', 3660], ['dec', 5, 3667, 3664],
                           ['inc', 1, 3665], ['inc', 6, 3666], ['jump', 3663]],
         'shared transfer')
    need(old[:11] == [['dec', 5, 4, 1], ['dec', 6, 3, 2], ['jump', 0],
                     ['jump', 5], ['dec', 6, 10, 5], ['dec', 5, 7, 6],
                     ['jump', 5], ['dec', 6, 9, 8], ['jump', 5],
                     ['jump', 11], ['halt']], 'comparator')
    for program in (old, new):
        incoming = [(i, target) for i, ins in enumerate(program)
                    for target in edges(ins) if i < 3660 and target >= 3660]
        need(incoming == [(48, 3660)], 'block entry')
        incoming = [(i, target) for i, ins in enumerate(program)
                    for target in edges(ins) if i >= 11 and target < 11]
        need(incoming == [(len(program) - 1, 0)], 'comparator entry')

    trials = list(itertools.product(range(12), repeat=3))
    trials += [(0, 0, 1000), (1000, 0, 0), (0, 1000, 0), (997, 991, 983)]
    for t, h, x in trials:
        s = t + h + x
        old_result = run_block(old, t, h, x)
        new_result = run_block(new, t, h, x)
        need(old_result[:2] == new_result[:2], 'complete exit equality')
        old_count = 3 * t + 4 * h + 3 * s + 5 + compare_cost(s, 1)
        new_count = 3 * t + 4 * h + 4 + compare_cost(1, s)
        need(old_result[2] == old_count and new_result[2] == new_count, 'exact counts')
        gain = 0 if s == 0 else 4 if s == 1 else 2 * s + 4
        need(old_count - new_count == gain, 'gain')
        need(old_count <= 9 * s + 10 and new_count <= 9 * s + 10, 'linear bound')

    report = {'status': 'PASS', 'source_graph_boundary_checked': True,
              'instruction_hashes': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                     for p in paths},
              'finite_counter_cases': len(trials), 'includes_arbitrary_scratch_examples': True,
              'all_natural_proof': 'proof/source_equivalence.tex',
              'scope': 'Exact graph binding plus finite corroboration of independently derived induction formulas; no Lean/Rocq compilation.'}
    (ROOT / 'proof/source_equivalence_check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
