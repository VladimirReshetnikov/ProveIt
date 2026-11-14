#!/usr/bin/env python3
"""Discover contextual state folds; exact checks alone justify acceptance.

Usage: python3 discover_folds.py TABLE --output RESULT.json

A depth-k context family overapproximates every tape neighborhood reachable
at each state from state 0, on any initial tape. It is formed by k exact
forward images of the family containing every state/tape, injecting the
initial state with unconstrained tape after every iteration. Thus it covers
both long histories and histories shorter than k.

Random execution is only a rejection screen. Every accepted candidate is
subsequently checked on every context and read bit by symbolic branching,
including arbitrary unspecified tape exterior. A negative search result is
restricted to this family of candidates and to the chosen bounds; it is
not a lower bound on the state complexity of the intended computation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
import time


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        state, bit, write, direction, target = line.split()
        key = int(state), int(bit)
        if key in table or direction not in ('L', 'R'):
            raise ValueError('Duplicate or malformed transition')
        table[key] = int(write), (1 if direction == 'R' else -1), int(target)
    return table


def remove_subsumed(contexts):
    """A weaker bit cylinder already covers any stronger cylinder."""
    result = []
    for context in sorted(set(contexts), key=lambda c: (len(c), c)):
        cells = set(context)
        if not any(set(other) <= cells for other in result):
            result.append(context)
    return result


def history_contexts(table, depth, initial=0):
    states = {state for state, bit in table}
    contexts = {state: [()] for state in states}
    for _ in range(depth):
        successors = {state: [] for state in states}
        successors[initial] = [()]
        for (state, bit), (write, direction, target) in table.items():
            if target not in states:
                continue
            for context in contexts[state]:
                cells = dict(context)
                if 0 in cells and cells[0] != bit:
                    continue
                cells[0] = write
                moved = tuple(sorted((pos - direction, value)
                                     for pos, value in cells.items()))
                successors[target].append(moved)
        contexts = {state: remove_subsumed(items)
                    for state, items in successors.items()}
    return contexts


def projected(state, drop, keep):
    return keep if state == drop else state


def candidate_step(table, state, bit, drop, keep, replacement):
    changed_bit, write, direction, helper = replacement
    if state == keep and bit == changed_bit:
        transition = write, direction, helper
    else:
        transition = table[state, bit]
    write, direction, target = transition
    return write, direction, projected(target, drop, keep)


def random_screen(table, old_state, bit, context, drop, keep,
                  replacement, rng, limit, halt):
    if 0 in context and context[0] != bit:
        return True  # Empty antecedent.
    tape = {pos: rng.randrange(2) for pos in range(-limit - 2, limit + 3)}
    tape.update(context)
    tape[0] = bit
    old_write, old_move, old_target = table[old_state, bit]
    target = projected(old_target, drop, keep)
    expected = dict(tape)
    expected[0] = old_write
    state, head = keep, 0
    for _ in range(limit):
        if state == halt:
            return False
        write, direction, state = candidate_step(
            table, state, tape[head], drop, keep, replacement)
        tape[head] = write
        head += direction
        if (state, head) == (target, old_move) and tape == expected:
            return True
    return False


def exact_case(table, old_state, bit, context, drop, keep,
               replacement, limit, halt):
    """Return exhaustive branch certificates, or None if any branch fails."""
    if 0 in context and context[0] != bit:
        return []
    context = dict(context)
    context[0] = bit
    old_write, old_move, old_target = table[old_state, bit]
    target = projected(old_target, drop, keep)
    stack = [(keep, 0, {}, context, [])]
    certificates = []
    while stack:
        state, head, writes, initial, trace = stack.pop()
        if trace and (state, head) == (target, old_move):
            positions = set(writes) | {0}
            equal_tape = all(
                writes.get(pos, initial.get(pos, ('var', pos))) ==
                (old_write if pos == 0 else initial.get(pos, ('var', pos)))
                for pos in positions)
            if equal_tape:
                certificates.append({'initial': initial, 'trace': trace,
                                     'endpoint': [target, old_move]})
                continue
        if len(trace) >= limit or state == halt:
            return None
        read_bit = writes.get(head, initial.get(head))
        if read_bit is None:
            for value in (0, 1):
                branch = dict(initial)
                branch[head] = value
                stack.append((state, head, dict(writes), branch, list(trace)))
            continue
        write, direction, target_state = candidate_step(
            table, state, read_bit, drop, keep, replacement)
        updated = dict(writes)
        updated[head] = write
        step = [state, head, read_bit, write, direction, target_state]
        stack.append((target_state, head + direction, updated,
                      initial, trace + [step]))
        if len(stack) + len(certificates) > 4096:
            return None
    return certificates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('table', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--depth', type=int, default=3)
    parser.add_argument('--limit', type=int, default=7)
    parser.add_argument('--seed', type=int, default=292109)
    parser.add_argument('--halt', type=int, default=254)
    args = parser.parse_args()
    table = read_table(args.table)
    states = sorted({state for state, bit in table})
    contexts = history_contexts(table, args.depth)
    rng = random.Random(args.seed)
    results = []
    pairs = mutations = 0
    started = time.monotonic()
    for drop in states:
        if drop == 0:
            continue
        for keep in states:
            if keep in (0, drop):
                continue
            def row_image(row):
                return row[:2] + (projected(row[2], drop, keep),)
            for changed_bit in (0, 1):
                other = 1 - changed_bit
                if row_image(table[drop, other]) != row_image(table[keep, other]):
                    continue
                pairs += 1
                for helper in states:
                    if helper in (drop, keep):
                        continue
                    for direction in (-1, 1):
                        for write in (changed_bit, 1 - changed_bit):
                            mutations += 1
                            replacement = changed_bit, write, direction, helper
                            inputs = [(state, bit, dict(context))
                                      for state in (drop, keep)
                                      for context in contexts[state]
                                      for bit in (0, 1)]
                            if not all(random_screen(
                                    table, state, bit, context, drop, keep,
                                    replacement, rng, args.limit, args.halt)
                                    for state, bit, context in inputs
                                    for _ in range(2)):
                                continue
                            cases = []
                            for state, bit, context in inputs:
                                branches = exact_case(
                                    table, state, bit, context, drop, keep,
                                    replacement, args.limit, args.halt)
                                if branches is None:
                                    break
                                cases.append({'old_state': state, 'read': bit,
                                              'context': context,
                                              'branches': branches})
                            else:
                                results.append({'remove': drop, 'keep': keep,
                                                'replacement': replacement,
                                                'cases': cases})
                                print('FOUND', drop, '->', keep,
                                      'replacement', replacement, flush=True)
    report = {'table': str(args.table),
              'input_sha256': hashlib.sha256(args.table.read_bytes()).hexdigest(),
              'history_depth': args.depth, 'maximum_macro_steps': args.limit,
              'seed': args.seed, 'row_compatible_pairs': pairs,
              'mutations_screened': mutations, 'results': results,
              'seconds': time.monotonic() - started}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print('Accepted:', len(results), 'seconds:', report['seconds'])


if __name__ == '__main__':
    main()
