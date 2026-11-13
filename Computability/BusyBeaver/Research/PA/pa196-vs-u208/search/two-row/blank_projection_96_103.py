#!/usr/bin/env python3
"""Replay a bounded step-projection failure for two 195-state folds."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pa196_blank_control', HERE / 'blank_halt_control.py')
control = importlib.util.module_from_spec(spec)
spec.loader.exec_module(control)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    table, table_sha = control.fold.read_table(control.fold.DEFAULT_TABLE)
    results = []
    for drop, keep in ((103, 96), (96, 103)):
        rows = ((0, 1, 59), (1, 1, 110))
        candidate = (drop, keep, rows)
        project = lambda q: keep if q == drop else q
        parent, parent_head, parent_tape = 0, 0, set()
        child, child_head, child_tape = 0, 0, set()
        child_steps = 0
        parent_digest = hashlib.sha256()
        child_digest = hashlib.sha256()
        for parent_steps in range(6000):
            require(parent != 196 and child != 196, 'unexpected early halt')
            require((child, child_head, child_tape) == (project(parent), parent_head, parent_tape),
                    'previous projected boundary mismatch')
            previous = (child, child_head, set(child_tape))
            parent_digest.update(f'{parent} {parent_head} {int(parent_head in parent_tape)}\n'.encode())
            next_tape = set(parent_tape)
            next_parent, next_head = control.step(table, parent, parent_head, next_tape)
            goal = (project(next_parent), next_head, next_tape)
            block_len = None
            for j in range(1, 513):
                if child == 196:
                    break
                child_digest.update(f'{child} {child_head} {int(child_head in child_tape)}\n'.encode())
                child, child_head = control.step(table, child, child_head, child_tape, candidate)
                child_steps += 1
                if (child, child_head, child_tape) == goal:
                    block_len = j
                    break
            if block_len is None:
                state, head, tape = previous
                require((parent_steps, child_steps, parent, state, head, len(tape)) ==
                        (5620, 6136, 96, keep, 8, 35), 'unexpected failure boundary')
                require(int(head in tape) == 1, 'unexpected read')
                mask = sum(int(head + i in tape) << (i+2) for i in range(-2, 3))
                require(mask == 22, 'unexpected five-cell mask')
                results.append({
                    'drop': drop, 'keep': keep,
                    'rows': [[0, 'R', 59], [1, 'R', 110]],
                    'parent_step': parent_steps, 'child_step_at_boundary': child_steps - 512,
                    'parent_state': parent, 'child_state': state, 'head': head,
                    'read': 1, 'window_mask': mask, 'one_cells': sorted(tape),
                    'attempted_child_steps': 512, 'no_matching_endpoint_in_attempt': True,
                    'parent_prefix_sha256': parent_digest.hexdigest(),
                    'child_prefix_plus_failed_block_sha256': child_digest.hexdigest()})
                break
            if parent not in (96, 103):
                require(block_len == 1, 'unaffected row did not commute in one step')
            parent, parent_head, parent_tape = next_parent, next_head, next_tape
        else:
            raise ValueError('failure boundary not reached')
    report = {'table_sha256': table_sha, 'candidates': results,
              'scope': 'Finite simulation failure only; later rejoining and halting equivalence are not decided.'}
    data = json.dumps(report, indent=2, sort_keys=True) + '\n'
    print(data, end='')
    if args.output:
        args.output.write_text(data)


if __name__ == '__main__':
    main()
