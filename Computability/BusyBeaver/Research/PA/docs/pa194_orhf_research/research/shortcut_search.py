#!/usr/bin/env python3
"""Discover finite-history, exact-tape transition shortcuts.

This is a bounded discovery tool, not the proof of the delivered machines.
It enumerates incoming histories and universally branches on unread tape bits.
A branch budget can omit possible answers; it never treats a cutoff as a proof
of impossibility. Accepted edits need a separate reachable-history argument,
including initial prefixes shorter than the chosen history depth.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
DEFAULT_TABLE = HERE.parent / 'reference/PA194ORH/machine.native.tm'


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        if (q, bit) in rows or bit not in (0, 1) or write not in (0, 1):
            raise ValueError('Malformed or duplicate binary row')
        if direction not in ('L', 'R'):
            raise ValueError('Expected a unit left/right move')
        rows[q, bit] = write, 1 if direction == 'R' else -1, target
    states = {q for q, bit in rows}
    if set(rows) != {(q, bit) for q in states for bit in (0, 1)}:
        raise ValueError('Incomplete working-state table')
    return rows


def contexts(incoming, state, depth):
    paths = [[]]
    for _ in range(depth):
        following = []
        for path in paths:
            target = path[0][0] if path else state
            for edge in incoming[target]:
                following.append([edge] + path)
        paths = following
    states = set()
    for path in paths:
        tape, head, bad = {}, 0, False
        for source, bit, write, direction, target in path:
            if head in tape and tape[head] != bit:
                bad = True
                break
            tape[head] = write
            head += direction
        if not bad:
            states.add(tuple(sorted((pos-head, value) for pos, value in tape.items())))
    return [dict(context) for context in states]


def possibilities(rows, state, bit, context, limit, branch_budget):
    original = dict(context)
    original[0] = bit
    remaining_budget = [branch_budget]

    def visit(q, head, original, written, remaining):
        if branch_budget:
            remaining_budget[0] -= 1
        answers = set()
        if head in (-1, 1) and all(pos == 0 or original.get(pos) == value
                                  for pos, value in written.items()):
            answers.add((written.get(0, original[0]), head, q))
        exhausted = bool(branch_budget and remaining_budget[0] <= 0)
        if remaining == 0 or exhausted or (q, 0) not in rows:
            return answers
        current = written.get(head, original.get(head))
        choices = (0, 1) if current is None else (current,)
        children = []
        for current in choices:
            old, changed = original.copy(), written.copy()
            if head not in old and head not in changed:
                old[head] = current
            write, direction, target = rows[q, current]
            changed[head] = write
            if changed[head] == old.get(head):
                changed.pop(head)
            children.append(visit(target, head+direction, old, changed, remaining-1))
        if children:
            answers.update(set.intersection(*children))
        return answers

    return visit(state, 0, original, {}, limit)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, default=DEFAULT_TABLE,
                        help='Native five-column table; defaults to the packaged ORH parent')
    parser.add_argument('--start-state', type=int, default=74,
                        help='Initial control, excluded from history-based shortcuts (default: 74)')
    parser.add_argument('--history-depth', type=int, default=3,
                        help='Number of incoming transitions to enumerate (default: 3)')
    parser.add_argument('--trace-cap', type=int, default=13,
                        help='Maximum old transitions considered per local trace (default: 13)')
    parser.add_argument('--branch-budget', type=int, default=0,
                        help='Recursive visits per context; 0 means unlimited (default: 0)')
    parser.add_argument('--output', type=Path, default=HERE/'shortcut_candidates_replay.json',
                        help='Fresh result path; recorded shortcuts.json is not overwritten by default')
    parser.add_argument('--receipt', type=Path,
                        help='Optional metadata receipt with exact settings and input hash')
    args = parser.parse_args()
    if args.history_depth < 1 or args.trace_cap < 1 or args.branch_budget < 0:
        parser.error('History depth and trace cap must be positive; branch budget must be nonnegative')
    rows = read_table(args.table)
    if (args.start_state, 0) not in rows:
        parser.error('The specified initial control has no working-state rows')
    incoming = collections.defaultdict(list)
    for (q, bit), (write, direction, target) in rows.items():
        incoming[target].append((q, bit, write, direction, target))
    results = []
    started = time.time()
    for q in sorted({q for q, bit in rows}):
        if q == args.start_state:
            continue
        histories = contexts(incoming, q, args.history_depth)
        for bit in (0, 1):
            relevant = [context for context in histories if context.get(0, bit) == bit]
            if not relevant:
                continue
            candidates = None
            for context in relevant:
                options = possibilities(rows, q, bit, context, args.trace_cap, args.branch_budget)
                candidates = options if candidates is None else candidates & options
                if not candidates:
                    break
            candidates.discard(rows[q, bit])
            for action in sorted(candidates):
                if action[2] == q:
                    continue
                item = dict(row=[q, bit], old=rows[q, bit], new=action, contexts=len(relevant))
                results.append(item)
                print(json.dumps(item), flush=True)
        if q % 30 == 0:
            print('progress', q, round(time.time()-started, 2), file=sys.stderr, flush=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(results, indent=2)+'\n')
    elapsed = time.time()-started
    if args.receipt:
        receipt = dict(input_sha256=hashlib.sha256(args.table.read_bytes()).hexdigest(),
                       history_depth=args.history_depth, trace_cap=args.trace_cap,
                       branch_budget=args.branch_budget, start_state=args.start_state,
                       candidates=len(results), elapsed_seconds=elapsed,
                       scope='Bounded discovery. A cutoff omits possibilities; it is not an impossibility result. Initial histories and simultaneous edits require separate proofs.')
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(receipt, indent=2)+'\n')
    print('done', len(results), elapsed, flush=True)


if __name__ == '__main__':
    main()
