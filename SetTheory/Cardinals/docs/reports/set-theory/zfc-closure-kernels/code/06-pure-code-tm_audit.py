"""Independent finite/static audit of a two-symbol Wade-format TM.

This is NOT a halting decision procedure, a set-theory proof, or a replacement
for upstream verification. No upstream transition table is distributed here.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

Transition = tuple[int, str, int]
Table = dict[tuple[int, int], Transition]


def parse(text: str) -> tuple[int, Table]:
    start = None
    table: Table = {}
    for line_no, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if line.startswith('#! start '):
            if start is not None:
                raise ValueError('duplicate start declaration')
            fields = line.split()
            if len(fields) != 3 or not fields[2].isdigit():
                raise ValueError('bad start declaration')
            start = int(fields[2])
            continue
        if line.startswith('#'):
            continue
        fields = line.split()
        if len(fields) != 5:
            raise ValueError(f'line {line_no}: expected five fields')
        q, r, w, move, t = fields
        if not all(s.isdigit() for s in (q, r, w, t)):
            raise ValueError(f'line {line_no}: invalid natural number')
        q, r, w, t = map(int, (q, r, w, t))
        if r not in (0, 1) or w not in (0, 1) or move not in ('L', 'R'):
            raise ValueError(f'line {line_no}: invalid symbol or move')
        if (q, r) in table:
            raise ValueError(f'line {line_no}: duplicate transition')
        table[q, r] = (w, move, t)
    if start is None or not table:
        raise ValueError('missing start declaration or empty table')
    states = {q for q, _ in table}
    if start not in states or any((q, r) not in table for q in states for r in (0, 1)):
        raise ValueError('nonhalting states must have both symbol transitions')
    return start, table


def congruence(table: Table) -> tuple[dict[int, int], list[int]]:
    """Coarsest state congruence preserving each write, move, and halt.

    Equivalent states are indistinguishable on ALL tapes under the SAME
    tape/head representation. Invariant-dependent and recoding optimizations
    are outside this criterion. Terminal targets are treated as one halt.
    """
    states = sorted({q for q, _ in table})
    classes = dict.fromkeys(states, 0)
    sizes = [1]
    while True:
        signatures = {}
        refined = {}
        for q in states:
            signature = tuple((w, d, classes.get(t, -1))
                              for w, d, t in (table[q, 0], table[q, 1]))
            if signature not in signatures:
                signatures[signature] = len(signatures)
            refined[q] = signatures[signature]
        sizes.append(len(signatures))
        if refined == classes:
            return classes, sizes
        classes = refined


def simulate(start: int, table: Table, steps: int) -> dict:
    if type(steps) is not int or steps < 0:
        raise ValueError('steps must be a nonnegative integer')
    tape: set[int] = set()
    q, head, left, right = start, 0, 0, 0
    visits: set[int] = set()
    for step in range(steps):
        if (q, int(head in tape)) not in table:
            return {'halted': True, 'steps': step, 'state': q, 'head': head,
                    'ones': len(tape), 'head_range': [left, right],
                    'distinct_states_visited': len(visits)}
        visits.add(q)
        w, d, q = table[q, int(head in tape)]
        if w:
            tape.add(head)
        else:
            tape.discard(head)
        head += 1 if d == 'R' else -1
        left, right = min(left, head), max(right, head)
    return {'halted': (q, int(head in tape)) not in table, 'steps': steps,
            'state': q, 'head': head, 'ones': len(tape),
            'head_range': [left, right], 'distinct_states_visited': len(visits),
            'tape_support_sha256': hashlib.sha256(
                ','.join(map(str, sorted(tape))).encode()).hexdigest()}


def audit(path: Path, steps: int) -> dict:
    raw = path.read_bytes()
    start, table = parse(raw.decode('utf-8'))
    states = {q for q, _ in table}
    targets = {t for _, _, t in table.values()}
    terminal = sorted(targets - states)
    seen, pending = {start}, [start]
    while pending:
        q = pending.pop()
        if q not in states:
            continue
        for r in (0, 1):
            t = table[q, r][2]
            if t not in seen:
                seen.add(t)
                pending.append(t)
    classes, history = congruence(table)
    blocks: dict[int, list[int]] = {}
    for q, c in classes.items():
        blocks.setdefault(c, []).append(q)
    return {
        'status': 'finite/static checks completed; no end-to-end proof replay',
        'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw),
        'start': start, 'nonhalting_states': len(states),
        'transitions': len(table), 'terminal_targets': terminal,
        'states_contiguous_from_zero': states == set(range(len(states))),
        'transition_graph_reachable_nonhalting': len(seen & states),
        'transition_graph_reachable_terminal': sorted(seen - states),
        'congruence_class_counts': history,
        'nontrivial_congruence_blocks': [v for v in blocks.values() if len(v) > 1],
        'blank_prefix': simulate(start, table, steps),
        'limitations': [
            'Graph reachability overapproximates actual tape-dependent reachability.',
            'Singleton congruence blocks exclude only this context-free merge method.',
            'Finite simulation does not prove nonhalting or consistency.',
            'No upstream Coq build or internal ZFC proof was rerun.']}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('table', type=Path)
    p.add_argument('--steps', type=int, default=264982)
    p.add_argument('--out', type=Path)
    args = p.parse_args()
    result = audit(args.table, args.steps)
    text = json.dumps(result, indent=2) + '\n'
    if args.out:
        args.out.write_text(text)
    print(text, end='')
