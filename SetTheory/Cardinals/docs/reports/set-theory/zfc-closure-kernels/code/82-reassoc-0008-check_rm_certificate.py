#!/usr/bin/env python3
"""Independently replay a finite Wade operation-bisimulation certificate.

This verifies only the register-program layer. It does not execute a binary
table, certify a bootstrap, or establish any consistency statement.
Uses only the Python standard library and leaves all inputs unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def load_program(path):
    raw = path.read_text()
    if path.suffix == '.json':
        return {int(q): tuple(es) for q, es in json.loads(raw).items()}
    body = raw.split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    rows = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', body)
    names = dict(CN='ENode', CI='EInc', CD='EDecnz', CB='EBreak', CC='EContinue', CH='EHalt')
    def translate(e):
        head, *tail = e.split()
        return ' '.join([names[head], *tail])
    if not rows:
        raise ValueError('No program rows found')
    return {q: tuple(map(translate, row)) for q, row in enumerate(rows)}


def walk(program, pc):
    node, used = 0, ''
    seen = set()
    for i in range(len(program) + 1):
        if node in seen:
            raise ValueError('Decoder contains a cycle')
        seen.add(node)
        bit = pc[i] if i < len(pc) else '0'
        used += bit
        edge = program[node][int(bit)]
        kind, *arg = edge.split()
        if kind != 'ENode':
            if '1' in pc[len(used):]:
                raise ValueError('Unconsumed nonzero path suffix')
            return used, edge
        node = int(arg[0])
    raise ValueError('Decoder exhausted its bound')


def increment(pc):
    value = (int(pc, 2) + 1) % (1 << len(pc)) if pc else 0
    return format(value, '0' + str(len(pc)) + 'b') if pc else ''


def strip(pc, bit, count):
    while pc and count:
        count -= pc[-1] == bit
        pc = pc[:-1]
    return pc


def control_normalize(program, pc):
    visited = set()
    count = 0
    while True:
        # Trailing zeros are implicit in walk; normalize only the key.
        key = pc.rstrip('0')
        if key in visited:
            raise ValueError('Infinite control-only path')
        visited.add(key)
        used, edge = walk(program, pc)
        kind, *arg = edge.split()
        if kind == 'EBreak':
            pc = increment(strip(used, '0', int(arg[0])))
        elif kind == 'EContinue':
            pc = strip(used, '1', int(arg[0]))
        else:
            return used, edge, count
        count += 1


def successors(program, pc, edge):
    kind, *arg = edge.split()
    if kind == 'EHalt':
        return []
    raw = ([increment(strip(pc, '0', 1)), increment(pc)]
           if kind == 'EDecnz' else [increment(pc)])
    if kind not in ('EDecnz', 'EInc'):
        raise ValueError('Certificate operation is not an operation')
    return [control_normalize(program, q)[:2] for q in raw]


def verify(old, new, certificate):
    rows = certificate['pairs']
    root = rows[certificate['initial']]
    if tuple(control_normalize(old, '')[:2]) != (root['old'], root['instruction']):
        raise ValueError('Wrong old initial pair')
    if tuple(control_normalize(new, '')[:2]) != (root['new'], root['instruction']):
        raise ValueError('Wrong new initial pair')
    checked_branches = 0
    for index, row in enumerate(rows):
        for program, side in [(old, 'old'), (new, 'new')]:
            actual, edge = walk(program, row[side])
            if (actual, edge) != (row[side], row['instruction']):
                raise ValueError(('Wrong operation', index, side))
            targets = successors(program, actual, edge)
            if len(targets) != len(row['successors']):
                raise ValueError(('Wrong branch count', index))
            for (p, e), target_index in zip(targets, row['successors']):
                target = rows[target_index]
                if (p, e) != (target[side], target['instruction']):
                    raise ValueError(('Wrong successor', index, side, target_index))
        checked_branches += len(row['successors'])
    reachable, pending = set(), [certificate['initial']]
    while pending:
        q = pending.pop()
        if q not in reachable:
            reachable.add(q)
            pending.extend(rows[q]['successors'])
    return dict(status='PASS_REGISTER_PROGRAM_ONLY', pairs=len(rows),
                branches=checked_branches, reachable_pairs=len(reachable),
                both_decrement_outcomes=True, binary_table_checked=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('old', type=Path)
    parser.add_argument('new', type=Path)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = verify(load_program(args.old), load_program(args.new),
                    json.loads(args.certificate.read_text()))
    result['sha256'] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in (args.old, args.new, args.certificate, Path(__file__))}
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    print(output, end='')


if __name__ == '__main__':
    main()
