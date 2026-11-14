#!/usr/bin/env python3
"""Exact complete-tape blank initialization, with explicit checks under -O."""
import argparse
import hashlib
import json
from pathlib import Path
from build import parse, need

def run(table, steps):
    ones, state, head = set(), 0, 0
    used, digest = set(), hashlib.sha256()
    for i in range(steps):
        bit = int(head in ones)
        write, move, target = table[state, bit]
        used.add((state, bit))
        digest.update((json.dumps([i, state, head, bit, write, move, target],
                                  separators=(',', ':')) + '\n').encode())
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        state, head = target, head + move
    return (state, head, ones), digest.hexdigest(), used

def ordinal_graph(rows):
    leaf = {word: i for i, (word, op, arg) in enumerate(rows)}
    bounds = {}
    def visit(prefix):
        if prefix in leaf:
            span = leaf[prefix], leaf[prefix] + 1
        else:
            left, right = visit(prefix + '0'), visit(prefix + '1')
            need(left[1] == right[0], 'Disjoint source interval')
            span = left[0], right[1]
        bounds[prefix] = span
        return span
    need(visit('') == (0, len(rows)), 'Source size')
    def jump(word, edge, count):
        for j in range(len(word) - 1, -1, -1):
            if word[j] == edge:
                count -= 1
                if count == 0:
                    return bounds[word[:j]][int(edge == '0')] % len(rows)
        return 0
    result = []
    for i, (word, op, arg) in enumerate(rows):
        after = (i + 1) % len(rows)
        result.append([jump(word, '0', 1), after] if op == 'CD' else
                      [jump(word, '0', arg)] if op == 'CB' else
                      [jump(word, '1', arg)] if op == 'CC' else
                      [after] if op == 'CI' else [])
    return result

def check(parent_path, child_path, source_path):
    parent, child = parse(parent_path), parse(child_path)
    a, hash_a, used = run(parent, 48140)
    b, hash_b, _ = run(child, 48140)
    need(a == b and hash_a == hash_b, 'Blank startup differs')
    need(b[:2] == (84, -2), 'Startup state/head')
    changed = {key for key in set(parent) | set(child) if parent.get(key) != child.get(key)}
    need(not used.intersection(changed), 'Startup visits an edited row')
    source = json.loads(Path(source_path).read_text())
    need(source[136] == ['001100110101010', 'CI', 1], 'Source entry changed')
    registers = [1, 0, 13, 0, 0, 1, 0, 0, 1]
    physical, permutation = [0] * 9, (6, 2, 0, 4, 3, 7, 8, 5, 1)
    for i, position in enumerate(permutation):
        physical[position] = registers[i]
    wanted = {-3, 54} | {-2 + i for i, bit in enumerate(source[136][0]) if bit == '1'}
    position = 55
    for value in physical + [1] * 43:
        wanted.update(range(position + 1, position + value + 2))
        position += value + 2
    need(b[2] == wanted, 'Whole tape differs from the calibrated canonical frame')
    graph, regs, ordinal, trace = ordinal_graph(source), [1, 0, 4, 0, 0, 1, 0, 0, 1], 106, []
    for _ in range(141):
        before = ordinal, regs.copy()
        word, op, arg = source[ordinal]
        if op == 'CI':
            regs[arg] += 1
            ordinal = graph[ordinal][0]
        elif op == 'CD':
            positive = regs[arg] > 0
            regs[arg] -= int(positive)
            ordinal = graph[ordinal][int(positive)]
        elif op in ('CB', 'CC'):
            ordinal = graph[ordinal][0]
        else:
            raise ValueError('Unexpected halt in source prefix')
        trace.append([*before, ordinal, regs.copy()])
    need((ordinal, regs) == (136, registers), 'Protected source-prefix bridge')
    return {'status': 'EXACT_STARTUP_PASS', 'literal_steps': 48140,
            'state': 84, 'head': -2, 'header': 54, 'header_distance': 56,
            'source_ordinal': 136, 'source_address': source[136][0],
            'logical_registers': registers, 'spares': [1] * 43,
            'complete_tape_one_cells': sorted(wanted), 'zero_exterior': True,
            'trace_sha256': hash_b, 'changed_row_visits': 0,
            'source_seed_ordinal': 106, 'source_seed': [1, 0, 4, 0, 0, 1, 0, 0, 1],
            'source_prefix_steps': 141, 'source_prefix_trace': trace,
            'candidate_sha256': hashlib.sha256(Path(child_path).read_bytes()).hexdigest(),
            'source_sha256': hashlib.sha256(Path(source_path).read_bytes()).hexdigest(),
            'scope': 'Exact finite startup and source-prefix bridge; not an unbounded proof search.'}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('parent', 'candidate', 'source', 'output'):
        parser.add_argument(name, type=Path)
    args = parser.parse_args()
    result = check(args.parent, args.candidate, args.source)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print('EXACT_STARTUP_PASS', result['candidate_sha256'])
