#!/usr/bin/env python3
"""Independent audit using subtree ordinal intervals, not rotation helpers.

Parses Program.lean directly. Resolves each source jump by locating the
selected ancestor and taking its first leaf or the leaf after its interval.
No source module, optimizer, allocator or original graph implementation is
imported. Outputs only finite source facts, never TM state claims.
"""
import hashlib
import json
import re
from collections import Counter
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]
OP = {'inc': 'CI', 'dec': 'CD', 'breakTo': 'CB', 'continueTo': 'CC', 'halt': 'CH'}


def lean_rows(path):
    env = {}
    for name, body in re.findall(r'^def (\w+) : Tree := (.*)$', path.read_text(), re.M):
        tokens = re.findall(r'\.\w+|\w+|[()]', body)
        pos = 0

        def expression():
            nonlocal pos
            token = tokens[pos]
            pos += 1
            if token == '(':
                result = expression()
                if tokens[pos] != ')':
                    raise ValueError('Unbalanced Lean tree syntax')
                pos += 1
                return result
            if token == '.node':
                return ('node', expression(), expression())
            if token == '.leaf':
                return expression()
            if token.startswith('.'):
                op = token[1:]
                if op not in OP:
                    raise ValueError('Unknown source operation')
                arg = None
                if op != 'halt':
                    arg = int(tokens[pos])
                    pos += 1
                return (OP[op], arg)
            return env[token]

        env[name] = expression()
        if pos != len(tokens):
            raise ValueError('Unparsed source suffix')
    result = []

    def flatten(t, path):
        if t[0] == 'node':
            flatten(t[1], path + '0')
            flatten(t[2], path + '1')
        else:
            result.append([path, *t])

    flatten(env['trie'], '')
    return result


def audit(rows):
    paths = [r[0] for r in rows]
    if paths != sorted(paths) or len(set(paths)) != len(rows):
        raise ValueError('Leaves not distinct and ordered')
    leaves = {p: (i, op, arg) for i, (p, op, arg) in enumerate(rows)}
    prefixes = {p[:j] for p in paths for j in range(len(p) + 1)}
    intervals = {}
    intern = {}
    unique_nodes = set()

    def build(p):
        if p in leaves:
            if p + '0' in prefixes or p + '1' in prefixes:
                raise ValueError('A leaf prefixes another leaf')
            i, op, arg = leaves[p]
            signature = ('leaf', op, arg)
            bounds = (i, i + 1)
        else:
            if p + '0' not in prefixes or p + '1' not in prefixes:
                raise ValueError('Not a full binary source tree')
            l = build(p + '0')
            r = build(p + '1')
            if intervals[p + '0'][1] != intervals[p + '1'][0]:
                raise ValueError('Noncontiguous leaf blocks')
            signature = ('node', l, r)
            bounds = (intervals[p + '0'][0], intervals[p + '1'][1])
        key = intern.setdefault(signature, len(intern))
        if signature[0] == 'node':
            unique_nodes.add(key)
        intervals[p] = bounds
        return key

    build('')

    def cut(p, bit, count):
        if count == 0:
            return p
        for j in range(len(p) - 1, -1, -1):
            if p[j] == bit:
                count -= 1
                if count == 0:
                    return p[:j]
        raise ValueError('Source control escapes without a selected ancestor')

    def after_interval(p):
        endpoint = intervals[p][1]
        return endpoint if endpoint < len(rows) else None

    graph = []
    for i, (p, op, arg) in enumerate(rows):
        if op == 'CI':
            instruction = ['inc', arg, after_interval(p)]
        elif op == 'CD':
            instruction = ['dec', arg, after_interval(cut(p, '0', 1)), after_interval(p)]
        elif op == 'CB':
            instruction = ['jump', after_interval(cut(p, '0', arg))]
        elif op == 'CC':
            instruction = ['jump', intervals[cut(p, '1', arg)][0]]
        elif op == 'CH':
            instruction = ['halt']
        else:
            raise ValueError('Unknown operation')
        graph.append(instruction)
    maxzero = max(len(run) for p in paths for run in p.split('1'))
    info = {
        'leaf_count': len(rows),
        'distinct_internal_nodes': len(unique_nodes),
        'max_path_length': max(map(len, paths)),
        'max_consecutive_path_zeros': maxzero,
        'source_site_25': rows[25],
        'operation_counts': dict(sorted(Counter(r[1] for r in rows).items())),
        'ordinal_cfg_sha256': hashlib.sha256(json.dumps(graph, separators=(',', ':')).encode()).hexdigest(),
    }
    return graph, info


def run(graph, steps=100000):
    pc, regs = 25, [2, 0, 0, 0, 0, 0, 0, 0, 0]
    for step in range(steps):
        if pc is None:
            return {'status': 'root_exit', 'steps': step, 'pc': None, 'registers': regs}
        instruction = graph[pc]
        if instruction[0] == 'halt':
            return {'status': 'halt', 'steps': step, 'pc': pc, 'registers': regs}
        if instruction[0] == 'inc':
            regs[instruction[1]] += 1
            pc = instruction[2]
        elif instruction[0] == 'dec':
            r = instruction[1]
            if regs[r] == 0:
                pc = instruction[2]
            else:
                regs[r] -= 1
                pc = instruction[3]
        else:
            pc = instruction[1]
    return {'status': 'step_limit', 'steps': steps, 'pc': pc, 'registers': regs}


def main():
    upstream = BASE / 'data/Program.lean'
    original = lean_rows(upstream)
    baseline, info = audit(original)
    info['file_sha256'] = hashlib.sha256(upstream.read_bytes()).hexdigest()
    info['sample_source_run'] = run(baseline)
    results = {'upstream': info}
    files = [
        'source_reductions/source157.json',
        'source_reductions/layout158.json',
        'source_reductions/essential158.json',
    ]
    all_passed = True
    for name in files:
        file = BASE / name
        rows = json.loads(file.read_text())
        graph, info = audit(rows)
        info['file_sha256'] = hashlib.sha256(file.read_bytes()).hexdigest()
        info['same_leaf_operations_in_order'] = [r[1:] for r in rows] == [r[1:] for r in original]
        info['same_complete_ordinal_cfg'] = graph == baseline
        info['sample_source_run'] = run(graph)
        info['sample_run_matches'] = info['sample_source_run'] == results['upstream']['sample_source_run']
        info['exact_site25_path_preserved'] = rows[25] == original[25]
        results[name] = info
        all_passed &= info['same_complete_ordinal_cfg'] and info['same_leaf_operations_in_order']
    result = {'all_cfg_checks_passed': all_passed, 'results': results,
              'method': 'Independent Lean parser; subtree ordinal-interval control resolver; no imported optimizer modules.',
              'scope': 'Finite source graphs only, not physical machine counts or verified TM simulation.'}
    out = Path(__file__).with_name('source_audit_receipt.json')
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0 if all_passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
