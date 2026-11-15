#!/usr/bin/env python3
"""Inspect the exact finite data used by relative_ORH.tex.

This supplements full literal replay. It does not replace the event-calculus
soundness proof or certify a new Lean theorem. All input directories are
read-only; only --output is written. Standard library plus the attributed
parent's two source/runtime helper modules are used.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib.util
import json


def require(test, explanation):
    if not test:
        raise AssertionError(explanation)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        require((q, b) not in rows and b in (0, 1) and w in (0, 1)
                and d in ('L', 'R'), 'literal row')
        rows[q, b] = w, d, t
    states = {q for q, b in rows}
    require(len(states) == 194 and set(rows) ==
            {(q, b) for q in states for b in (0, 1)}, '194 complete controls')
    require({t for w, d, t in rows.values()} - states == {254}, 'native halt')
    return rows


def local_run(rows, q, head, tape, steps):
    tape = dict(tape)
    trace = []
    for _ in range(steps):
        bit = tape.get(head, 0)
        w, d, target = rows[q, bit]
        trace.append([q, head, bit, w, d, target])
        tape[head] = w
        head += 1 if d == 'R' else -1
        q = target
    return (q, head, tape), trace


def check_reader(rows, words):
    result = []
    for word, target in words:
        q = 213
        trace = []
        for c in word:
            bit = int(c)
            w, d, nxt = rows[q, bit]
            require((w, d) == (bit, 'R'), 'reader preserves each consumed bit')
            trace.append([q, bit, nxt])
            q = nxt
        require(q == target, 'reader target')
        result.append({'word': word, 'target': target, 'trace': trace})
    require(sum(2 ** (3-len(word)) for word, _ in words) == 8,
            'reader code is complete')
    require(all(not b.startswith(a) for a, _ in words for b, _ in words if a != b),
            'reader code is prefix-free')
    return result


def inspect(folder, reference):
    source = module(reference/'source_language.py', 'relative_source')
    runtime = module(reference/'independent_runtime.py', 'relative_runtime')
    sites = read(folder/'sites.json')
    tags = {'inc': 'CI', 'dec': 'CD', 'breakTo': 'CB',
            'continueTo': 'CC', 'halt': 'CH'}
    mapped = [[p, tags[op], a] for p, op, a in sites]
    source.tree(mapped)
    graph, _ = source.graph_arithmetic(mapped)
    require(graph == source.graph_intervals(mapped), 'independent source resolvers')
    names = {'identity': 'jump', 'increment': 'inc', 'decrement': 'dec', 'halt': 'halt'}
    instructions = [[names[e[0]]] + e[1:] + targets for e, targets in graph]
    require(instructions == read(folder/'instructions.json'), 'literal source graph')
    receipt = read(folder/'independent/receipt.json')
    require(receipt['status'] == 'PASS', 'full replay receipt')
    for file, field in [('machine.tm', 'dense_sha256'),
                        ('machine.native.tm', 'native_sha256'),
                        ('independent/contracts.json', 'contracts_sha256')]:
        require(sha(folder/file) == receipt[field], 'replay input identity: '+file)
    require(receipt.get('complete_startup_tape_equal', receipt.get('whole_blank_startup')),
            'whole-tape startup replay')
    contracts = read(folder/'independent/contracts.json')
    required = [(i, positive) for i, (_, op, _) in enumerate(mapped)
                for positive in ([False, True] if op == 'CD' else [False])]
    require([(c['site'], c['positive']) for c in contracts] == required,
            'exact complete contract index')
    require(len(sites) == 3671 and len(contracts) == 4778, 'expected source size')
    maximum = [0] * 13
    endpoints = halts = 0
    for c in contracts:
        ds, motion = c['duration'], c['motion']
        require(len(ds) == len(motion) == 13, 'affine slots')
        require(all(type(x) is int and x >= 0 for x in ds) and ds[0] >= 3,
                'positive affine duration before source halt')
        maximum = list(map(max, maximum, ds))
        i, positive = c['site'], c['positive']
        pc, op, arg = mapped[i]
        effect, targets = graph[i]
        if op == 'CH':
            require(ds == [3] + [0]*12 and not positive
                    and effect == ['halt'] and not targets, 'canonical halt contract')
            halts += 1
            continue
        overflow = 0
        if op == 'CI' or (op == 'CD' and positive):
            successor, overflow = runtime.inc(pc)
        elif op in ('CD', 'CB'):
            successor, overflow = runtime.inc(runtime.strip(pc, '0', arg if op == 'CB' else 1))
        else:
            require(op == 'CC', 'source opcode')
            successor = runtime.strip(pc, '1', arg)
        target = mapped[targets[int(positive)] if op == 'CD' else targets[0]][0]
        require(len(successor) <= 48 and len(target) <= 48, 'header coverage')
        require(successor.ljust(48, '0') == target.ljust(48, '0'), 'padded endpoint')
        require(overflow == 0 and motion == [0]*13, 'head and gap closure')
        endpoints += 1
    reg, spare = max(maximum[2:11]), max(maximum[11:13])
    alpha = maximum[0] + 2*reg + 78*spare
    beta = maximum[1] + reg + 3*spare
    result = {'status': 'PASS', 'sites': len(sites), 'contracts': len(contracts),
              'opcounts': dict(Counter(op for _, op, _ in sites)),
              'nonhalting_endpoints': endpoints, 'halt_outcomes': halts,
              'max_address_length': max(len(p) for p, _, _ in sites),
              'max_duration_coefficients': maximum,
              'duration_constant_minimum': min(c['duration'][0] for c in contracts),
              'register_coefficient': reg, 'spare_width_coefficient': spare,
              'blank_run_duration_bound': {'alpha': alpha, 'beta': beta,
                                          'formula': 'D(z_k) <= alpha + beta*k'},
              'physical_time_bound': {'startup': receipt['startup_steps'],
                                      'alpha': alpha, 'beta': beta,
                                      'formula': 'startup + alpha*k + beta*k*(k-1)/2'},
              'hashes': {f: sha(folder/f) for f in
                         ('machine.tm', 'machine.native.tm', 'instructions.json',
                          'sites.json', 'independent/contracts.json', 'independent/receipt.json')}}
    return sites, instructions, result


def main(args):
    old, new = table(args.parent/'machine.native.tm'), table(args.candidate/'machine.native.tm')
    old_sites, old_ins, old_info = inspect(args.parent, args.reference)
    new_sites, new_ins, new_info = inspect(args.candidate, args.reference)
    require(old_ins == new_ins, 'same full source graph')
    require(all(a[1:] == b[1:] for a, b in zip(old_sites, new_sites)), 'same source operations')
    require(old_sites[25] == new_sites[25] == ['1000000', 'dec', 8], 'same initial site')
    history = []
    for bit, length in [(0, 3), (1, 2)]:
        tape = {-1: bit, 0: 0}
        a, ta = local_run(old, 69, 0, tape, length)
        b, tb = local_run(new, 69, 0, tape, length)
        require(a == b, 'history selector exact endpoint')
        require(a == (104, 1, tape) if bit == 0 else a == (90, 0, tape),
                'history selector intended endpoint')
        require(all(row[1] in (-1, 0) for row in ta+tb), 'history context not inspected')
        history.append({'history_bit': bit, 'steps': length, 'old': ta, 'new': tb,
                        'exit_control': a[0], 'exit_displacement': a[1]})
    result = {'status': 'PASS', 'scope': 'Finite bindings and affine envelope; written iPRA argument separate',
              'parent': old_info, 'candidate': new_info,
              'source_instruction_arrays_identical': True,
              'changed_source_addresses': sum(a[0] != b[0] for a, b in zip(old_sites, new_sites)),
              'history_selector_cases': history,
              'old_operand_reader': check_reader(old, [('00',104),('010',107),('011',98),('1',90)]),
              'new_operand_reader': check_reader(new, [('0',104),('10',107),('110',98),('111',90)]),
              'reference_hashes': {f: sha(args.reference/f) for f in
                                   ('source_language.py','independent_runtime.py')}}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status','source_instruction_arrays_identical',
                                          'changed_source_addresses')}, indent=2))
    for k in ('parent', 'candidate'):
        print(k, json.dumps(result[k]['physical_time_bound']))


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent', type=Path, default=root/'proof/relative_ORH_parent')
    ap.add_argument('--candidate', type=Path, default=root/'machines/PA194ORH')
    ap.add_argument('--reference', type=Path, default=root/'verification/vendor')
    ap.add_argument('--output', type=Path, default=root/'proof/relative_ORH_inspection.json')
    main(ap.parse_args())
