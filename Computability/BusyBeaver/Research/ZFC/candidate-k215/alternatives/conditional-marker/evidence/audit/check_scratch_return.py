#!/usr/bin/env python3
"""Literal source/blank audit exposing the scratch-biased return error.

The source CFG resolver is implemented here independently of the received
packet's helper. Its finite checks support the separate all-natural proof.
"""
import argparse
import hashlib
import json
from pathlib import Path

from compare_tables import parse


def require(p, message):
    if not p:
        raise ValueError(message)


def cfg(rows):
    index = {r[0]: i for i, r in enumerate(rows)}
    spans = {}
    def interval(prefix):
        if prefix in index:
            i = index[prefix]
            result = i, i + 1
        else:
            left, right = interval(prefix + '0'), interval(prefix + '1')
            require(left[1] == right[0], 'noncontiguous source tree')
            result = left[0], right[1]
        spans[prefix] = result
        return result
    require(interval('') == (0, len(rows)), 'whole tree')
    def outward(path, bit, count):
        for i in range(len(path) - 1, -1, -1):
            if path[i] == bit:
                count -= 1
                if count == 0:
                    return spans[path[:i]][1] % len(rows) if bit == '0' else spans[path[:i]][0]
        return 0
    result = []
    for i, (path, op, k) in enumerate(rows):
        after = (i + 1) % len(rows)
        if op == 'CI':
            targets = [after]
        elif op == 'CD':
            targets = [outward(path, '0', 1), after]
        elif op == 'CB':
            targets = [outward(path, '0', k)]
        elif op == 'CC':
            targets = [outward(path, '1', k)]
        elif op == 'CH':
            targets = []
        else:
            raise ValueError('opcode')
        result.append((op, k, targets))
    return result


def distinct_subtrees(rows):
    leaves = {path: (op, k) for path, op, k in rows}
    seen = set()
    def descend(path):
        tree = (('leaf',) + leaves[path] if path in leaves else
                ('pair', descend(path + '0'), descend(path + '1')))
        seen.add(tree)
        return tree
    descend('')
    return len(seen)


def step(graph, pc, registers):
    op, k, edges = graph[pc]
    r = registers.copy()
    if op == 'CI':
        r[k] += 1
        return edges[0], r
    if op == 'CD':
        positive = r[k] > 0
        r[k] -= int(positive)
        return edges[int(positive)], r
    if op in ('CC', 'CB'):
        return edges[0], r
    raise ValueError('halting primitive has no successor')


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--packet', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    packet = a.packet
    sp = packet / 'candidates/scratch-biased/source.sites.json'
    tp = packet / 'candidates/scratch-biased/machine.native.tm'
    raw = sp.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == '2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a', 'exact source identity')
    require(hashlib.sha256(tp.read_bytes()).hexdigest() == 'f08bed9e62b9f43237b65c465d2f1bfc17474637b4b02785ca7f1813827bb0ce', 'exact table identity')
    rows = json.loads(raw)
    graph = cfg(rows)
    parent_raw = (packet / 'inputs/parent.sites.json').read_bytes()
    require(hashlib.sha256(parent_raw).hexdigest() == '05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922', 'exact parent source identity')
    parent = json.loads(parent_raw)
    parent_graph = cfg(parent)
    require([r[1:] for r in rows[25:4590]] == [r[1:] for r in parent[25:4590]], 'unchanged complete AX primitive word')
    require(graph[25:4590] == parent_graph[25:4590], 'unchanged complete AX ordinal CFG')
    require(rows[4697] == ['100111', 'CC', 3] and graph[4697][2] == [23], 'literal return destination')
    corrected = [r.copy() for r in rows]
    corrected[4697][2] = 4
    require(cfg(corrected)[4697][2] == [0], 'corrected CC4 would reach scheduler')
    require(distinct_subtrees(rows) == 201 and distinct_subtrees(corrected) == 203, 'literal subtree counts')
    pc, r = 4696, [1, 0, 3, 0, 0, 0, 0, 0, 0]
    trace = []
    while graph[pc][0] != 'CH':
        require(len(trace) < 100, 'witness bound')
        trace.append({'ordinal': pc, 'registers': r.copy(), 'instruction': rows[pc]})
        pc, r = step(graph, pc, r)
    require(pc == 4718 and len(trace) == 15, 'exact halt-primitive witness')
    halt_registers = r.copy()
    # These concrete corroborations are not the all-natural proof: the trace
    # never reads W, N, D, Y, or L, and the only variable loop clears T.
    corroborations = 0
    for top in range(12):
        for stack in (0, 1, 2, 3, 17, 1000000):
            x, v, steps = 4696, [9, top, stack, 0, 13, 0, 0, 8, 37], 0
            while graph[x][0] != 'CH':
                x, v = step(graph, x, v)
                steps += 1
            require(x == 4718 and steps == 2 * top + 15, 'variable-top corroboration')
            require(v[2] == stack, 'stack never read')
            corroborations += 1
    # Independently replay the entire literal blank prefix, then match the
    # abstract AX prefix using the independently resolved source graph.
    q, table = parse(tp)
    require(q == 74, 'native blank start')
    h, ones = 0, set()
    for _ in range(69744):
        bit = int(h in ones)
        w, direction, q = table[q, bit]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += direction
    saved = json.loads((packet / 'evidence/simple_offset6_zero_startup.json').read_text())['startup_frames'][0]
    require((q, h, sorted(ones)) == (84, -2, saved['one_cells']), 'entire blank endpoint')
    pc, r = 25, [1, 0, 3, 0, 0, 0, 0, 0, 0]
    for _ in range(172):
        pc, r = step(graph, pc, r)
    require(pc == 64 and r == saved['logical'] == [1, 4, 0, 0, 0, 0, 3, 10, 0], 'exact AX prefix')
    result = {
        'status': 'SCRATCH_BIASED_SOURCE_CALIBRATION_REJECTED',
        'source_sha256': hashlib.sha256(raw).hexdigest(),
        'table_sha256': hashlib.sha256(tp.read_bytes()).hexdigest(),
        'parent_source_sha256': hashlib.sha256(parent_raw).hexdigest(),
        'return': {'ordinal': 4697, 'path': '100111', 'operation': 'CC3', 'target': 23, 'intended_target': 0},
        'corrected_return': {'operation': 'CC4', 'target': 0, 'source_dag_nodes': 203},
        'source_dag_nodes': 201,
        'unchanged_AX_span': [25, 4590], 'AX_exit': 4696,
        'witness_steps_to_CH': len(trace), 'CH_ordinal': 4718,
        'trace': trace, 'terminal_registers': halt_registers,
        'all_natural_return_statement': 'For arbitrary N,T,W,D,Y,L and A=H=X=0, ordinal4696 reaches CH4718 after 2*T+15 nonhalting primitive transitions; W is never read.',
        'finite_return_corroborations': corroborations,
        'whole_blank_prefix_steps': 69744,
        'abstract_AX_prefix_steps': 172,
        'AX_seed': [1, 0, 3, 0, 0, 0, 0, 0, 0],
        'blank_halt_proof_boundary': 'Complete AX word/CFG is identical to the inherited terminating AX. Its zero-parameter seed exits with A=H=X=0 and T=0. The literal 15-step suffix reaches CH. Together with the separately supplied full primitive runtime, this proves eventual blank halting. No complete step count through the huge unary AX execution is claimed.',
        'scope': 'Independent literal finite checks plus the stated all-natural argument; no new proof-assistant theorem.'
    }
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('trace',)}, indent=2))


if __name__ == '__main__':
    main()
