#!/usr/bin/env python3
"""Owned finite prototype. Parses fetched Lean as data; never executes its code.

This is evidence for a proposed Lean checker, NOT a replacement kernel proof.
"""
from __future__ import annotations
import hashlib
import itertools
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
OPS = {'node', 'inc', 'decnz', 'brk', 'cont', 'halt'}

def read_nodes():
    nodes = {}
    counts = {}
    for filename in ['Dag222.lean', 'Dag219.lean', 'DagDom.lean', 'DagPerm.lean']:
        text = (HERE / 'sources' / filename).read_text()
        rows = {}
        for line in text.splitlines():
            match = re.match(r'\s*\| (\d+) => (.*)$', line)
            if not match:
                continue
            edges = re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?:\s+(\d+))?', match[2])
            if len(edges) != 2:
                raise ValueError(('unexpected row', filename, line))
            pair = tuple((op, int(arg) if arg else 0) for op, arg in edges)
            if int(match[1]) in rows:
                raise ValueError(('duplicate row', filename, line))
            rows[int(match[1])] = pair
        counts[filename] = len(rows)
        nodes.update(rows)
    assert counts == {'Dag222.lean': 461, 'Dag219.lean': 7, 'DagDom.lean': 18, 'DagPerm.lean': 7}
    assert sorted(nodes) == list(range(487))
    return [nodes[n] for n in range(487)], counts

def leaf_summary(edge):
    op, arg = edge
    if op == 'node':
        raise ValueError('node is not a leaf')
    if op in {'brk', 'cont'} and arg <= 0:
        raise ValueError('zero break/continue')
    if op not in OPS or arg < 0:
        raise ValueError('invalid edge')
    return 0, 1 if op == 'decnz' else arg if op == 'brk' else 0, arg if op == 'cont' else 0

def analyze(nodes, root, canonical_height=True):
    """Visit every bounded node, including nodes unreachable from root.

    States: 0 unseen, 1 on DFS stack, 2 complete. A complete tuple holds
    canonical height, minimum B and minimum C. A separate completion rank
    can replace height in the WF witness without computing any max-height.
    """
    nn = len(nodes)
    if not 0 <= root < nn:
        raise ValueError('root out of range')
    states, memo, ranks, order = [0] * nn, [None] * nn, [0] * nn, []
    jobs = [('visit', n) for n in reversed(range(nn))]
    steps = 0
    while jobs:
        steps += 1
        if steps > 4 * nn:
            raise ValueError('finite work budget exceeded')
        mode, n = jobs.pop()
        if mode == 'finish':
            values = []
            for op, arg in nodes[n]:
                if op == 'node':
                    if states[arg] != 2:
                        raise ValueError('child not complete')
                    values.append(memo[arg])
                else:
                    values.append(leaf_summary((op, arg)))
            a, b = values
            height = 1 + max(a[0], b[0]) if canonical_height else len(order) + 1
            memo[n] = (height, max(max(a[1] - 1, 0), b[1]), max(a[2], max(b[2] - 1, 0)))
            states[n] = 2
            order.append(n)
            ranks[n] = len(order)
            continue
        if states[n] == 2:
            continue
        if states[n] == 1:
            raise ValueError('node cycle')
        states[n] = 1
        if len(nodes[n]) != 2:
            raise ValueError('non-binary node')
        jobs.append(('finish', n))
        children = []
        for edge in nodes[n]:
            op, arg = edge
            if op == 'node':
                if not 0 <= arg < nn:
                    raise ValueError('child out of range')
                children.append(('visit', arg))
            else:
                leaf_summary(edge)
        jobs.extend(reversed(children))
    assert all(s == 2 for s in states)
    if memo[root][0] > nn + 1:
        raise ValueError('root height exceeds decoder fuel')
    if memo[root][1:] != (0, 0):
        raise ValueError('break/continue escapes root')
    return {'summaries': memo, 'ranks': ranks, 'order': order, 'steps': steps}

def original_conditions(nodes, root, H, B, C):
    """Independent direct translation of RMEquiv.WF's finite inequalities."""
    nn = len(nodes)
    if not 0 <= root < nn or H[root] > nn + 1 or B[root] or C[root]:
        return False
    def edge(e):
        op, arg = e
        if op == 'node':
            if not 0 <= arg < nn:
                return None
            return H[arg], B[arg], C[arg]
        try:
            return leaf_summary(e)
        except ValueError:
            return None
    for n, pair in enumerate(nodes):
        a, b = map(edge, pair)
        if a is None or b is None:
            return False
        if not (a[0] < H[n] and b[0] < H[n] and a[1] <= B[n] + 1 and b[1] <= B[n] and a[2] <= C[n] and b[2] <= C[n] + 1):
            return False
    return True

def reference_scan(nodes, root):
    """Separate repeated readiness scan, without DFS or a supplied order."""
    nn = len(nodes)
    if not 0 <= root < nn:
        return False
    done = {}
    try:
        for _ in range(nn):
            for n, pair in enumerate(nodes):
                if n in done:
                    continue
                if any(op == 'node' and not 0 <= arg < nn for op, arg in pair):
                    return False
                if any(op == 'node' and arg not in done for op, arg in pair):
                    continue
                a, b = [done[arg] if op == 'node' else leaf_summary((op, arg)) for op, arg in pair]
                done[n] = (1 + max(a[0], b[0]), max(max(a[1]-1, 0), b[1]), max(a[2], max(b[2]-1, 0)))
    except ValueError:
        return False
    return len(done) == nn and done[root][1:] == (0, 0)

def accepted(nodes, root):
    try:
        analyze(nodes, root)
        return True
    except ValueError:
        return False

def run():
    if not __debug__:
        raise SystemExit('Refusing optimized Python: validation assertions must remain enabled.')
    for pin in json.loads((HERE/'SOURCE_PINS.json').read_text())['files']:
        filename = pin.get('local_filename', Path(pin['path']).name)
        data = (HERE/'sources'/filename).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if blob != pin['sha']:
            raise ValueError(('source pin mismatch', filename))
    nodes, counts = read_nodes()
    result = analyze(nodes, 0)
    H, B, C = map(list, zip(*result['summaries']))
    source = (HERE / 'sources' / 'KSource215WfData.lean').read_text()
    supplied = [list(map(int, re.search(r'def t' + key + r' : List Nat := \[([^]]*)\]', source, re.S)[1].replace('\n', ' ').split(','))) for key in ['H', 'B', 'C']]
    exact = {'t' + key: computed == given for key, computed, given in zip(['H', 'B', 'C'], [H, B, C], supplied)}
    assert all(exact.values())
    normalized_path = HERE/'sources/NormalizedKSource215Programs.lean'
    normalized_text = normalized_path.read_text()
    normalized_arrays = [list(map(int, re.search(r'def t' + key + r' : List Nat := \[([^]]*)\]', normalized_text, re.S)[1].replace('\n', ' ').split(','))) for key in ['H', 'B', 'C']]
    assert normalized_arrays == supplied
    assert len(re.findall(r'private theorem wf_part\d+ ', normalized_text)) == 16
    assert original_conditions(nodes, 0, H, B, C)
    assert original_conditions(nodes, 0, result['ranks'], B, C)
    rank_only = analyze(nodes, 0, canonical_height=False)
    rankH, rankB, rankC = map(list, zip(*rank_only['summaries']))
    assert rankH == result['ranks'] and rankB == B and rankC == C
    assert original_conditions(nodes, 0, rankH, rankB, rankC)
    reachable, todo = set(), [0]
    while todo:
        n = todo.pop()
        if n in reachable:
            continue
        reachable.add(n)
        todo += [m for op, m in nodes[n] if op == 'node']
    tests = []
    def reject(name, graph, root=0):
        try:
            analyze(graph, root)
        except ValueError as e:
            tests.append({'name': name, 'rejected': True, 'reason': str(e)})
            return
        raise AssertionError(('accepted invalid graph', name))
    reject('root exactly at bound', nodes, 487)
    reject('empty graph', [], 0)
    for name, n, edge in [('root self-cycle', 0, ('node', 0)), ('out of range child', 0, ('node', 487)), ('zero break', 0, ('brk', 0)), ('zero continue', 0, ('cont', 0))]:
        changed = nodes.copy()
        changed[n] = (edge, changed[n][1])
        reject(name, changed)
    dead = sorted(set(range(487)) - reachable)
    changed = nodes.copy()
    changed[dead[0]] = (('node', dead[0]), changed[dead[0]][1])
    reject('unreachable self-cycle', changed)
    reject('break in cdr escapes', [(('inc', 0), ('brk', 1))])
    reject('continue in car escapes', [(('cont', 1), ('inc', 0))])
    reject('break level 2 in car escapes', [(('brk', 2), ('inc', 0))])
    reject('continue level 2 in cdr escapes', [(('inc', 0), ('cont', 2))])
    positive = {
        'break level 1 in car is consumed': [(('brk', 1), ('inc', 0))],
        'continue level 1 in cdr is consumed': [(('inc', 0), ('cont', 1))],
        'decnz in car is consumed': [(('decnz', 0), ('inc', 0))],
        'out of range register is allowed by WF': [(('inc', 999999), ('halt', 0))],
    }
    assert all(accepted(g, 0) for g in positive.values())
    exhaustive_count = 0
    for nn in [1, 2]:
        alphabet = [('node', n) for n in range(nn)] + [('inc', 0), ('decnz', 0), ('brk', 0), ('brk', 1), ('brk', 2), ('cont', 0), ('cont', 1), ('cont', 2), ('halt', 0)]
        for flat in itertools.product(alphabet, repeat=2*nn):
            graph = [flat[i:i+2] for i in range(0, len(flat), 2)]
            a, b = accepted(graph, 0), reference_scan(graph, 0)
            assert a == b, graph
            if a:
                info = analyze(graph, 0)
                _, bs, cs = map(list, zip(*info['summaries']))
                assert original_conditions(graph, 0, info['ranks'], bs, cs)
            exhaustive_count += 1
    report = {
        'status': 'owned Python finite checks passed; no Lean compilation or generic soundness theorem claimed',
        'nodes': len(nodes), 'edges': 2*len(nodes), 'parsed_rows': counts,
        'root': 0, 'root_summary': result['summaries'][0], 'root_completion_rank': result['ranks'][0],
        'reachable_nodes': len(reachable), 'unreachable_nodes': dead,
        'fold_jobs': result['steps'], 'work_budget_from_counting_argument': 4*len(nodes),
        'computed_arrays_equal_supplied': exact,
        'normalized1426_lane_arrays_identical': True,
        'normalized1426_lane_WF_batches': 16,
        'normalized1426_lane_WF_data_module': 'KSource215Programs.lean',
        'normalized1426_lane_source_sha256': hashlib.sha256(normalized_path.read_bytes()).hexdigest(),
        'original_WF_inequalities_with_canonical_height': True,
        'original_WF_inequalities_with_completion_rank': True,
        'rank_only_variant_computes_no_max_height': True,
        'nonzero_break_nodes': [n for n, b in enumerate(B) if b],
        'nonzero_continue_nodes': [n for n, c in enumerate(C) if c],
        'negative_controls': tests, 'positive_controls': list(positive),
        'exhaustive_one_and_two_node_graphs': exhaustive_count,
        'exhaustive_check': 'DFS equals independent readiness scan; all accepts satisfy original WF inequalities with rank height',
        'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((HERE/'sources').iterdir()) if p.is_file()},
    }
    (HERE/'check_result.json').write_text(json.dumps(report, indent=2)+'\n')
    (HERE/'computed_summaries.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    run()
