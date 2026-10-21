#!/usr/bin/env python3
"""Independently audit the K216 command-tag permutation at source level.

Python 3 standard library only. The checks concern finite source structure,
all primitive control-flow cases, and symbolic command wire formats. Arithmetic
macro contracts and the all-natural consistency calibration are mathematical
dependencies documented in source_calibration.tex. No TM simulation occurs here.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path

PINS = {
    'baseline219': '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',
    'frozen202': 'abb7229877759170b61dfcfe21ca0889b3df2f91f4215383817a125eb0f8996c',
    '210': '8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc',
    '120': 'ee1f7c7cb216a80315449371b040ee094728a655439954225ed4be4635296680',
}
COMMANDS = ('MP', 'DROP', 'NIP')
BODY_PATHS = ('111', '110101', '110100101')
AX_PATH = '1101001001'
DISPATCH_PATH = '1100'

def sha(raw): return hashlib.sha256(raw).hexdigest()
def leaf(t): return isinstance(t[0], str)
def sites(t, p=''):
    return [(p, *t)] if leaf(t) else sites(t[0], p+'0') + sites(t[1], p+'1')
def parse(rr):
    trie = {}
    for p, op, r in rr:
        t = trie
        for bit in p:
            assert bit in '01'
            assert 'leaf' not in t
            t = t.setdefault(bit, {})
        assert not t
        assert op in ('CI', 'CD', 'CB', 'CC', 'CH')
        assert r is None if op == 'CH' else isinstance(r, int) and r >= 0
        t['leaf'] = (op, r)
    def finish(t):
        if 'leaf' in t:
            assert set(t) == {'leaf'}
            return t['leaf']
        assert set(t) == {'0', '1'}
        return finish(t['0']), finish(t['1'])
    ans = finish(trie)
    assert [list(r) for r in sites(ans)] == rr
    return ans
@lru_cache(None)
def width(t): return 1 if leaf(t) else width(t[0]) + width(t[1])
@lru_cache(None)
def boundary(t):
    if leaf(t):
        op, r = t
        if op == 'CD': return 1, 0
        if op == 'CB': return r, 0
        if op == 'CC': return 0, r
        return 0, 0
    a, b = boundary(t[0]), boundary(t[1])
    return max(a[0]-1, b[0], 0), max(a[1], b[1]-1, 0)
def seq(ts):
    assert ts
    return ts[0] if len(ts) == 1 else (ts[0], seq(ts[1:]))
def extract(t, lo, hi):
    chunks = []
    def go(q, i=0):
        j = i + width(q)
        if j <= lo or hi <= i: return
        if lo <= i and j <= hi:
            assert boundary(q) == (0, 0)
            chunks.append(q)
            return
        assert not leaf(q)
        go(q[0], i)
        go(q[1], i+width(q[0]))
    go(t)
    assert sum(map(width, chunks)) == hi-lo
    return seq(chunks)
def noncommon_reference(t):
    a = extract(t, 40, 66)
    read_d = extract(t, 23, 37)
    read_h = extract(t, 121, 135)
    edits = {
        (23, 37): None, (121, 135): None, (161, 194): a,
        (194, 221): (read_h, extract(t, 194, 221)),
        (221, 247): (read_d, a), (4652, 4678): (read_d, a),
    }
    used = {}
    def go(q, i=0):
        j = i + width(q)
        overlaps = [(rg, v) for rg, v in edits.items()
                    if not (j <= rg[0] or rg[1] <= i)]
        if not overlaps: return q
        for (lo, hi), v in overlaps:
            if lo <= i and j <= hi:
                assert boundary(q) == (0, 0)
                if i == lo:
                    used[lo, hi] = used.get((lo, hi), 0) + 1
                    return v
                return None
        assert not leaf(q)
        a, b = go(q[0], i), go(q[1], i+width(q[0]))
        if a is None:
            if b is not None: assert boundary(b) == (0, 0)
            return b
        if b is None:
            assert boundary(a) == (0, 0)
            return a
        return a, b
    result = go(t)
    assert used == {rg: 1 for rg in edits}
    return result

def structured_graph(t):
    count = width(t)
    out = []
    def target(stack, k): return stack[k-1] if k <= len(stack) else 0
    def go(q, i, breaks, continues):
        if leaf(q):
            op, r = q
            nxt = (i+1) % count
            if op == 'CI': dest = (nxt,)
            elif op == 'CD': dest = (target(breaks, 1), nxt)
            elif op == 'CB': dest = (target(breaks, r),)
            elif op == 'CC': dest = (target(continues, r),)
            else: dest = ()
            out.append((op, r if op in ('CI', 'CD', 'CH') else None, dest))
            return
        go(q[0], i, ((i+width(q)) % count,)+breaks, continues)
        go(q[1], i+width(q[0]), breaks, (i,)+continues)
    go(t, 0, (), ())
    return out

def counter_graph(rr):
    lookup = {p: i for i, (p, op, r) in enumerate(rr)}
    depth = max(map(len, lookup))
    def dispatch(p):
        q = p + '0'*(depth+1)
        for k in range(1, len(q)+1):
            if q[:k] in lookup:
                assert '1' not in p[k:]
                return lookup[q[:k]]
        raise AssertionError('incomplete source tree')
    def successor(p):
        return format((int(p, 2)+1) % 2**len(p), f'0{len(p)}b') if p else ''
    def cut(p, bit, k):
        js = [j for j, b in enumerate(p) if b == bit]
        return p[:js[-k]] if len(js) >= k else ''
    out = []
    for p, op, r in rr:
        if op == 'CI': dest = (dispatch(successor(p)),)
        elif op == 'CD': dest = (dispatch(successor(cut(p, '0', 1))), dispatch(successor(p)))
        elif op == 'CB': dest = (dispatch(successor(cut(p, '0', r))),)
        elif op == 'CC': dest = (dispatch(cut(p, '1', r)),)
        else: dest = ()
        out.append((op, r if op in ('CI', 'CD', 'CH') else None, dest))
    return out

def at(t, path):
    for bit in path: t = t[int(bit)]
    return t

def permute(t, permutation):
    bodies = [at(t, p) for p in BODY_PATHS]
    assert [width(q) for q in bodies] == [106, 26, 26]
    assert all(boundary(q) == (0, 0) for q in bodies)
    changes = dict(zip(BODY_PATHS, (bodies[i] for i in permutation)))
    def go(q, p=''):
        if p in changes: return changes[p]
        if leaf(q): return q
        return go(q[0], p+'0'), go(q[1], p+'1')
    return go(t)

def metrics(t):
    seen = set()
    def go(q):
        if q in seen: return
        seen.add(q)
        if not leaf(q): go(q[0]); go(q[1])
    go(t)
    rr = sites(t)
    return {'dag_nodes': len(seen), 'leaf_occurrences': len(rr),
            'guarded_cases': sum(2 if op == 'CD' else 1 for _, op, _ in rr),
            'maximum_depth': max(len(p) for p, _, _ in rr),
            'maximum_zero_run': max(len(z) for p, _, _ in rr for z in p.split('1'))}

def entry(rr, prefix):
    return next(i for i, (p, _, _) in enumerate(rr) if p.startswith(prefix))

def selector_audit(t, permutation):
    rr = sites(t)
    graph = structured_graph(t)
    starts = {entry(rr, path): COMMANDS[permutation[j]] for j, path in enumerate(BODY_PATHS)}
    starts[entry(rr, AX_PATH)] = 'AX'
    first = next(i for i, (p, _, _) in enumerate(rr) if p == DISPATCH_PATH)
    outcomes = []
    # Three exact finite cases and the exhaustive symbolic residual case.
    for val in range(4):
        pc, current, steps = first, val, []
        while pc not in starts:
            op, reg, targets = graph[pc]
            assert (op, reg) == ('CD', 3)
            steps.append(pc)
            if current:
                current -= 1
                pc = targets[1]
            else:
                pc = targets[0]
            assert len(steps) <= 3
        if val < 3:
            assert starts[pc] == COMMANDS[permutation[val]] and current == 0
            condition = {'selector': val, 'residual_selector': 0}
        else:
            assert starts[pc] == 'AX' and current == 0 and len(steps) == 3
            condition = {'selector_minimum': 3, 'residual_selector': 'selector - 3'}
        outcomes.append({**condition, 'command': starts[pc], 'entry_ordinal': pc,
                         'decrement_test_ordinals': steps})
    # The fourth case is symbolic: it follows three positive tests, hence
    # applies to every original selector n >= 3 with residual n-3.
    inverse = {COMMANDS[permutation[j]]: j for j in range(3)}
    fields = {'MP': [inverse['MP'], 'x'], 'DROP': [inverse['DROP']],
              'NIP': [inverse['NIP']], 'AX': ['c+3', 'y', 'x']}
    def fold(fs, tail):
        for f in reversed(fs): tail = ['P', f, tail]
        return tail
    packed = {name: fold(fs, 'R') for name, fs in fields.items()}
    assert packed['AX'] == ['P', 'c+3', ['P', 'y', ['P', 'x', 'R']]]
    assert fold([3, 'Y', 1], 'R') == ['P', 3, ['P', 'Y', ['P', 1, 'R']]]
    return outcomes, fields, packed

def return_audit(t, permutation):
    """Check each closed body's ordinary continuation to the source root."""
    rr = sites(t)
    graph = structured_graph(t)
    results = []
    for j, path in enumerate(BODY_PATHS):
        start = entry(rr, path)
        pc = (start + width(at(t, path))) % len(rr)
        route, seen = [], set()
        while pc:
            assert pc not in seen, 'cyclic command return wrapper'
            seen.add(pc)
            op, _, targets = graph[pc]
            assert op in ('CB', 'CC') and len(targets) == 1
            route.append({'ordinal': pc, 'op': op, 'target': targets[0]})
            pc = targets[0]
        results.append({'command': COMMANDS[permutation[j]],
                        'body_entry': start, 'normal_return_wrappers': route,
                        'final_target': 0})
    assert sum(op == 'CH' for _, op, _ in rr) == 1
    return results

def load(path, pin):
    raw = Path(path).read_bytes()
    assert sha(raw) == PINS[pin], f'hash mismatch: {path}'
    return parse(json.loads(raw)), sha(raw)

def audit(args):
    baseline, hb = load(args.baseline219, 'baseline219')
    frozen, hf = load(args.frozen202, 'frozen202')
    candidate, hc = load(args.candidate, args.permutation)
    reference = noncommon_reference(baseline)
    reference_graph = structured_graph(reference)
    frozen_graph = structured_graph(frozen)
    assert reference_graph == counter_graph(sites(reference))
    assert frozen_graph == counter_graph(sites(frozen))
    assert reference_graph == frozen_graph, 'frozen202 differs from calibrated reference'
    permutation = tuple(map(int, args.permutation))
    assert sorted(permutation) == [0, 1, 2]
    assert candidate == permute(frozen, permutation), 'candidate is not the exact branch permutation'
    cg = structured_graph(candidate)
    assert cg == counter_graph(sites(candidate))
    m = metrics(candidate)
    assert (m['dag_nodes'], m['leaf_occurrences'], m['maximum_depth'], m['maximum_zero_run']) == (202, 4751, 44, 6)
    # All paths external to the three replacement bodies remain literal.
    external = lambda t: [r for r in sites(t) if not any(r[0].startswith(p) for p in BODY_PATHS)]
    assert external(candidate) == external(frozen)
    assert at(candidate, AX_PATH) == at(frozen, AX_PATH)
    outcomes, fields, packed = selector_audit(candidate, permutation)
    result = {'status': 'PASS_EXACT_SOURCE_COMMAND_PERMUTATION',
        'baseline219_sha256': hb, 'frozen202_sha256': hf, 'candidate_sha256': hc,
        'permutation': args.permutation,
        'reference_metrics': metrics(reference), 'frozen_metrics': metrics(frozen),
        'candidate_metrics': m, 'all_primitive_guarded_cases_checked': m['guarded_cases'],
        'reference_cfg_sha256': sha((json.dumps(reference_graph, separators=(',', ':'))+'\n').encode()),
        'candidate_cfg_sha256': sha((json.dumps(cg, separators=(',', ':'))+'\n').encode()),
        'independent_cfg_resolvers': ['structured ancestor stacks', 'binary address counter'],
        'literal_external_primitive_occurrences': len(external(candidate)),
        'AX_subtree_unchanged': True, 'body_paths_in_tag_order': list(BODY_PATHS),
        'body_boundary_demands': [list(boundary(at(candidate, p))) for p in BODY_PATHS],
        'selector_partition': outcomes, 'wire_fields': fields,
        'normal_return_routes': return_audit(candidate, permutation),
        'halting_primitive_occurrences': 1,
        'symbolic_command_packing': packed,
        'cofinal_padding_packing': ['P', 3, ['P', 'Y', ['P', 1, 'R']]],
        'scope': 'Finite source structure and exhaustive guarded control graph; mathematical all-natural macro and calculus contracts are inherited; no binary runtime or bootstrap claim.'}
    text = json.dumps(result, indent=2)+'\n'
    if args.output: Path(args.output).write_text(text)
    print(text, end='')

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline219', required=True)
    ap.add_argument('--frozen202', required=True)
    ap.add_argument('--candidate', required=True)
    ap.add_argument('--permutation', choices=['210', '120'], required=True)
    ap.add_argument('--output')
    audit(ap.parse_args())
