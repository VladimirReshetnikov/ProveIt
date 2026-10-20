#!/usr/bin/env python3
"""Independent finite certificate for closed reassociation and the 85/212 fold.

Standard library only. This proves exact finite syntactic obligations; the
accompanying argument lifts the local whole-tape blocks to an unbounded
stuttering simulation. It is not a replacement for the source/runtime bridge.
"""
from __future__ import annotations
import argparse, functools, hashlib, json
from pathlib import Path


def need(p, why):
    if not p:
        raise ValueError(why)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def table(p):
    need(p.read_text().splitlines()[0] == '#! start 0', 'unexpected initial native state')
    rows = {}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, r, w, d, z = line.split()
        k = (int(q), int(r))
        need(k not in rows, 'duplicate native transition')
        need(d in ('L', 'R'), 'bad direction')
        rows[k] = (int(w), -1 if d == 'L' else 1, int(z))
    return rows


def syntax(p):
    rows = json.loads(p.read_text())
    d = {}
    for address, op, arg in rows:
        need(address and set(address) <= {'0', '1'}, 'bad source address')
        n = d
        for bit in address:
            need('leaf' not in n, 'overlapping source address')
            n = n.setdefault(bit, {})
        need(not n, 'duplicate source address')
        n['leaf'] = (op, arg)
    def unpack(n):
        if 'leaf' in n:
            need(set(n) == {'leaf'}, 'leaf has children')
            return n['leaf']
        need(set(n) == {'0', '1'}, 'source tree not full')
        return unpack(n['0']), unpack(n['1'])
    root = unpack(d)
    need(sites(root) == rows, 'source ordinals not canonical')
    return root


def leaf(t):
    return isinstance(t[0], str)


@functools.cache
def word(t):
    return (t,) if leaf(t) else word(t[0]) + word(t[1])


def sites(t, address=''):
    return [[address, *t]] if leaf(t) else sites(t[0], address+'0') + sites(t[1], address+'1')


@functools.cache
def boundary(t):
    if leaf(t):
        op, k = t
        if op == 'CD': return 1, 0, False
        if op == 'CB': return k, 0, False
        if op == 'CC': return 0, k, False
        return 0, 0, op == 'CH'
    a, b = boundary(t[0]), boundary(t[1])
    return max(a[0]-1, 0, b[0]), max(a[1], b[1]-1, 0), a[2] or b[2]


@functools.cache
def nodes(t):
    return frozenset([t]) if leaf(t) else frozenset([t]) | nodes(t[0]) | nodes(t[1])


def metrics(t):
    ss = sites(t)
    return {'dag_nodes': len(nodes(t)), 'leaf_occurrences': len(ss),
            'maximum_depth': max(len(p) for p, _, _ in ss),
            'maximum_zero_run': max(len(x) for p, _, _ in ss for x in p.split('1'))}


def subtree(t, p):
    for c in p:
        need(not leaf(t), 'subtree address below leaf')
        t = t[int(c)]
    return t


def continuation_graph(t):
    """Resolve controls with explicit semantic continuations, without address cuts.

    In a pair (A,B), break1 from A exits the pair, and continue1 from B
    restarts the pair. Other breaks/continues follow the outer continuation
    stacks. The outermost normal/break/continue target is the root ordinal0.
    """
    out = [None] * len(word(t))
    def compile_at(n, start, normal, breaks, continues):
        if not leaf(n):
            a, b = n
            mid = start + len(word(a))
            compile_at(a, start, mid, (normal,)+breaks, continues)
            compile_at(b, mid, normal, breaks, (start,)+continues)
            return
        op, k = n
        def choose(xs, i): return xs[i-1] if i <= len(xs) else 0
        if op == 'CI': effect, targets = ('increment', k), (normal,)
        elif op == 'CD': effect, targets = ('decrement', k), (choose(breaks, 1), normal)
        elif op == 'CB': effect, targets = ('identity', None), (choose(breaks, k),)
        elif op == 'CC': effect, targets = ('identity', None), (choose(continues, k),)
        else:
            need(op == 'CH', 'bad opcode')
            effect, targets = ('halt', None), ()
        need(out[start] is None, 'duplicate ordinal')
        out[start] = (effect, targets)
    compile_at(t, 0, 0, (), ())
    need(all(x is not None for x in out), 'unresolved ordinal')
    need(all(0 <= x < len(out) for _, ss in out for x in ss), 'out-of-range target')
    return out


def local_block(T, marker, scanned):
    # The unknown exterior tape is never accessed. Keeping explicit zero cells
    # makes the locality check independent of sparse-tape defaults.
    tape = {-1: marker, 0: scanned}
    q, h = 85, 0
    target = 98 if scanned == 0 else (12 if marker == 0 else 150)
    steps = []
    while (q, h) != (target, 1):
        need(len(steps) < 10, 'local block does not finish')
        need(h in tape, 'block touches unknown exterior tape')
        r = tape[h]
        w, d, z = T[q, r]
        steps.append({'state': q, 'head': h, 'read': r, 'write': w,
                      'move': d, 'next_state': z})
        tape[h] = w
        q, h = z, h+d
    need(tape == {-1: marker, 0: scanned}, 'block changed tape')
    return {'preceding_bit': marker, 'scanned_bit': scanned,
            'steps': steps, 'step_count': len(steps), 'final_state': q,
            'final_head': h, 'tape_preserved': True,
            'read_and_write_window': [-1, 0]}


def main():
    ap = argparse.ArgumentParser()
    for name in ('parent-sites', 'old-sites', 'new-sites', 'old-table', 'unfolded-table', 'new-table', 'out'):
        ap.add_argument('--'+name, type=Path, required=True)
    a = ap.parse_args()
    old, new = syntax(a.old_sites), syntax(a.new_sites)
    parent = syntax(a.parent_sites)
    original, unfolded, folded = table(a.old_table), table(a.unfolded_table), table(a.new_table)
    p = '110100100110111111110'
    left = subtree(old, p)
    A, B = left[0]
    C = left[1]
    need([len(word(x)) for x in (A,B,C)] == [26,19,7], 'wrong three factors')
    need(all(boundary(x) == (0,0,False) for x in (A,B,C)), 'nonclosed factor')
    right = (A, (B,C))
    occurrences = []
    def rewrite(t, at=''):
        if t == left:
            occurrences.append(at)
            return right
        if leaf(t): return t
        return rewrite(t[0], at+'0'), rewrite(t[1], at+'1')
    need(rewrite(old) == new, 'new source is not the specified global reassociation')
    need(len(occurrences) == 5, 'wrong occurrence count')
    need(word(old) == word(new), 'primitive word changed')
    g1, g2 = continuation_graph(old), continuation_graph(new)
    need(g1 == g2, 'primitive control graph changed')
    need(word(parent) == word(new), 'primitive word differs from pinned K219')
    need(continuation_graph(parent) == g2, 'control graph differs from pinned K219')
    need(metrics(parent) == {'dag_nodes':206, 'leaf_occurrences':4744,
         'maximum_depth':38, 'maximum_zero_run':6}, 'parent source metrics changed')
    need(metrics(old) == metrics(new) == {'dag_nodes':205, 'leaf_occurrences':4744,
         'maximum_depth':38, 'maximum_zero_run':6}, 'source metrics changed')
    expected = dict(original)
    expected[188,0] = (0,1,166)
    expected[188,1] = (1,1,12)
    need(expected == unfolded, 'unfolded table differs outside188')
    incoming = {q: [(k,v) for k,v in unfolded.items() if v[2] == q] for q in (85,212)}
    need(incoming[85] == [((155,0),(0,1,85))], 'old85 does not have its unique0-marker entry')
    need(incoming[212] == [((177,1),(1,1,212))], 'old212 does not have its unique1-marker entry')
    need(unfolded[85,0] == unfolded[212,0] == (0,1,98), 'different read0 behavior')
    need(unfolded[85,1] == (1,1,12), 'wrong old85/read1')
    need(unfolded[212,1] == (1,1,150), 'wrong old212/read1')
    expected = {(q,r):(w,d,85 if z == 212 else z)
                for (q,r),(w,d,z) in unfolded.items() if q != 212}
    expected[85,1] = (1,-1,190)
    need(expected == folded, 'fold has additional table edits')
    blocks = [local_block(folded, m, r) for m in (0,1) for r in (0,1)]
    need([b['step_count'] for b in blocks] == [1,3,1,5], 'wrong local block lengths')
    def states(T): return {q for q,r in T}
    need(len(states(original)) == len(states(unfolded)) == 219, 'wrong old count')
    need(len(states(folded)) == 218, 'wrong new count')
    receipt = {
        'status':'PASS',
        'scope':'Closed-source reassociation and exact whole-tape local fold obligations; global unbounded simulation follows by the stated induction.',
        'input_sha256': {k:sha(getattr(a,k)) for k in ('parent_sites','old_sites','new_sites','old_table','unfolded_table','new_table')},
        'source': {'occurrences':occurrences,'factor_leaf_counts':[26,19,7],
                   'factor_boundaries':[boundary(x) for x in (A,B,C)],
                   'same_primitive_word':True,'same_continuation_graph':True,
                   'same_word_and_continuation_graph_as_pinned_K219':True,
                   'primitive_cfg_vertices':len(g1),
                   'primitive_cfg_edges':sum(len(y) for _,y in g1),
                   'metrics':metrics(new)},
        'unfolded_changes': [{'state':188,'read':r,'before':original[188,r],
                              'after':unfolded[188,r]} for r in (0,1)],
        'fold': {'removed_state':212,'retained_state':85,
                 'unique_incoming_edges': {str(q):incoming[q] for q in (85,212)},
                 'local_blocks':blocks,'native_state_count':218,
                 'admissible_start_state':0,
                 'global_simulation_initial_tape':'arbitrary two-sided binary tape'}
    }
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'PASS','source_occurrences':len(occurrences),
          'source_cfg_vertices':len(g1),'native_state_count':218,
          'local_block_lengths':[b['step_count'] for b in blocks],
          'out':str(a.out)}))

if __name__ == '__main__':
    main()
