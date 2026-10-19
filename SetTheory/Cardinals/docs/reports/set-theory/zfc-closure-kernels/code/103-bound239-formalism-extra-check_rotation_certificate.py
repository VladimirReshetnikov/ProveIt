#!/usr/bin/env python3
"""Independently check the exact 13-stage source-control certificate.

Python 3 standard library only. No repository imports, solvers, sampling, or
execution fuel. The finite graph is a complete abstraction of the source's
register control: both zero/nonzero decrement outcomes are checked separately.
It is not a certificate for any binary Turing-machine implementation.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import json


def is_leaf(t):
    return isinstance(t[0], str)


def tree_of_sites(ss):
    leaves = {}
    for item in ss:
        if not isinstance(item, list) or len(item) != 3:
            raise ValueError('site must be [binary_path, operation, operand]')
        p, o, r = item
        if not isinstance(p, str) or not p or set(p) - {'0', '1'}:
            raise ValueError('nonempty binary site path required')
        if o not in ('CI', 'CD', 'CB', 'CC', 'CH'):
            raise ValueError('unknown operation')
        if o != 'CH' and (type(r) is not int or r < 0):
            raise ValueError('natural operand required')
        if o in ('CI', 'CD') and r >= 9:
            raise ValueError('register must lie in 0..8 for this artifact')
        if o == 'CH' and r is not None:
            raise ValueError('halt operand must be null')
        if p in leaves:
            raise ValueError('duplicate site')
        leaves[p] = (o, r)
    if not leaves:
        raise ValueError('empty program')
    prefixes = {p[:i] for p in leaves for i in range(len(p))}
    if prefixes & leaves.keys():
        raise ValueError('site paths are not prefix-free')
    def build(p):
        if p in leaves:
            return leaves[p]
        if p not in prefixes:
            raise ValueError('source tree is not full binary at '+p)
        return build(p+'0'), build(p+'1')
    return build('')


def sites_of_tree(t, p=''):
    if is_leaf(t):
        return [(p, t[0], t[1])]
    return sites_of_tree(t[0], p+'0') + sites_of_tree(t[1], p+'1')


def increment_path(p):
    """Fixed-length binary increment, including all-ones rollover."""
    if '0' not in p:
        return '0'*len(p)
    i = p.rindex('0')
    return p[:i]+'1'+'0'*(len(p)-i-1)


def strip_path(bit, count, p):
    """Delete suffix through the count-th occurrence; exhaustion yields ''."""
    while count and p:
        last, p = p[-1], p[:-1]
        if last == bit:
            count -= 1
    return p


def break_path(k, p):
    return increment_path(strip_path('0', k, p))


def continue_path(k, p):
    return strip_path('1', k, p)


def graph(t):
    ss = sites_of_tree(t)
    ids = {p: i for i, (p, _, _) in enumerate(ss)}
    def locate(pc):
        """Walk with infinite zero padding, truncating at the encountered leaf."""
        n, p = t, ''
        while not is_leaf(n):
            b = pc[len(p)] if len(p) < len(pc) else '0'
            n, p = n[int(b)], p+b
        if '1' in pc[len(p):]:
            raise ValueError('nonzero unused successor-path suffix after leaf '+p)
        return ids[p]
    if locate('') != 0:
        raise ValueError('initial empty path does not map to leaf zero')
    out = []
    for p, o, r in ss:
        if o == 'CI':
            out.append(('CI', r, locate(increment_path(p))))
        elif o == 'CD':
            out.append(('CD', r, locate(increment_path(p)), locate(break_path(1,p))))
        elif o == 'CB':
            out.append(('J', locate(break_path(r,p))))
        elif o == 'CC':
            out.append(('J', locate(continue_path(r,p))))
        else:
            out.append(('H',))
    return out


def rotate_stage(t, step):
    direction = step['direction']
    if direction not in ('left', 'right'):
        raise ValueError('rotation direction')
    paths = step['paths']
    if len(paths) != len(set(paths)):
        raise ValueError('repeated rotation path')
    if any(set(p)-{'0','1'} for p in paths):
        raise ValueError('nonbinary rotation path')
    prefixes = {p[:i] for p in paths for i in range(len(p))}
    if prefixes & set(paths):
        raise ValueError('simultaneous rotation paths overlap')
    targets, reached = set(paths), set()
    def visit(n, p):
        if p in targets:
            if is_leaf(n):
                raise ValueError('rotation at a leaf')
            reached.add(p)
            a, b = n
            if direction == 'left':
                if is_leaf(b):
                    raise ValueError('left rotation needs (a,(b,c))')
                ba, bb = b
                return (a,ba),bb
            if is_leaf(a):
                raise ValueError('right rotation needs ((a,b),c)')
            aa, ab = a
            return aa,(ab,b)
        if is_leaf(n) or p not in prefixes:
            return n
        return visit(n[0],p+'0'),visit(n[1],p+'1')
    out = visit(t,'')
    if reached != targets:
        raise ValueError('unreached rotation paths')
    return out


def statistics(t):
    intern = {}
    def visit(n):
        key = n if is_leaf(n) else (visit(n[0]), visit(n[1]))
        if key not in intern:
            intern[key] = len(intern)
        return intern[key]
    visit(t)
    ss = sites_of_tree(t)
    leaf_kinds = sum(isinstance(x[0],str) for x in intern)
    return dict(leaves=len(ss), leaf_kinds=leaf_kinds,
                dag_nodes=len(intern), internal_source_nodes=len(intern)-leaf_kinds,
                max_path=len(max((p for p,_,_ in ss),key=len)),
                max_zero_run=max(len(z) for p,_,_ in ss for z in p.split('1')),
                operations=dict(sorted(Counter(o for _,o,_ in ss).items())))


def check(baseline, certificate, candidate):
    raw = baseline.read_bytes()
    cert = json.loads(certificate.read_text())
    if cert['format'] != 'busy-beaver-source-rotation-certificate-v1':
        raise ValueError('certificate format')
    if sha256(raw).hexdigest() != cert['baseline_sha256']:
        raise ValueError('baseline bytes do not match the pinned certificate')
    t = tree_of_sites(json.loads(raw))
    original = t
    reference_graph = graph(t)
    reference_word = [x[1:] for x in sites_of_tree(t)]
    rows = []
    for number, step in enumerate(cert['steps'], 1):
        if step['number'] != number:
            raise ValueError('certificate stage numbers')
        t = rotate_stage(t, step)
        if [x[1:] for x in sites_of_tree(t)] != reference_word:
            raise ValueError('ordered operation word changed')
        gg = graph(t)
        if gg != reference_graph:
            i = next(i for i,(a,b) in enumerate(zip(gg,reference_graph)) if a!=b)
            raise ValueError(f'control edge mismatch at stage {number}, leaf {i}: {gg[i]} != {reference_graph[i]}')
        rows.append(dict(stage=number, simultaneous_rotations=len(step['paths']),
                         direction=step['direction'], **statistics(t)))
    expected = tree_of_sites(json.loads(candidate.read_text()))
    if sites_of_tree(t) != sites_of_tree(expected):
        raise ValueError('replayed source differs from candidate')
    final = statistics(t)
    if final['dag_nodes'] != 224 or final['max_zero_run'] != 6:
        raise ValueError('unexpected final source metrics')
    edge_count = sum(2 if e[0]=='CD' else 0 if e[0]=='H' else 1 for e in reference_graph)
    return dict(status='PASS_EXACT_SOURCE_CONTROL_CERTIFICATE',
                baseline_sha256=sha256(raw).hexdigest(),
                candidate_sites_sha256=sha256(candidate.read_bytes()).hexdigest(),
                certificate_sha256=sha256(certificate.read_bytes()).hexdigest(),
                normalized_control_graph_sha256=sha256(json.dumps(reference_graph,separators=(',',':')).encode()).hexdigest(),
                stages=len(rows), local_rotations=sum(r['simultaneous_rotations'] for r in rows),
                guards_or_edges_checked_per_stage=edge_count,
                halt_descriptors_checked_per_stage=sum(e[0]=='H' for e in reference_graph),
                canonical_successor_paths=True,
                initial=statistics(original), final=final, stage_results=rows,
                scope='Exact source-level bisimulation for every natural register vector; no binary TM correspondence asserted.')


if __name__ == '__main__':
    here = Path(__file__).resolve().parent
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,default=here/'baseline_sites.json')
    ap.add_argument('--certificate',type=Path,default=here/'rotation_certificate.json')
    ap.add_argument('--candidate',type=Path,default=here/'boundary224_sites.json')
    ap.add_argument('--report',type=Path)
    args = ap.parse_args()
    result = check(args.baseline,args.certificate,args.candidate)
    rendered = json.dumps(result,indent=2)+'\n'
    if args.report:
        args.report.write_text(rendered)
    print(rendered,end='')
