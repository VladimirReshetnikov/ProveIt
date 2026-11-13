#!/usr/bin/env python3
"""Rebuild a source-only copyH/cons simplification and audit its scope."""
from collections import defaultdict, deque
from functools import lru_cache
import argparse
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent
TREE = SOURCE / 'negation-mp197/source.tree.json'
TREE_SHA = '7d01a47445daf5ff804d32af8886364b3ee9e9f38efaa1e9d147d7989c28479e'
ENTRIES = [317, 396, 679, 1435, 1907]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def branches(row):
    return row[2:] if row[0] in ('inc', 'dec') else row[1:]


def normalize(graph, start, size):
    result = []
    for row in graph[start:start+size]:
        prefix = row[:2] if row[0] in ('inc', 'dec') else row[:1]
        result.append(prefix + tuple(x-start for x in branches(row)))
    return result


def execute(graph, pc, end, registers):
    regs = list(registers)
    for steps in range(1000000):
        if pc == end:
            return tuple(regs), steps
        row = graph[pc]
        if row[0] == 'inc':
            regs[row[1]] += 1
            pc = row[2]
        elif row[0] == 'dec':
            if regs[row[1]]:
                regs[row[1]] -= 1
                pc = row[3]
            else:
                pc = row[2]
        elif row[0] == 'jump':
            pc = row[1]
        else:
            raise ValueError(('unexpected instruction', pc, row))
    raise ValueError('finite control exceeded step limit')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--sites', type=Path)
    args = ap.parse_args()
    need(hashlib.sha256(TREE.read_bytes()).hexdigest() == TREE_SHA, 'combined tree changed')
    rot = load('rotations', SOURCE / 'scan_rotations.py')
    combined = load('combined', SOURCE / 'negation-mp197/replay.py')
    interval = load('interval', SOURCE / 'verify_zero_transfer.py')
    joint = load('joint', SOURCE / 'verify_joint_mask.py')
    original = combined.decode_tree(rot, json.loads(TREE.read_text()))

    @lru_cache(None)
    def rename(t, old, new):
        row = rot.store[t]
        if rot.isnode(t):
            return rot.node(rename(row[1], old, new), rename(row[2], old, new))
        return rot.interned((row[0], new if row[0] in ('inc', 'dec') and row[1] == old else row[1]))

    @lru_cache(None)
    def associate(xs):
        if len(xs) == 1:
            return (xs[0],)
        return tuple(rot.node(a,b) for i in range(1,len(xs))
                     for a in associate(xs[:i]) for b in associate(xs[i:]))

    # The five closed blocks originally use copyH = node58 and cons = node65.
    old = rot.node(rot.env['node58'], rot.env['node65'])
    drain_t_to_r = rename(rot.env['node37'], 6, 7)
    components = (rot.env['node42'], drain_t_to_r, rot.env['node57'],
                  rot.env['node10'], rot.env['node64'])
    candidates = associate(components)
    need(len(candidates) == 14, 'association census changed')
    direct = min(candidates, key=lambda z: rot.metric(rot.rewrite(original, old, z)))
    transformed = rot.rewrite(original, old, direct)
    need(rot.bound(old) == (0,0) and rot.bound(direct) == (0,0), 'block closure changed')
    oldgraph, newgraph = rot.graph(original), rot.graph(transformed)
    need(oldgraph == interval.interval_graph(rot, original)[0] and
         newgraph == interval.interval_graph(rot, transformed)[0], 'graph resolvers disagree')
    need((len(oldgraph), len(newgraph), rot.metric(original), rot.metric(transformed)) ==
         (3573, 3468, 159, 164), 'source census changed')
    leaves = list(rot.leaf_occurrences(original))
    starts = sorted(next(i for i,(p,_) in enumerate(leaves) if p[:len(path)] == path)
                    for path, node in rot.node_occurrences(original) if node == old)
    need(starts == ENTRIES, 'block occurrences changed')
    old_intervals = [(s,s+53) for s in starts]
    new_starts = [s-21*i for i,s in enumerate(starts)]
    old_template = normalize(oldgraph, starts[0], 53)
    new_template = normalize(newgraph, new_starts[0], 32)
    for start, new_start in zip(starts, new_starts):
        need(normalize(oldgraph,start,53) == old_template and
             normalize(newgraph,new_start,32) == new_template, 'block CFG changed')
        for graph, lo, size in ((oldgraph,start,53),(newgraph,new_start,32)):
            for i,row in enumerate(graph):
                for dest in branches(row):
                    if lo <= i < lo+size:
                        need(lo <= dest <= lo+size, 'block has another exit')
                    else:
                        need(not lo < dest < lo+size, 'external edge enters block interior')
    def relocate(pc):
        need(not any(lo < pc < hi for lo,hi in old_intervals), 'edge enters old block interior')
        return pc - 21*sum(hi <= pc for lo,hi in old_intervals)
    outside = 0
    for pc,row in enumerate(oldgraph):
        if any(lo <= pc < hi for lo,hi in old_intervals):
            continue
        prefix = row[:2] if row[0] in ('inc','dec') else row[:1]
        need(newgraph[relocate(pc)] == prefix + tuple(relocate(x) for x in branches(row)),
             'outside CFG relocation changed')
        outside += 1
    need(outside == 3308, 'outside CFG census changed')

    seed = (25,1)
    seen, queue, masks = {seed}, deque([seed]), defaultdict(set)
    while queue:
        pc,mask = queue.popleft()
        masks[pc].add(mask)
        for state in joint.successors(oldgraph[pc],mask):
            if state not in seen:
                seen.add(state)
                queue.append(state)
    need(all(all(z in seen for z in joint.successors(oldgraph[pc],mask))
             for pc,mask in seen), 'mask set not closed')
    need(len(seen) == 258660, 'mask closure census changed')
    for pc in starts:
        need(masks[pc] and all(mask & (1 << 7) == 0 for mask in masks[pc]),
             'register 7 is not forced zero')

    tests = 0
    for start,new_start in zip(starts,new_starts):
        for t,w,h,s in product(range(4), repeat=4):
            regs = [7,t,w,3,5,h,s,0,9]
            a,_ = execute(oldgraph,start,start+53,regs)
            b,_ = execute(newgraph,new_start,new_start+32,regs)
            u = t+s+h
            expected = [7, 4*(u*(u+1)//2+h), w, 3, 5, h, 0, 0, 9]
            need(a == b == tuple(expected), 'closed-form check failed')
            tests += 1
    bad = [7,0,0,3,3,0,0,2,9]
    a,na = execute(oldgraph,starts[0],starts[0]+53,bad)
    b,nb = execute(newgraph,new_starts[0],new_starts[0]+32,bad)
    need(a != b, 'nonzero scratch negative control changed')
    new_leaves = list(rot.leaf_occurrences(transformed))
    ops = {'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    sites = [[''.join(map(str,p)),ops[rot.store[t][0]],
              None if rot.store[t][0]=='halt' else rot.store[t][1]] for p,t in new_leaves]
    site_text = json.dumps(sites)+'\n'
    if args.sites:
        args.sites.write_text(site_text)
    out = {'input_tree_sha256':TREE_SHA,'sites_sha256':hashlib.sha256(site_text.encode()).hexdigest(),
           'old_sites':3573,'new_sites':3468,'old_internal_nodes':159,'new_internal_nodes':164,
           'old_entries':starts,'new_entries':new_starts,'old_block_sites':53,'new_block_sites':32,
           'other_cfg_rows_checked':outside,'both_graph_resolvers_agree':True,
           'joint_mask_states':len(seen),'entry_mask_counts':[len(masks[pc]) for pc in starts],
           'scratch_zero_proved_at_all_entries':True,'finite_zero_scratch_controls':tests,
           'nonzero_scratch_counterexample':{'input':bad,'old':a,'new':b,
                                              'old_steps':na,'new_steps':nb},
           'scope':'Source-level mathematical rewrite only; no physical table or PA theorem.'}
    text = json.dumps(out,indent=2,sort_keys=True)+'\n'
    print(text,end='')
    if args.output:
        args.output.write_text(text)


if __name__ == '__main__':
    main()
