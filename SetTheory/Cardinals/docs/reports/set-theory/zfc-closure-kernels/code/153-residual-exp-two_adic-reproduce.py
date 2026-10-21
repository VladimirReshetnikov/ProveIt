#!/usr/bin/env python3
"""Reproduce the offset two-adic codec experiment using only this packet.

This is a source-cost and helper-contract experiment, not a calibrated
machine.  The pair-only and reader-only modes deliberately mix codecs and
are measurements only.  The matched mode still needs caller invariants
and a full-program proof before it can be compiled as a consistency search.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INPUT_SHA256 = '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
D = lambda i: ('CD', i)
I = lambda i: ('CI', i)
C = lambda i: ('CC', i)
B = lambda i: ('CB', i)
TRANSFER = lambda a,b: (D(a), (I(b), C(2)))
DOUBLE = lambda a,b: (D(a), ((I(b), I(b)), C(2)))

# The exact ten-leaf additive Cantor pairer in the pinned K219 source.
OLD_PAIR = ((D(1), (I(7), (I(6), C(3)))),
            (D(6), ((I(7), TRANSFER(6,1)), C(3))))

def old_reader(src):
    return ((D(src), (I(7), (((D(6), B(1)), TRANSFER(7,6)), C(3)))),
            TRANSFER(7,src))

# For clean destination r7=0, output 2^r6 (2 r1 + 1) - 1 in r7.
NEW_PAIR = ((DOUBLE(1,7), I(7)),
            ((D(6), ((DOUBLE(7,1), TRANSFER(1,7)), C(2))), D(7)))

def new_reader(src):
    odd = ((D(src), B(1)), B(2))
    half = (D(src), (odd, (I(7), C(3))))
    outer = (half, (I(6), (TRANSFER(7,src), C(3))))
    return ((I(src), outer), TRANSFER(7,src))

def leaf(node):
    return isinstance(node[0], str)

def parse_source(rows):
    leaves = {p:(op,k) for p,op,k in rows}
    assert len(leaves) == len(rows)
    prefixes = {p[:i] for p in leaves for i in range(len(p)+1)}
    def walk(p):
        if p in leaves:
            assert p+'0' not in prefixes and p+'1' not in prefixes
            return leaves[p]
        assert p+'0' in prefixes and p+'1' in prefixes
        return walk(p+'0'), walk(p+'1')
    return walk('')

def sites(tree):
    rows = []
    def walk(node,p):
        if leaf(node):
            rows.append([p,node[0],node[1]])
        else:
            walk(node[0],p+'0')
            walk(node[1],p+'1')
    walk(tree,'')
    return rows

def metrics(tree):
    seen = set()
    def walk(node):
        if node in seen:
            return
        seen.add(node)
        if not leaf(node):
            walk(node[0])
            walk(node[1])
    walk(tree)
    rows = sites(tree)
    return dict(dag_nodes=len(seen),leaf_occurrences=len(rows),
                maximum_depth=max(len(p) for p,_,_ in rows),
                maximum_zero_run=max(len(x) for p,_,_ in rows for x in p.split('1')))

def source_bytes(tree):
    return (json.dumps(sites(tree),separators=(',',':'))+'\n').encode()

def evaluate(tree, initial):
    """Direct open-tree semantics, independent of the compiler CFG."""
    regs = list(initial)
    visits = 0
    def walk(node):
        nonlocal visits
        visits += 1
        if visits > 2000000:
            raise RuntimeError('finite diagnostic step cap')
        if leaf(node):
            op,k = node
            if op == 'CI':
                regs[k] += 1
                return 'N',0
            if op == 'CD':
                if regs[k] == 0:
                    return 'B',1
                regs[k] -= 1
                return 'N',0
            if op == 'CB':
                return 'B',k
            if op == 'CC':
                return 'C',k
            raise ValueError(node)
        while True:
            kind,depth = walk(node[0])
            if kind == 'B':
                return ('N',0) if depth == 1 else ('B',depth-1)
            if kind != 'N':
                return kind,depth
            kind,depth = walk(node[1])
            if kind == 'C':
                if depth == 1:
                    continue
                return 'C',depth-1
            return kind,depth
    outcome = walk(tree)
    return outcome,regs,visits

def unpair_offset(n):
    a = 0
    q = n+1
    while q % 2 == 0:
        q //= 2
        a += 1
    return a,(q-1)//2

def helper_checks():
    checked = total = largest = 0
    for a in range(6):
        for b in range(7):
            initial = [19,b,11,17,23,29,a,0,31]
            expected = list(initial)
            expected[1] = expected[6] = 0
            expected[7] = 2**a*(2*b+1)-1
            outcome,actual,visits = evaluate(NEW_PAIR,initial)
            assert outcome == ('N',0) and actual == expected
            checked += 1
            total += visits
            largest = max(largest,visits)
    for src in (2,8):
        for n in range(301):
            initial = [19,23,29,31,37,41,0,0,47]
            initial[src] = n
            expected = list(initial)
            expected[6],expected[src] = unpair_offset(n)
            outcome,actual,visits = evaluate(new_reader(src),initial)
            assert outcome == ('N',0) and actual == expected
            checked += 1
            total += visits
            largest = max(largest,visits)
    assert checked == 644
    # The new helper is not additive in an uncleared destination.
    dirty = [0]*9
    dirty[6] = dirty[7] = 1
    outcome,actual,_ = evaluate(NEW_PAIR,dirty)
    assert outcome == ('N',0) and actual[7] == 3
    assert 2**1*(2*0+1)-1+1 == 2
    return dict(cases=checked,pair_cases=42,reader_cases=602,
                evaluator_node_visits=total,maximum_evaluator_node_visits=largest,
                dirty_destination_witness=dict(a=1,b=0,initial_r7=1,
                    actual_r7=3,required_for_additive_offset_pairer=2))

def transform(tree,pairing,reading):
    counts = dict(pair=0,unpair2=0,unpair8=0)
    def walk(node):
        if pairing and node == OLD_PAIR:
            counts['pair'] += 1
            return NEW_PAIR
        for src in (2,8):
            if reading and node == old_reader(src):
                counts['unpair'+str(src)] += 1
                return new_reader(src)
        if leaf(node):
            return node
        return walk(node[0]),walk(node[1])
    return walk(tree),counts

def reproduce(output_dir,source_path):
    if not __debug__:
        raise SystemExit('Run with assertions enabled; omit -O and -OO.')
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True,exist_ok=True)
    raw = Path(source_path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA256
    tree = parse_source(json.loads(raw))
    diagnostic = helper_checks()
    helpers = {'cantor_pair':metrics(OLD_PAIR),'two_adic_pair':metrics(NEW_PAIR),
               'cantor_reader':metrics(old_reader(2)),
               'two_adic_reader':metrics(new_reader(2))}
    assert [(helpers[k]['dag_nodes'],helpers[k]['leaf_occurrences'])
            for k in helpers] == [(16,10),(20,15),(19,11),(21,15)]
    expected = {(False,False):(206,4744,38), (True,False):(214,5614,40),
                (False,True):(217,5088,38), (True,True):(225,5958,40)}
    variants = []
    for pairing,reading in expected:
        variant,counts = transform(tree,pairing,reading)
        measured = metrics(variant)
        assert (measured['dag_nodes'],measured['leaf_occurrences'],measured['maximum_depth']) == expected[pairing,reading]
        assert measured['maximum_zero_run'] == 6
        assert counts == dict(pair=174 if pairing else 0,
                              unpair2=82 if reading else 0,
                              unpair8=4 if reading else 0)
        encoded = source_bytes(variant)
        filename = f'p{int(pairing)}u{int(reading)}.sites.json'
        (output_dir/filename).write_bytes(encoded)
        variants.append(dict(pairing=pairing,unpairing=reading,replacements=counts,
                             metrics=measured,source=filename,
                             sha256=hashlib.sha256(encoded).hexdigest()))
    for name,macro in (('pair',NEW_PAIR),('reader2',new_reader(2)),('reader8',new_reader(8))):
        (output_dir/(name+'.macro.json')).write_text(json.dumps(macro,separators=(',',':'))+'\n')
    result = dict(status='PASS_SOURCE_COST_AND_FINITE_HELPERS',input_sha256=INPUT_SHA256,
                  helper_diagnostic_cases=644,diagnostics=diagnostic,
                  helper_metrics=helpers,variants=variants,
                  codec='P2(a,b)=2^a(2b+1)-1',
                  scope='Exact source replacements and finite helper diagnostics. One-sided modes mix codecs. No full-program calibration, literal TM compilation, or state bound is supplied.')
    (output_dir/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,required=True)
    parser.add_argument('--baseline-source',type=Path,default=ROOT/'encoding/inputs/k219.sites.json')
    args = parser.parse_args()
    print(json.dumps(reproduce(args.output_dir,args.baseline_source),indent=2))
