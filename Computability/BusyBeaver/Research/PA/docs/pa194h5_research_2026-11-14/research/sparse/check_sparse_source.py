#!/usr/bin/env python3
"""Exact graph edit for inserting the extra fresh-counter increment.

Point --construction to the extracted primary PA194 construction directory.
This is an algebraic/source check only; it does not validate a physical TM.
"""
import argparse
import importlib
import json
import sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--construction', type=Path, default=Path(__file__).parent/'base194')
    args = ap.parse_args()
    sys.path.insert(0, str(args.construction.resolve()))
    c = importlib.import_module('compiler')
    grammar = c.read_grammar(args.construction/'source/pa194.grammar.json')
    old_nodes = c.raw_nodes
    old_sites, old_ins, old_contracts = c.source(grammar)
    def sparse_nodes():
        nodes = old_nodes()
        assert nodes['node27'] == ('node25', 'node26')
        nodes['node27'] = ('node25', (('leaf', 'inc', 0), 'node26'))
        return nodes
    c.raw_nodes = sparse_nodes
    new_sites, new_ins, new_contracts = c.source(grammar)
    assert len(new_ins) == len(old_ins) + 1
    k = 31
    ren = lambda i: i + (i >= k)
    def expected(i, op):
        if op[0] == 'inc':
            return ('inc', op[1], ren(op[2]))
        if op[0] == 'dec':
            return ('dec', op[1], k if i == 27 else ren(op[2]), ren(op[3]))
        if op[0] == 'jump':
            return ('jump', ren(op[1]))
        return op
    for i, ins in enumerate(old_ins):
        assert new_ins[ren(i)] == expected(i, ins), (i, ins, new_ins[ren(i)])
    assert new_ins[k] == ('inc', 0, k+1)
    def run_fetch(n, l, x=0):
        pc, v, steps = 25, [n,0,0,0,0,0,x,0,l], 0
        while pc != 35:
            op, *p = new_ins[pc]
            if op == 'inc':
                r, pc = p; v[r] += 1
            elif op == 'dec':
                r, zero, positive = p
                pc = positive if v[r] else zero
                v[r] = max(0,v[r]-1)
            elif op == 'jump':
                pc = p[0]
            else:
                raise AssertionError(op)
            steps += 1
            assert steps <= 100000
        return steps,v
    for n in range(100):
        steps,v=run_fetch(n,0)
        assert steps==7*n+5 and v==[n+2,0,0,0,0,0,0,0,n]
        for l in (1,2,7):
            steps,v=run_fetch(n,l)
            assert steps==2 and v==[n,0,0,0,0,0,0,0,l-1]
    # The concrete H/X-permuted physical startup is checked separately.
    # Here its returned source seed is joined to the clean N=4 boundary.
    v, pc, seed_trace = [4,0,0,0,0,0,0,0,1], 40, []
    for step in range(49):
        seed_trace.append([pc, v.copy()])
        if step == 48:
            assert pc == 25 and v == [4,0,0,0,0,0,0,0,0]
            break
        op, *parameters = new_ins[pc]
        if op == 'inc':
            r, pc = parameters; v[r] += 1
        elif op == 'dec':
            r, zero, positive = parameters
            pc = positive if v[r] else zero
            v[r] = max(0, v[r]-1)
        elif op == 'jump':
            pc = parameters[0]
        else:
            raise AssertionError('The startup source prefix must not halt')
    trace_path = Path(__file__).parent/'safe_sparse_seed_to_clean.json'
    if trace_path.exists():
        assert json.loads(trace_path.read_text()) == seed_trace
    print(json.dumps({'old_source_instructions':len(old_ins),
        'new_source_instructions':len(new_ins), 'old_branch_contracts':len(old_contracts),
        'new_branch_contracts':len(new_contracts), 'inserted_source_ordinal':k,
        'only_old_edge_changed':{'source':27,'branch':'zero','new_target':31},
        'max_new_path_length':max(map(lambda x:len(x[0]),new_sites)),
        'fresh_fetch_duration':'7*N+5', 'fresh_fetch_effect':'(N,0,0)->(N+2,N,0)',
        'continuation_duration':2,'startup_seed_to_clean_source_steps':48,
        'clean_initial_counter':4,'result':'PASS'},indent=2))

if __name__=='__main__':main()
