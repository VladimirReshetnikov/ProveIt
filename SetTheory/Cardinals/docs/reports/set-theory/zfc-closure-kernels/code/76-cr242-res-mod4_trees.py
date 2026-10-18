#!/usr/bin/env python3
"""Enumerate register-path tree realizations of a destructive residue-1 test.

The tested syntax template has four distinct H-decrement leaves, one halt,
one continue, and optionally one break. This is a finite template search, not
a lower bound for arbitrary source programs or Turing machines.
"""
from functools import lru_cache
from itertools import permutations
from pathlib import Path
import json

@lru_cache(None)
def trees(n):
    if n == 1:
        return (None,)
    return tuple((l, r) for k in range(1, n) for l in trees(k) for r in trees(n-k))

def leaves(t,p=''):
    if t is None:
        return (p,)
    return leaves(t[0],p+'0')+leaves(t[1],p+'1')

def inc(p):
    return format((int(p,2)+1)%(1<<len(p)), f'0{len(p)}b') if p else ''

def jump(p,b,n):
    for i in range(len(p)-1,-1,-1):
        if p[i]==b:
            n-=1
            if n==0:
                s=p[:i]
                return inc(s) if b=='0' else s
    return ''

def control(paths,ops):
    # A stand-alone call is the left child of (TEST, RETURN).
    ps=['0'+p for p in paths]+['1']
    table={p:i for i,p in enumerate(ps)}
    def decode(p):
        for i in range(1,max(map(len,ps))+1):
            q=(p+'0'*i)[:i]
            if q in table:
                if '1' in p[i:]:
                    raise ValueError('discarded nonzero suffix')
                return table[q]
        raise ValueError('no leaf')
    out=[]
    for p,op in zip(ps,ops+['R']):
        if op in ('H','R'): out.append((op,)); continue
        if op=='D': out.append(('D',decode(inc(p)),decode(jump(p,'0',1))))
        elif op[0]=='C':
            if int(op[1:])>p.count('1'): raise ValueError('continue escapes caller')
            out.append(('C',decode(jump(p,'1',int(op[1:])))))
        else:
            if int(op[1:])>p.count('0'): raise ValueError('break escapes caller')
            out.append(('B',decode(jump(p,'0',int(op[1:])))))
    return out

def test(g,h):
    pc=0; fuel=12*(h+1); steps=0
    while steps<fuel:
        op=g[pc]
        if op[0] in ('H','R'):return op[0],h,steps
        if op[0]=='D':pc=op[1] if h else op[2];h=max(0,h-1)
        else:pc=op[1]
        steps+=1
    return 'L',h,steps

def expression(t,opiter):
    return next(opiter) if t is None else [expression(t[0],opiter),expression(t[1],opiter)]

def run(n):
    syntax=[];family=0;valid_paths=0
    # Continue/break counts need not exceed the maximal tree depth: larger
    # counts all remove the complete caller prefix and are not local calls.
    alphabet=['D']*4+['H','C']+(['B'] if n==7 else [])
    opsets=sorted(set(permutations(alphabet)))
    for t in trees(n):
        ps=leaves(t)
        for row in opsets:
            if row[0]!='D':continue
            for c in range(1,n):
                for b in (range(1,n) if n==7 else [1]):
                    ops=[x+str(c) if x=='C' else x+str(b) if x=='B' else x for x in row]
                    family+=1
                    try:g=control(ps,ops)
                    except ValueError:continue
                    valid_paths+=1
                    if all(test(g,h)[:2]==(('H' if h%4==1 else 'R'),0) for h in range(33)):
                        # Exact finite-control certificate: following positive
                        # edges visits exactly four D's and returns to entry;
                        # each zero edge has the required halt/return suffix.
                        pc=0;seen=set();sequence=[]
                        while pc not in seen:
                            seen.add(pc);sequence.append(pc)
                            if g[pc][0] in ('R','H'):break
                            pc=g[pc][1]
                        if pc!=0:continue
                        if sum(g[i][0]=='D' for i in sequence)!=4:continue
                        syntax.append(dict(paths=ps,ops=ops,graph=g,tree=expression(t,iter(ops)),cycle=sequence,
                                           clock=[test(g,h)[2] for h in range(4)]))
    return dict(leaves=n,tree_shapes=len(trees(n)),template_assignments_considered=family,
                valid_path_assignments=valid_paths,candidates=syntax)

if __name__=='__main__':
    result={str(n):run(n) for n in [6,7]}
    p=Path(__file__).with_name('mod4_trees.json');p.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({n:{k:v for k,v in d.items() if k!='candidates'}|{'candidate_count':len(d['candidates'])} for n,d in result.items()},indent=2))
