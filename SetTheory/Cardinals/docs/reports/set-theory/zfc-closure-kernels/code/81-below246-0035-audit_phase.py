#!/usr/bin/env python3
"""Independent fixed-point audit of known-zero source loops.

The literal program is Mira-Cult's, verified by Jeff Ketchersid. The
zero/one/many domain was used by the ProveIt phase-analysis experiment.
This audit independently applies that domain to the actual 246 initial
register vector and to strictly larger start families, and checks every
postfix obligation after convergence. It does not emit a binary TM.
"""
from pathlib import Path
from collections import deque
import json
import hashlib
import re

ROOT = Path(__file__).resolve().parents[1]
PROGRAM = ROOT / 'sources/context246/zfc-context246/sources/Prog254.v'
EXPECTED = '1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'

def next_pc(path, op, n, positive=False):
    p=list(path)
    def strip(bit, count):
        while count and p:
            count -= p.pop() == bit
    if op == 'CD' and not positive:
        strip('0', 1)
    elif op == 'CB':
        strip('0', n)
    elif op == 'CC':
        strip('1', n)
        return ''.join(p)
    elif op == 'CH':
        return None
    carry=True
    for i in range(len(p)-1,-1,-1):
        if not carry: break
        if p[i]=='1': p[i]='0'
        else: p[i]='1'; carry=False
    return ''.join(p)

def read_program(raw):
    s=raw.decode().split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    token=r'(?:CN|CI|CD|CB|CC) \d+|CH'
    matches=list(re.finditer(r'\(('+token+r'),\s*('+token+r')\)',s))
    residual=re.sub(r'\(('+token+r'),\s*('+token+r')\)', '', s)
    assert re.sub(r'[;\s]', '', residual)==''
    nodes=[tuple(tuple(x.split()) for x in m.groups()) for m in matches]
    leaves=[]; seen=set()
    def visit(node,path):
        assert node not in seen
        seen.add(node)
        for bit,e in enumerate(nodes[node]):
            op=e[0]; n=int(e[1]) if len(e)>1 else None
            if op=='CN': visit(n,path+str(bit))
            else: leaves.append((path+str(bit),op,n,node,bit))
    visit(0,'')
    assert len(nodes)==len(seen)==6459 and len(leaves)==6460
    lookup={l[0]:i for i,l in enumerate(leaves)}
    def decode(pc):
        node=0; depth=0; p=''
        while True:
            b=pc[depth] if depth<len(pc) else '0'
            p+=b; depth+=1
            e=nodes[node][int(b)]
            if e[0]=='CN': node=int(e[1])
            else:
                assert all(b=='0' for b in pc[depth:])
                return lookup[p]
    cases=[]; by_leaf=[[] for _ in leaves]
    for i,(p,op,n,node,bit) in enumerate(leaves):
        for positive in ([False,True] if op=='CD' else [None]):
            q=next_pc(p,op,n,positive)
            j=None if q is None else decode(q)
            by_leaf[i].append(len(cases))
            cases.append((i,positive,j))
    assert len(cases)==8391
    return leaves,cases,by_leaf,decode('')

def transfer(mask,leaf,positive):
    if mask is None: return None
    p,op,r,_,_=leaf; out=list(mask)
    if op=='CI': out[r]=(2 if mask[r]&1 else 0)|(4 if mask[r]&6 else 0)
    elif op=='CD':
        old=mask[r]&(6 if positive else 1)
        if not old: return None
        out[r]=((1 if old&2 else 0)|(6 if old&4 else 0)) if positive else 1
    return tuple(out)

def analyze(leaves,cases,by_leaf,first,initial):
    masks=[None]*len(leaves); masks[first]=tuple(initial)
    todo=deque([first]); pops=0
    while todo:
        i=todo.popleft(); pops+=1
        for c in by_leaf[i]:
            _,positive,j=cases[c]
            out=transfer(masks[i],leaves[i],positive)
            if j is None or out is None: continue
            joined=out if masks[j] is None else tuple(a|b for a,b in zip(masks[j],out))
            if joined != masks[j]: masks[j]=joined; todo.append(j)
    assert all(a & ~b == 0 for a,b in zip(initial,masks[first]))
    impossible=[]; enabled=0
    for c,(i,positive,j) in enumerate(cases):
        out=transfer(masks[i],leaves[i],positive)
        if out is None: impossible.append(c)
        else:
            enabled+=1
            if j is not None:
                assert masks[j] is not None
                assert all(a & ~b == 0 for a,b in zip(out,masks[j]))
    loops=[]
    for c in [8201,8202,8203,8204,8357,8358,8359,8360]:
        i,pos,j=cases[c]; p,op,r,node,edge=leaves[i]
        loops.append({'case':c,'path':p,'op':op,'register':r,'positive':pos,
                      'node':node,'edge':edge,'mask':masks[i],
                      'successor_path':None if j is None else leaves[j][0],
                      'successor_op':None if j is None else leaves[j][1],
                      'successor_register':None if j is None else leaves[j][2]})
    classes=sorted(set(m for m in masks if m is not None))
    class_index={m:i for i,m in enumerate(classes)}
    return {'initial_masks':initial,'worklist_pops':pops,'possible_guards':enabled,
            'impossible_cases':impossible,'possible_leaves':sum(x is not None for x in masks),
            'loop_cases':loops,'all_postfix_obligations_checked':True,
            'mask_classes':classes,'site_mask_class_ids':[None if m is None else class_index[m] for m in masks]}

def main():
    raw=PROGRAM.read_bytes(); assert hashlib.sha256(raw).hexdigest()==EXPECTED
    data=read_program(raw)
    starts={
        'zero_root':[1]*9,
        'actual_246':[4,1,1,1,4,1,1,1,1],
        'six_arbitrary_numeric_fields':[7,1,1,7,7,1,7,7,7],
        'all_nine_arbitrary':[7]*9,
    }
    result={'program_sha256':EXPECTED,'domain':{'1':'zero','2':'one','4':'at least two'},
            'runs':{k:analyze(*data,v) for k,v in starts.items()}}
    (Path(__file__).parent/'phase_generalized_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:{f:r[f] for f in ['worklist_pops','possible_guards','impossible_cases','possible_leaves']} for k,r in result['runs'].items()},indent=2))

if __name__=='__main__': main()
