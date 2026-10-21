#!/usr/bin/env python3
"""Independently check a finite zero-support certificate and guarded rewrite.

This checker does not compute a least fixed point and does not use the interval
CFG resolver used by the certificate producer.  It checks every local closure
obligation against the arithmetic address resolver.  The mathematical induction
from these finite obligations to all natural register values is in the receipt.
"""
import argparse, hashlib, json
from pathlib import Path

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def require(b, s):
    if not b: raise ValueError(s)

def graph(rows):
    leaves = {p:i for i,(p,op,r) in enumerate(rows)}
    require(len(leaves)==len(rows), 'distinct addresses')
    depth = max(map(len, leaves))
    def locate(prefix):
        w=prefix+'0'*depth
        for k in range(1,depth+1):
            if w[:k] in leaves:
                require('1' not in prefix[k:], 'no stray suffix')
                return leaves[w[:k]]
        raise ValueError('no successor')
    def inc(p):
        return format((int(p,2)+1)%(1<<len(p)), '0'+str(len(p))+'b') if p else ''
    def cut(p,bit,n):
        hits=[i for i,c in enumerate(p) if c==bit]
        return p[:hits[-n]] if len(hits)>=n else ''
    answer=[]
    for p,op,r in rows:
        require(p and set(p)<={'0','1'}, 'binary address')
        require(op in ('CI','CD','CB','CC','CH'), 'opcode')
        if op in ('CI','CD'): require(type(r)==int and 0<=r<9, 'register')
        if op in ('CB','CC'): require(type(r)==int and r>=1, 'control depth')
        if op=='CI': e=[locate(inc(p))]
        elif op=='CD': e=[locate(inc(cut(p,'0',1))),locate(inc(p))]
        elif op=='CB': e=[locate(inc(cut(p,'0',r)))]
        elif op=='CC': e=[locate(cut(p,'1',r))]
        else: e=[]
        answer.append(e)
    require(locate('')==0,'entry ordinal')
    return answer

def successors(row,edges,mask):
    _,op,r=row
    if op=='CI': return [(edges[0],mask|(1<<r))]
    if op=='CD':
        if mask&(1<<r): return [(edges[1],mask),(edges[1],mask&~(1<<r))]
        return [(edges[0],mask)]
    if op=='CH': return []
    return [(edges[0],mask)]

def main():
    p=argparse.ArgumentParser();p.add_argument('--baseline',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--invariant',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    old=json.loads(a.baseline.read_text());new=json.loads(a.candidate.read_text());raw=json.loads(a.invariant.read_text());oldg=graph(old);newg=graph(new)
    require(len(old)==len(new)==len(raw),'same ordinal count')
    sets=[]
    for i,xs in enumerate(raw):
        require(type(xs)==list and len(xs)==len(set(xs)),f'invariant list {i}')
        require(all(type(m)==int and 0<=m<512 for m in xs),f'mask range {i}')
        sets.append(set(xs))
    require(17 in sets[0], 'all seeds with support {0,4} admitted')
    checks=0
    for i,(row,edges,masks) in enumerate(zip(old,oldg,sets)):
        for m in masks:
            for j,n in successors(row,edges,m):
                require(n in sets[j],f'closure ({i},{m})->({j},{n})')
                checks+=1
    changed=[]
    for i,(r,s) in enumerate(zip(old,new)):
        require(r[0]==s[0], 'identical tree addresses')
        if r==s: require(oldg[i]==newg[i],f'unchanged CFG {i}');continue
        require(r[1:]==['CB',1] and s[1]=='CD', f'allowed guarded rewrite {i}')
        k=s[2]
        require(sets[i] and all((m&(1<<k))==0 for m in sets[i]),f'zero guard {i}')
        require(newg[i][0]==oldg[i][0],f'zero edge equality {i}')
        changed.append({'ordinal':i,'register':k,'admitted_masks':len(sets[i]),'successor':oldg[i][0]})
    for i,(row,edges,masks) in enumerate(zip(new,newg,sets)):
        for m in masks:
            for j,n in successors(row,edges,m): require(n in sets[j],f'candidate closure ({i},{m})->({j},{n})')
    report={'status':'PASS','baseline_sha256':digest(a.baseline),'candidate_sha256':digest(a.candidate),'invariant_sha256':digest(a.invariant),'ordinal_count':len(old),'abstract_configurations':sum(map(len,sets)),'baseline_local_closure_edges':checks,'initial_support_mask':17,'unreachable_ordinals':[i for i,s in enumerate(sets) if not s],'replacements':changed,'scope':'Finite certificate proves full source-step equivalence for every natural register seed whose nonzero registers are exactly 0 and 4. It does not assert equivalence for arbitrary support patterns. Each concrete increment/decrement is covered by the checked support transfer; induction gives the invariant, then simultaneous guarded rewrites preserve every concrete register vector and source ordinal, including halting.'}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
