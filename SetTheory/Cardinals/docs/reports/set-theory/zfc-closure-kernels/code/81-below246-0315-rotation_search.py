#!/usr/bin/env python3
"""Finite grammar-association experiment, with exact source-control checks.

Keeps every instruction occurrence and its register argument. A proposed
rotation is accepted only if all 8391 guarded successors agree, or if all
8385 root-feasible successors agree with the independently checked phase
invariant. Counts describe source pair subtrees, not binary TM states.
"""
from pathlib import Path
from bisect import bisect_right
import hashlib
import json
import time
import audit_phase as a
from erase_known_zero_loops import parse_nodes

OUT=Path(__file__).resolve().parent
entries=[]; intern={}

def mk(value):
    if value not in intern: intern[value]=len(entries);entries.append(value)
    return intern[value]

def load(raw):
    nodes=parse_nodes(raw)
    def edge(e):
        return rec(int(e[1])) if e[0]=='CN' else mk((e[0],int(e[1]) if len(e)>1 else None))
    def rec(i): return mk(('N',edge(nodes[i][0]),edge(nodes[i][1])))
    return rec(0)

def reachable(root):
    seen=set()
    def walk(i):
        if i in seen:return
        seen.add(i)
        v=entries[i]
        if v[0]=='N':walk(v[1]);walk(v[2])
    walk(root)
    return sorted(i for i in seen if entries[i][0]=='N')

def rotate(root,pivot,direction):
    v=entries[pivot]
    if direction=='left':
        rhs=entries[v[2]]
        if rhs[0]!='N':return None
        replacement=mk(('N',mk(('N',v[1],rhs[1])),rhs[2]))
    else:
        lhs=entries[v[1]]
        if lhs[0]!='N':return None
        replacement=mk(('N',lhs[1],mk(('N',lhs[2],v[2]))))
    memo={}
    def rec(i):
        if i==pivot:return replacement
        if i in memo:return memo[i]
        e=entries[i]
        memo[i]=mk(('N',rec(e[1]),rec(e[2]))) if e[0]=='N' else i
        return memo[i]
    return rec(root)

def flatten(root):
    leaves=[]
    def rec(i,p):
        v=entries[i]
        if v[0]=='N':rec(v[1],p+'0');rec(v[2],p+'1')
        else:leaves.append((p,*v))
    rec(root,'')
    return leaves

def successor(path,op,n,positive):
    p=path
    if op=='CH':return None
    if op in ('CC','CB') or op=='CD' and not positive:
        bit='1' if op=='CC' else '0'
        count=n if op in ('CC','CB') else 1
        while count and p:
            count-=p[-1]==bit;p=p[:-1]
        if op=='CC':return p
    i=p.rfind('0')
    return p[:i]+'1'+'0'*(len(p)-i-1) if i>=0 else '0'*len(p)

def check(root,base_leaves,cases,excluded):
    ls=flatten(root)
    assert [(op,n) for p,op,n in ls]==[(op,n) for p,op,n,_,_ in base_leaves]
    depth=max(len(p) for p,op,n in ls)
    starts=[int(p,2)<<(depth-len(p)) for p,_,_ in ls]
    assert starts==sorted(starts) and len(set(starts))==len(starts)
    cache={}
    def decode(pc):
        if pc is None:return None
        if pc in cache:return cache[pc]
        x=(int(pc,2) if pc else 0)<<(depth-len(pc))
        i=bisect_right(starts,x)-1
        if '1' in pc[len(ls[i][0]):]:i=-1
        cache[pc]=i;return i
    failures=[]
    for c,(i,positive,target) in enumerate(cases):
        p,op,n=ls[i]
        got=decode(successor(p,op,n,positive))
        if got!=target:
            failures.append(c)
            if c not in excluded:return None
    maximum_zero_run=max(max(map(len,p.split('1'))) for p,_,_ in ls)
    return {'unique_pairs':len(reachable(root)),'maximum_zero_run':maximum_zero_run,
            'maximum_depth':depth,'changed_unreachable_successors':failures,
            'exact_all_guards':not failures,'retained_leaf_count':len(ls)}

def dump_graph(root,path,metadata):
    ids=reachable(root)
    data={'metadata':metadata,'root':root,'entries':{str(i):entries[i] for i in ids}}
    used=set(ids)
    for i in ids:used.update(entries[i][1:])
    data['entries']={str(i):entries[i] for i in sorted(used)}
    path.write_text(json.dumps(data,separators=(',',':'))+'\n')

def main():
    began=time.monotonic();raw=a.PROGRAM.read_bytes()
    assert hashlib.sha256(raw).hexdigest()==a.EXPECTED
    ls,cases,by,first=a.read_program(raw)
    phase=a.analyze(ls,cases,by,first,[7]*9)
    excluded=set(phase['impossible_cases'])
    root=load(raw); base=check(root,ls,cases,excluded)
    assert base['unique_pairs']==203 and base['exact_all_guards']
    records=[];good=[];rejected=0
    for p in reachable(root):
        for direction in ('left','right'):
            candidate=rotate(root,p,direction)
            if candidate is None:continue
            result=check(candidate,ls,cases,excluded)
            if result is None:rejected+=1;continue
            result.update(pivot=p,direction=direction,root=candidate)
            good.append((candidate,result))
            records.append(result)
    good.sort(key=lambda x:(x[1]['unique_pairs'],x[1]['maximum_zero_run'],x[1]['maximum_depth']))
    interesting=[(candidate,r) for candidate,r in good if r['unique_pairs']<203 or r['maximum_zero_run']<base['maximum_zero_run']]
    for k,(candidate,r) in enumerate(interesting[:20]):dump_graph(candidate,OUT/f'rotation_candidate_{k:02}.json',r)
    out={'source_sha256':a.EXPECTED,'baseline':base,'admitted':len(good),'rejected':rejected,
         'seconds':time.monotonic()-began,'interesting':len(interesting),'records':records,
         'best':good[0][1] if good else None}
    (OUT/'rotation_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:out[k] for k in ['baseline','admitted','rejected','seconds','interesting','best']},indent=2))
    print(json.dumps([r for _,r in interesting[:20]],indent=2))

if __name__=='__main__':main()
