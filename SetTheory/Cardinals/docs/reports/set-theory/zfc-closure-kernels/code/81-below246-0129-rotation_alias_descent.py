#!/usr/bin/env python3
"""Search source reassociations while retaining original alias contracts.

Conservative search: keep every context-shared source subtree and every
borrowed helper subtree literally unchanged, and retain the one/two bits
of incoming context inspected by each alias. This is a candidate filter,
not a substitute for literal binary verification.
"""
import json
import time
from collections import Counter
from pathlib import Path
import rotation_control_repair as cr
r=cr.r

HERE=r.OUT;ROOT=HERE.parent

def setup(original):
    ng=json.loads((HERE/'passive_source_mapping.json').read_text())['node_grammar']
    state_nodes=json.loads((ROOT/'research/first_decoder_state_map.json').read_text())
    deps=json.loads((ROOT/'agent_states/original_alias_dependencies.json').read_text())
    node_state={n:int(q) for q,ns in state_nodes.items() for n in ns}
    table={}
    for line in (ROOT/'sources/context246/zfc-context246/machine/zfc_prefix246_old.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),d,int(t))
    shared={};depths={};fixed=set()
    for q,ns in state_nodes.items():
        gs=set(ng[str(n)] for n in ns)
        if len(gs)>1:
            shared[int(q)]=gs
            for g in gs:fixed.update(r.reachable(g))
            depths[int(q)]=2 if q=='143' else 1
    for q,d in deps.items():
        for g in d['borrowed_source_classes']:fixed.update(r.reachable(g))
        for b,path,target,trace in d['arcs']:
            head=0;lo=0
            for edge in trace:
                head+=1 if table[tuple(edge)][1]=='R' else -1;lo=min(lo,head)
            depths[int(q)]=max(depths.get(int(q),0),-lo)
    oldnodes=r.parse_nodes(r.a.PROGRAM.read_bytes());cursor=0;contexts={}
    def visit(n,p):
        nonlocal cursor
        start=cursor
        for b,e in enumerate(oldnodes[n]):
            if e[0]=='CN':visit(int(e[1]),p+str(b))
            else:cursor+=1
        q=node_state[n]
        if q in shared:
            depth=depths[q]
            contexts[start,cursor]=(ng[str(n)],depth,p[-depth:])
    visit(0,'')
    return fixed,contexts,shared,depths

def context_check(root,contexts):
    cursor=0;seen=0;ok=True
    def walk(i,p):
        nonlocal cursor,seen,ok
        if not ok:return
        e=r.entries[i];start=cursor
        if e[0]=='N':
            walk(e[1],p+'0');walk(e[2],p+'1')
            key=(start,cursor)
            if key in contexts:
                expected,depth,suffix=contexts[key]
                if i!=expected or p[-depth:]!=suffix:ok=False
                seen+=1
        else:cursor+=1
    walk(root,'')
    return ok and seen==len(contexts)

def score(root):
    counts=Counter(len(p)-len(p.rstrip('0')) for p,op,n in r.flatten(root) if op=='CD')
    return tuple(counts[n] for n in range(30,0,-1))

def describe(s):return {str(30-i):n for i,n in enumerate(s) if n}

def main():
    began=time.monotonic();raw=r.a.PROGRAM.read_bytes()
    ls,cases,by,first=r.a.read_program(raw);root=r.load(raw)
    fixed,contexts,shared,depths=setup(root)
    assert context_check(root,contexts)
    print(json.dumps(dict(protected_pairs=len(fixed),context_occurrences=len(contexts),
        alias_depths=depths,initial_score=describe(score(root)))),flush=True)
    records=[];checks=0
    for step in range(70):
        current=score(root);options=[]
        for p in r.reachable(root):
            if p in fixed:continue
            for direction in ('left','right'):
                c=r.rotate(root,p,direction)
                if c is None or len(r.reachable(c))>203:continue
                if max(max(map(len,pth.split('1'))) for pth,_,_ in r.flatten(c))>7:continue
                if not fixed.issubset(r.reachable(c)):continue
                s=score(c)
                if s<current:options.append((s,p,direction,c))
        options.sort();best=None
        for s,p,direction,c in options:
            if not context_check(c,contexts):continue
            answer=cr.repair(c,ls,cases,by,first);checks+=1
            if answer is None:continue
            new,meta=answer
            if meta['unique_pairs']>203 or not fixed.issubset(r.reachable(new)) or not context_check(new,contexts):continue
            best=new,meta,p,direction,s;break
        if best is None:break
        root,meta,p,direction,s=best
        meta.update(step=step+1,pivot=p,direction=direction,source_base='original203',
            protected_pairs=len(fixed),preserved_alias_context_occurrences=len(contexts),
            trailing_zero_decrement_histogram=describe(s))
        records.append({k:v for k,v in meta.items() if k!='edits'})
        r.dump_graph(root,HERE/f'rotation_alias7_candidate_{step+1:02}.json',meta)
        print(json.dumps(records[-1]),flush=True)
        if max(map(int,describe(s)))<7:break
    out=dict(seconds=time.monotonic()-began,checks=checks,records=records,
        final_histogram=describe(score(root)),protected_pairs=sorted(fixed),
        alias_depths=depths,context_count=len(contexts))
    (HERE/'rotation_alias7_results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('records','protected_pairs')},indent=2),flush=True)

if __name__=='__main__':main()
