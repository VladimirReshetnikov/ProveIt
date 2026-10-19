#!/usr/bin/env python3
"""Independent full control-graph and exact history checker for source search."""
from pathlib import Path
from functools import cache
import argparse,json,hashlib

HERE=Path(__file__).resolve().parent
DEFAULT=HERE/'boundary_sites_input.json'

def source_graph(rows):
    leaf={p:(op,arg) for p,op,arg in rows}
    assert len(leaf)==len(rows)
    internal={p[:i] for p in leaf for i in range(len(p))}
    assert not internal & leaf.keys() and len(internal)+1==len(leaf)
    assert all(p+b in internal or p+b in leaf for p in internal for b in '01')
    order=sorted(leaf); ordinal={p:i for i,p in enumerate(order)}
    @cache
    def first(p):
        while p not in leaf:
            assert p in internal;p+='0'
        return ordinal[p]
    def next_subtree(p):
        i=p.rfind('0')
        return p[:i]+'1' if i>=0 else ''
    def cut(p,bit,count):
        found=[i for i,b in enumerate(p) if b==bit]
        return p[:found[-count]] if len(found)>=count else ''
    out=[];guards=0
    for p in order:
        op,arg=leaf[p]
        if op=='CI':targets=[first(next_subtree(p))]
        elif op=='CD':targets=[first(next_subtree(cut(p,'0',1))),first(next_subtree(p))]
        elif op=='CB':targets=[first(next_subtree(cut(p,'0',arg)))]
        elif op=='CC':targets=[first(cut(p,'1',arg))]
        else:assert op=='CH';targets=['HALT']
        out.append([op,arg,targets]);guards+=len(targets)
    return out,dict(leaves=len(leaf),distinct_paths=len(leaf),guards=guards,maximum_depth=max(map(len,leaf)),maximum_zero_run=max(max(map(len,p.split('1'))) for p in leaf))

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,default=DEFAULT)
    ap.add_argument('--candidate',type=Path,default=HERE/'best_source.json')
    ap.add_argument('--output',type=Path,default=HERE/'source_result_certificate.json')
    args=ap.parse_args()
    old=json.loads(args.baseline.read_text());J=json.loads(args.candidate.read_text());S=[tuple(x) for x in J['structures']]
    original=list(S);index={x:i for i,x in enumerate(S)}
    def cons(a,b):
        x=a,b
        if x not in index:index[x]=len(S);S.append(x)
        return index[x]
    @cache
    def paths(n):
        x=S[n]
        if isinstance(x[0],str):return (('',x[0],x[1]),)
        return tuple((str(b)+p,op,arg) for b in (0,1) for p,op,arg in paths(x[b]))
    def live(n):
        out=set();todo=[n]
        while todo:
            k=todo.pop()
            if k in out:continue
            out.add(k)
            if isinstance(S[k][0],int):todo.extend(S[k])
        return out
    def no_break(n):
        return all(not ((op=='CD' and p.count('0')<1) or (op=='CB' and p.count('0')<arg)) for p,op,arg in paths(n))
    def no_continue(n):
        return all(not (op=='CC' and p.count('1')<arg) for p,op,arg in paths(n))
    def closed(n):
        return no_break(n) and no_continue(n) and all(op!='CH' for p,op,arg in paths(n))
    def replace(root,node,alternative):
        @cache
        def visit(k):
            if k==node:return alternative
            if isinstance(S[k][0],str):return k
            return cons(*map(visit,S[k]))
        return visit(root)
    root=J['original_root'];assert [list(x) for x in paths(root)]==old
    exact_steps=[]
    original_graph,oldstats=source_graph(old)
    for i,m in enumerate(J['history']):
        node,alt=m['node'],m['alternative'];a,b,c=m['chunks']
        assert node in live(root)
        assert no_break(a) and no_continue(c)
        if m['direction']=='L':
            assert S[node]==(a,cons(b,c)) and S[alt]==(cons(a,b),c)
        else:
            assert m['direction']=='R'
            assert S[node]==(cons(a,b),c) and S[alt]==(a,cons(b,c))
        root=replace(root,node,alt)
        graph,stats=source_graph(paths(root))
        assert graph==original_graph,(i,'full source graph differs')
        exact_steps.append(dict(index=i+1,direction=m['direction'],node=node,alternative=alt,chunks=[a,b,c],all_chunks_closed=all(map(closed,(a,b,c))),**stats))
    assert root==J['root']
    final=[list(x) for x in paths(root)];assert final==J['sites']
    graph,newstats=source_graph(final);assert graph==original_graph
    newstats['distinct_source_nodes']=len(live(root))
    assert J['score']==[newstats['distinct_source_nodes'],newstats['maximum_zero_run'],newstats['maximum_depth']]
    result=dict(status='EXACT_SOURCE_CONTROL_GRAPH_PASS',binary_status='NO_BINARY_TABLE_CLAIMED',before=oldstats,after=newstats,history=exact_steps,rotations_beyond_all_closed=sum(not m['all_chunks_closed'] for m in exact_steps),baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest(),candidate_sha256=hashlib.sha256(args.candidate.read_bytes()).hexdigest(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='history'},indent=2))

if __name__=='__main__':main()
