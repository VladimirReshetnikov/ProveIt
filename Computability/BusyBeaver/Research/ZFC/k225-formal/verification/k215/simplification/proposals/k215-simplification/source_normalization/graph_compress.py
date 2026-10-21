#!/usr/bin/env python3
"""Explore a decrement/effect graph factorization of the pinned K215 source proof.

This is research evidence, not a replacement kernel proof. Path operations reuse
the pinned repository generator; graph quotienting and checks below are new.
"""
from __future__ import annotations
import collections, hashlib, importlib.util, json
from pathlib import Path
if not __debug__:
    raise SystemExit('Run this generator without Python -O; its validation uses assertions.')

BASE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('upstream_cert', BASE/'upstream/gen_cert.py')
mod=importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)

def dag_leaves(data):
    nodes=data['nodes']; leaves={}
    def walk(n,p):
        for bit,(op,arg) in enumerate(nodes[str(n)]):
            q=p+(bool(bit),)
            if op=='N': walk(arg,q)
            else: leaves[q]=(op,arg)
    walk(0,())
    return leaves

def effects(xs):
    return tuple(sorted(collections.Counter(xs).items()))

def graph(tree):
    ids={}; todo=collections.deque(); rows=[]; paths=[]
    def segment(p):
        s=mod.seg(tree,p)
        if s is None: raise ValueError('segment out of fuel')
        xs,p=s
        _,q=tree.tsite(p) # canonicalize implicit-zero prefixes to literal leaves
        if q not in ids:
            ids[q]=len(ids); paths.append(q); todo.append(q); rows.append(None)
        return effects(xs),ids[q]
    initial=segment(())
    while todo:
        p=todo.popleft(); (op,r),q=tree.tsite(p)
        if op=='EHalt': rows[ids[p]]=('H',)
        elif op=='EDecnz':
            yes=segment(mod.inc_path(q)); no=segment(mod.brk(1,q))
            rows[ids[p]]=('D',r,yes,no)
        else: raise ValueError(op)
    return initial,rows,paths

def quotient(rows):
    colors=[0]*len(rows); history=[]
    while True:
        intern={}; new=[]
        for row in rows:
            sig=row if row[0]=='H' else ('D',row[1],row[2][0],colors[row[2][1]],row[3][0],colors[row[3][1]])
            new.append(intern.setdefault(sig,len(intern)))
        history.append(len(intern))
        if new==colors: break
        colors=new
    qrows=[None]*(1+max(colors))
    for i,row in enumerate(rows):
        q=row if row[0]=='H' else ('D',row[1],(row[2][0],colors[row[2][1]]),(row[3][0],colors[row[3][1]]))
        old=qrows[colors[i]]
        assert old is None or old==q
        qrows[colors[i]]=q
    return colors,qrows,history

def main():
    sfile=BASE/'upstream/sites215.json'; dfile=BASE/'upstream/dagperm_nodes.json'
    ts=mod.Tree(mod.load(sfile)); td=mod.Tree(dag_leaves(json.loads(dfile.read_text())))
    cert=mod.generate(ts,td)
    a,ga,pa=graph(ts); b,gb,pb=graph(td)
    n=len(ga)
    shifted=[r if r[0]=='H' else ('D',r[1],(r[2][0],r[2][1]+n),(r[3][0],r[3][1]+n)) for r in gb]
    colors,qrows,hist=quotient(ga+shifted)
    assert a[0]==b[0] and colors[a[1]]==colors[n+b[1]]
    data={'schema':'K215-effect-quotient-v1','source_sha256':hashlib.sha256(sfile.read_bytes()).hexdigest(),'dag_sha256':hashlib.sha256(dfile.read_bytes()).hexdigest(),
          'root_effect':a[0],'root_class':colors[a[1]],'rows':qrows,
          'source_classes':colors[:n],'dag_classes':colors[n:],
          'source_paths':[''.join(map(lambda x:str(int(x)),p)) for p in pa],
          'dag_paths':[''.join(map(lambda x:str(int(x)),p)) for p in pb]}
    (BASE/'effect_quotient.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    stats={'original_paired_entries':len(cert),'original_nonzero_offsets':sum(x[2]!=0 for x in cert),'source_leaf_occurrences':len(ts.leaf),'dag_leaf_occurrences':len(td.leaf),'source_effect_states':len(ga),'dag_effect_states':len(gb),'quotient_states':len(qrows),'refinement_rounds':len(hist),'refinement_counts':hist,'quotient_file_bytes':(BASE/'effect_quotient.json').stat().st_size,'root_effect':a[0],'root_class':colors[a[1]]}
    (BASE/'effect_quotient_summary.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))

if __name__=='__main__': main()
