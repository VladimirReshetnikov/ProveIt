#!/usr/bin/env python3
"""Compile an AX binary grammar reusing PA196's unchanged macro readers."""
import symbolic as S
from pathlib import Path
import json,sys,re
from collections import defaultdict

WORK=Path(__file__).resolve().parents[1]
TOKENS={'node49':'P','node58':'H','node55':'A','node70':'D','node65':'C','node72':'R','node75':'S','node142':'G','node150':'K'}

def replace(t,old,new):
    if t==old:return new
    if t[0]=='leaf':return t
    return (replace(t[0],old,new),replace(t[1],old,new))

def compile_grammar(data=None):
    root,defs=S.source_tree()
    named=json.loads((WORK/'verification/node_map.json').read_text())
    original=S.load_machine()
    if data is None:newax=defs['x67']
    else:
        atom={v:defs[k] for k,v in TOKENS.items()}
        atom['i']=('leaf',('inc',1));atom['B']=('leaf',('breakTo',1))
        def expand(name):
            if name in atom:return atom[name]
            a,b=data['rules'][name]
            return (expand(a),expand(b))
        newax=expand(data['root'])
    # Macro roots and all their closed, already stored subtrees may be reused.
    fixed={t:named[name][0] for name,t in defs.items() if name.startswith('node') and int(name[4:])<=150 and len(named[name])==1}
    fixed[('leaf',('inc',1))]=58
    machine={k:v for k,v in original.items() if k[0]<134}
    allocated={};newrows={}
    def emit(t):
        if t in fixed:return fixed[t]
        if t in allocated:return allocated[t]
        if t[0]=='leaf':raise ValueError(('unknown leaf',t))
        a,b=t
        def child_row(child,read):
            if child==('leaf',('breakTo',1)):
                return (0,-1,131 if read else 5)
            return read,1,emit(child)
        row0=child_row(a,0);row1=child_row(b,1)
        q=1000+len(allocated);allocated[t]=q
        newrows[q,0]=row0;newrows[q,1]=row1
        return q
    newentry=emit(newax)
    machine.update(newrows);machine[89,1]=(1,1,newentry)
    newtree=replace(root,defs['x67'],newax)
    return machine,newtree,allocated,newentry

def check(machine,tree,all_failures=False):
    sites=S.flatten(tree)
    assert len(sites)==3812
    old=S.all_sites
    oldcodes=S.instructions(old());newcodes=S.instructions(sites)
    unchanged=oldcodes==newcodes
    S.all_sites=lambda:sites
    failures=[];lens=[]
    try:
        assert S.check_engine(machine)
        for i,branch,br,s,t in S.contracts():
            v=S.execute(machine,br,s,t)
            if v is None:
                failures.append((i,branch))
                if not all_failures:break
            else:lens.append(v[0])
    finally:S.all_sites=old
    return dict(states=len(machine)//2,unchanged_instructions=unchanged,sites=len(sites),max_path=max(map(lambda s:len(s[0]),sites)),failures=failures,passed=len(lens),max_symbolic=max(lens,default=0))

if __name__=='__main__':
    data=json.loads(Path(sys.argv[1]).read_text()) if len(sys.argv)>1 else None
    machine,tree,allocated,entry=compile_grammar(data)
    print('new reader states',len(allocated),'entry',entry,flush=True)
    print(json.dumps(check(machine,tree,True),indent=2),flush=True)
    name=Path(sys.argv[1]).stem if len(sys.argv)>1 else 'pure_baseline'
    out=WORK/'verification/compiled';out.mkdir(exist_ok=True)
    (out/(name+'.tm')).write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for (q,b),(w,d,n) in sorted(machine.items())))
    (out/(name+'.json')).write_text(json.dumps(dict(tree=tree,entry=entry,allocated_nodes=len(allocated))))
