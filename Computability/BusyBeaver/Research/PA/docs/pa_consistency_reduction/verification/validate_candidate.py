#!/usr/bin/env python3
"""Compile, extend the return scan, fold a maximum matching, verify all sites."""
import symbolic as S
import compile_grammar as C
import optimize_extended as O
from pathlib import Path
import json,sys,time,collections

def make(name):
    data=json.loads(Path(name).read_text())
    def dec(q):return tuple(map(dec,data['rules'][q]))if q in data['rules']else q
    grammar=dec(data['root'])
    score,nn,nfold,edges=O.evaluate(grammar)
    machine,tree,allocated,entry=C.compile_grammar(data)
    extra=max(0,O.zero_shape(grammar)[1]-6)
    if extra:
        machine[34,0]=(0,-1,2000)
        for j in range(extra):
            q=2000+j
            machine[q,0]=(0,1,69)if j==extra-1 else (0,-1,q+1)
            machine[q,1]=(1,-1,3)
    assert len(machine)//2==134+nn+extra
    es=collections.defaultdict(list);detail={}
    for q,r,ds in edges:es[q].append(r);detail[q,r]=ds
    mate={}
    def augment(q,seen):
        for r in es[q]:
            if r in seen:continue
            seen.add(r)
            if r not in mate or augment(mate[r],seen):mate[r]=q;return True
        return False
    for q in es:augment(q,set())
    assert len(mate)==nfold
    mapping={r:q for r,q in mate.items()}
    foldrows={};certificate=[]
    for r,q in sorted(mate.items()):
        ds=detail[q,r]
        for b,h in enumerate(ds):
            if h is None:foldrows[q,b]=machine[q,b]
            else:foldrows[q,b]=(b,-1,h)
        certificate.append(dict(keep=q,drop=r,helpers=ds))
    folded=machine|foldrows
    folded={k:(w,d,mapping.get(t,t))for k,(w,d,t)in folded.items()if k[0]not in mapping}
    return machine,folded,tree,dict(extra_scanner_states=extra,new_readers=nn,folds=certificate,entry=entry,score=score)

def main():
    name=sys.argv[1]
    pure,folded,tree,cert=make(name)
    print('candidate',name,'states',len(folded)//2,'metadata',cert,flush=True)
    print('pure',json.dumps(C.check(pure,tree,True)),flush=True)
    check=C.check(folded,tree,True)
    print('folded',json.dumps(check),flush=True)
    out=Path(__file__).with_name('candidates');out.mkdir(exist_ok=True)
    tag=Path(name).stem
    (out/(tag+'.tm')).write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n'for(q,b),(w,d,n)in sorted(folded.items())))
    (out/(tag+'.json')).write_text(json.dumps(dict(tree=tree,certificate=cert,check=check),indent=2))

if __name__=='__main__':main()
