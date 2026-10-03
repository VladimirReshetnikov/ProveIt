#!/usr/bin/env python3
"""Produce explicit L/S/F/X symbolic proofs; no integer-code expansion."""
from pathlib import Path
import json
from shared_compression import create, Memo, SymbolicMemo, bitbound


def main():
    A,d=create();X=A.var('X');SX=A.S(X);SSX=A.S(SX)
    cases=[]
    for name,inp in [('base0',A.L),('base1',A.S(A.L))]:
        M=Memo(A);assert M.app(d['R'],inp)==d['I']
        rows={k:(z,(0,h),ps) for k,(z,h,ps) in M.rows.items()}
        cases.append((name,(d['R'],inp),None,rows))
    M=SymbolicMemo(A,(d['R'],SX),d['I']);assert M.app(d['R'],SSX)==d['I']
    cases.append(('step',(d['R'],SSX),(d['R'],SX),M.rows))
    nodes=[];renumber={}
    def visit(i):
        if i in renumber:return renumber[i]
        n=A.nodes[i];assert n[0] in ['L','S','F','v']
        if n[0]=='v':
            assert n[1]=='X';out=['X']
        else:out=[n[0]]+[visit(j) for j in n[1:]]
        renumber[i]=len(nodes);nodes.append(out);return renumber[i]
    outcases=[]
    for name,root,oracle,rows in cases:
        keys=[root]+[k for k in rows if k!=root];idx={k:i for i,k in enumerate(keys)}
        outrows=[]
        for key in keys:
            z,h,ps=rows[key]
            outrows.append(dict(x=visit(key[0]),y=visit(key[1]),z=visit(z),
                                cost=list(h),premises=[idx[p] for p in ps],oracle=key==oracle))
        outcases.append(dict(name=name,rows=outrows))
    names={k:visit(v) for k,v in dict(R=d['R'],I=d['I'],L=A.L,X=X,SX=SX,SSX=SSX).items()}
    package=dict(format='original-jay-symbolic-application-dag-v1',nodes=nodes,names=names,cases=outcases)
    here=Path(__file__).resolve().parent
    (here/'shared_symbolic_proofs.json').write_text(json.dumps(package,indent=2)+'\n')
    print(json.dumps(dict(constructor_templates=len(nodes),rows={x['name']:len(x['rows']) for x in outcases}),indent=2))

if __name__=='__main__':main()
