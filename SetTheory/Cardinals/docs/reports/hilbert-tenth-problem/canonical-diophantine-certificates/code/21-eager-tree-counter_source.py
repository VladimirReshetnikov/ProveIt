#!/usr/bin/env python3
"""Explicit finite counter-table -> weak-CBV source lambda constructor.

Input rows use ADD(j,next), SUB(j,positive_next,zero_next), or HALT.
The designated halt label may be absent from rows and is then added.
No external source program is executed by this file.
"""
from eager_compiler import V,A,Lam,Z,ID,scott_nat,Algebra,source_eval,closure_tree
import json
from pathlib import Path

def counter_term(machine, values):
    rows = dict(machine['rows'])
    halt = machine['halt']
    if halt not in rows: rows[halt] = ['HALT']
    labels = sorted(rows)
    k,m = len(machine['registers']),len(labels)
    assert len(values)==k and k>=1
    qbinders = ['sel'+str(i) for i in range(m)]
    Q = {label:Lam(qbinders,V(qbinders[i])) for i,label in enumerate(labels)}
    regs = ['reg'+str(j) for j in range(k)]
    vs = [V(r) for r in regs]
    succ = Lam('sn sz ss',A(V('ss'),V('sn')))
    zero = scott_nat(0)
    def call(label, args): return A(V('loop'),Q[label],*args)
    branches=[]
    for label in labels:
        row=rows[label]
        if row[0]=='HALT': body=vs[0]
        elif row[0]=='ADD':
            _,j,nxt=row
            args=list(vs);args[j]=A(succ,vs[j])
            body=call(nxt,args)
        elif row[0]=='SUB':
            _,j,pos,nul=row
            az=list(vs);az[j]=zero
            ap=list(vs);ap[j]=V('pred')
            body=A(vs[j],Lam('delay',call(nul,az)),
                   Lam('pred delay',call(pos,ap)),ID)
        else: raise ValueError(row)
        branches.append(Lam(regs,body))
    step=Lam(['loop','state']+regs,A(A(V('state'),*branches),*vs))
    return A(A(Z,step),Q[machine['entry']],*(scott_nat(n) for n in values))

def main():
    alg=Algebra()
    true=Lam('bt bf',V('bt')); false=Lam('bt bf',V('bf'))
    iz=Lam('nn',A(V('nn'),true,Lam('np',false)))
    pred=Lam('nn',A(V('nn'),scott_nat(0),ID))
    machines=[
        ('increment',{'registers':['r'],'entry':'inc','halt':'halt',
          'rows':{'inc':['ADD',0,'halt']}},[0],1),
        ('decrement_positive',{'registers':['r'],'entry':'dec','halt':'halt',
          'rows':{'dec':['SUB',0,'halt','loop'],'loop':['ADD',0,'loop']}},[2],1),
        ('decrement_zero',{'registers':['r'],'entry':'dec','halt':'halt',
          'rows':{'dec':['SUB',0,'loop','halt'],'loop':['ADD',0,'loop']}},[0],0),
        ('transfer',{'registers':['r','s'],'entry':'dec','halt':'halt',
          'rows':{'dec':['SUB',1,'inc','halt'],'inc':['ADD',0,'dec']}},[1,2],3),
    ]
    checks=[]
    for name,machine,values,answer in machines:
        term=counter_term(machine,values)
        cl,steps=source_eval(term)
        assert cl is not None,name
        value,calls=alg.eval(alg.compile(term))
        assert value==closure_tree(alg,cl),name
        observations=[]
        for i in range(answer+2):
            t=term
            for _ in range(i): t=A(pred,t)
            observed,_=alg.eval(alg.compile(A(iz,t)))
            want=alg.compile(true if i>=answer else false)
            assert observed==want,(name,i)
            observations.append(i>=answer)
        checks.append(dict(name=name,initial=values,expected=answer,
                           source_steps=steps,tree_kernel_calls=calls,
                           successive_zero_tests=observations))
    out=Path(__file__).with_name('counter_source_receipt.json')
    out.write_text(json.dumps(checks,indent=2)+'\n')
    print(json.dumps(checks,indent=2))

if __name__=='__main__':main()
