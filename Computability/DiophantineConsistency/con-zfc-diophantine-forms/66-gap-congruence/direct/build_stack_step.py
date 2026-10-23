#!/usr/bin/env python3
"""Author-built literal polynomial for a one-stack C222 proof machine.

This is a LOCAL transition polynomial, not a completed Con(ZFC) equation.
No upstream programs are imported or executed.
"""
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent
class DAG:
    def __init__(self): self.nodes=[]; self.cache={}
    def node(self,op,*args):
        if op in ('add','mul'): args=tuple(sorted(args))
        key=(op,)+args
        if key not in self.cache:
            self.cache[key]=len(self.nodes);self.nodes.append({'op':op,'args':list(args)})
        return self.cache[key]
    def c(self,n):return self.node('const',n)
    def v(self,n):return self.node('var',n)
    def add(self,a,b):return self.node('add',a,b)
    def sub(self,a,b):return self.node('sub',a,b)
    def mul(self,a,b):return self.node('mul',a,b)
    def sq(self,a):return self.mul(a,a)
    def sum(self,seq):
        seq=list(seq);v=seq[0]
        for a in seq[1:]:v=self.add(v,a)
        return v
    def prod(self,seq):
        seq=list(seq);v=seq[0]
        for a in seq[1:]:v=self.mul(v,a)
        return v

def build():
    d=DAG(); one,two,three,four=map(d.c,[1,2,3,4]);
    S,Sp,a,b,c,u,v=map(d.v,['S','Sp','a','b','c','u','v'])
    add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    def I(x,y):
        z=add(x,y)
        return add(mul(two,mul(z,add(z,one))),mul(four,y))
    def Rel(x,y):return add(I(x,y),one)
    def All(x,y):return add(I(x,y),two)
    def Eq(x,y):return add(I(x,y),three)
    def Neg(x):return I(x,one)
    def Ex(x,y):return Neg(All(x,Neg(y)))
    def Req(b,k,m):return All(b,I(m,Neg(All(b,I(m,Neg(Rel(b,k)))))))
    def Clos(a,b,k,m):return All(b,I(Rel(b,k),Neg(All(a,I(m,Neg(All(a,I(All(k,I(Rel(k,a),Rel(k,b))),Req(b,k,m)))))))))
    def Bundle(a,b,c):return Neg(I(I(Rel(a,b),All(c,Rel(a,b))),All(c,I(Clos(a,b,c,c),Neg(Req(b,c,c))))))
    rows=[Ex(a,Eq(a,b)),I(All(a,I(b,c)),I(All(a,b),All(a,c))),
        I(Eq(a,b),I(Rel(c,a),Rel(c,b))),I(All(a,All(b,c)),All(b,All(a,c))),
        I(Eq(c,a),I(Rel(c,b),Rel(a,b))),I(Ex(a,All(a,b)),b),
        I(Eq(c,a),I(Eq(c,b),All(Rel(a,b),Eq(a,b)))),
        I(I(I(c,u),a),I(I(a,c),I(b,c)))]
    bundle=Bundle(a,b,c)
    # L(x,h,t)=0 iff x=1+Cantor(h,t).
    def L(x,h,t):
        ht=add(h,t)
        return sub(sub(mul(two,x),two),add(mul(ht,add(ht,one)),mul(two,t)))
    def ss(rs):return d.sum(sq(r) for r in rs)
    # Separate squares preserve natural values at every nonlinear wire.
    guard=sub(mul(sq(sub(c,a)),sq(sub(c,b))),sq(add(u,one)))
    axiom=d.prod([sq(v)]+[sq(sub(v,row)) for row in rows]+[ss([sub(v,bundle),guard])])
    branches={
      'axiom':add(sq(L(Sp,v,S)),axiom),
      'mp':ss([L(S,I(a,b),v),L(v,a,c),L(Sp,b,c)]),
      'gen':ss([L(S,b,c),L(Sp,All(a,b),c)])}
    out=d.prod(branches.values())
    live=set()
    def visit(i):
        if i in live:return
        live.add(i)
        if d.nodes[i]['op'] not in ['var','const']:
            for j in d.nodes[i]['args']:visit(j)
    visit(out)
    assert len(live)==len(d.nodes)
    degrees=[]
    for n in d.nodes:
        op,args=n['op'],n['args']
        degrees.append(0 if op=='const' else 1 if op=='var' else sum(degrees[j] for j in args) if op=='mul' else max(degrees[j] for j in args))
    return {'schema':'literal-binary-arithmetic-dag-v1','domain':'natural numbers',
      'meaning':'local transition relation only; not a complete consistency equation',
      'state_inputs':['S'],'state_outputs':['Sp'],
      'existential_witnesses':['a','b','c','u','v'],
      'nodes':d.nodes,'output':out,'branches':branches,
      'operation_count':sum(n['op'] not in ['var','const'] for n in d.nodes),
      'syntactic_degree_upper_bound':degrees[out],
      'branch_degree_upper_bounds':{k:degrees[v] for k,v in branches.items()}}

if __name__=='__main__':
    obj=build();(ROOT/'stack_step.json').write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps({k:obj[k] for k in ['operation_count','syntactic_degree_upper_bound','branch_degree_upper_bounds']},indent=2))
