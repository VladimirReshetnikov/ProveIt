#!/usr/bin/env python3
"""Own fixed-program eager-application sharing experiment; original Jay kernel.
Imports only the companion compiler written for this packet, not upstream code.
"""
from eager_compiler import Algebra
import json
from pathlib import Path


def create():
    A=Algebra()
    L=A.L; I=A.I; K=A.S(L); KI=A.F(L,I)
    kap=lambda a:A.F(L,a)
    d=lambda a:A.S(A.S(a))
    KK=kap(K); KL=kap(L)
    zero=A.F(A.S(kap(KI)), A.F(A.S(KK),L))
    pred=A.F(A.S(KK),A.F(A.S(kap(kap(kap(L)))),
            A.F(A.S(A.F(A.S(KL),I)),KL)))
    def app(*xs):
        t=xs[0]
        for x in xs[1:]:t=A.app(t,x)
        return t
    def lam(names,body):
        for x in reversed(names.split()):body=A.bracket(x,body)
        return body
    f=A.var('f');x=A.var('x');v=A.var('v')
    half=lam('x',app(f,lam('v',app(x,x,v))))
    Z=lam('f',app(half,half))
    r=A.var('r');n=A.var('n')
    recurse=app(r,app(pred,n))
    body=app(app(zero,n),lam('unused',I),
             lam('unused',app(K,recurse,recurse)),L)
    functional=lam('r n',body)
    R,calls=A.eval(app(Z,functional),limit=100000)
    assert R is not None
    return A,dict(L=L,I=I,K=K,KI=KI,zero=zero,pred=pred,Z=Z,functional=functional,R=R,setup_calls=calls)


class Memo:
    def __init__(self,A): self.A=A;self.rows={};self.active=set()
    def app(self,x,y):
        key=(x,y)
        if key in self.rows:return self.rows[key][0]
        if key in self.active:raise ValueError('cycle')
        self.active.add(key)
        n=self.A.nodes[x]; ps=[]
        if n[0]=='L':z=self.A.S(y)
        elif n[0]=='S':z=self.A.F(n[1],y)
        else:
            assert n[0]=='F';left,b=n[1:];m=self.A.nodes[left]
            if m[0]=='L':z=b
            elif m[0]=='S':
                a=m[1];u=self.app(b,y);v=self.app(a,y);z=self.app(u,v)
                ps=[(b,y),(a,y),(u,v)]
            else:
                assert m[0]=='F';a,b=m[1:];u=self.app(y,a);z=self.app(u,b)
                ps=[(y,a),(u,b)]
        h=1+sum(self.rows[p][1] for p in ps)
        self.rows[key]=(z,h,ps)
        self.active.remove(key)
        return z


def bitbound(A,root,cache):
    if root in cache:return cache[root]
    n=A.nodes[root]
    if n[0]=='L':b=0
    elif n[0]=='S':b=bitbound(A,n[1],cache)+1
    else:
        assert n[0]=='F';b=2*max(bitbound(A,n[1],cache),bitbound(A,n[2],cache))+3
    cache[root]=b
    return b


def main():
    A,d=create();t=d['L'];results=[];prev=None
    for n in range(21):
        M=Memo(A);o=M.app(d['R'],t)
        assert o==d['I']
        h=M.rows[(d['R'],t)][1]
        cached={}
        maxbit=max(bitbound(A,v,cached) for key,(out,cost,ps) in M.rows.items() for v in [*key,out])
        ZM=Memo(A);PM=Memo(A)
        z=ZM.app(d['zero'],t);p=PM.app(d['pred'],t)
        assert z==(d['K'] if n==0 else d['KI'])
        if n:assert p==last_t
        results.append(dict(n=n,distinct_calls=len(M.rows),unfolded_calls=h,
            max_scalar_bitlength_upper_bound=maxbit,
            h_minus_twice_previous=None if prev is None else h-2*prev,
            zero_cost=ZM.rows[(d['zero'],t)][1],pred_cost=PM.rows[(d['pred'],t)][1]))
        prev=h;last_t=t;t=A.S(t)
    here=Path(__file__).resolve().parent
    literal=A.export_value(d['R'])
    (here/'shared_compression_program.json').write_text(json.dumps(literal,indent=2)+'\n')
    receipt=dict(program_constructor_dag_nodes=len(literal['nodes']),
            program_code_bitlength_upper_bound=bitbound(A,d['R'],{}),setup_calls=d['setup_calls'],results=results)
    (here/'shared_compression_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()

class SymbolicMemo(Memo):
    def __init__(self,A,oracle,output):
        super().__init__(A)
        self.oracle=oracle;self.output=output
    def app(self,x,y):
        key=(x,y)
        if key in self.rows:return self.rows[key][0]
        if key==self.oracle:
            self.rows[key]=(self.output,(1,0),[])
            return self.output
        if key in self.active:raise ValueError('symbolic cycle')
        self.active.add(key)
        n=self.A.nodes[x];ps=[]
        if n[0]=='L':z=self.A.S(y)
        elif n[0]=='S':z=self.A.F(n[1],y)
        elif n[0]=='F':
            left,b=n[1:];m=self.A.nodes[left]
            if m[0]=='L':z=b
            elif m[0]=='S':
                a=m[1];u=self.app(b,y);v=self.app(a,y);z=self.app(u,v)
                ps=[(b,y),(a,y),(u,v)]
            elif m[0]=='F':
                a,b=m[1:];u=self.app(y,a);z=self.app(u,b);ps=[(y,a),(u,b)]
            else:raise ValueError(('unknown nested shape',m))
        else:raise ValueError(('unknown function shape',n))
        h=(sum(self.rows[p][1][0] for p in ps),1+sum(self.rows[p][1][1] for p in ps))
        self.rows[key]=(z,h,ps);self.active.remove(key);return z
