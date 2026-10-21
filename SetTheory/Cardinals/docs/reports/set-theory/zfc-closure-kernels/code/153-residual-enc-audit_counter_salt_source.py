#!/usr/bin/env python3
"""Cross-audit DISCARD/RESET against the literal 4,741-leaf source tree.

This is separate from an abstract command interpreter.  It executes the
actual source AST, accelerating only transfers, the Cantor pairing loop,
the Cantor reader, and the proved asymmetric comparator.  Formula values
remain hash-consed natural-arithmetic expressions, so huge formula codes
need not be expanded.  Unknown branch conditions are errors.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
from math import isqrt
import argparse,json,hashlib

D=lambda i:('CD',i)
I=lambda i:('CI',i)
C=lambda k:('CC',k)
B=lambda k:('CB',k)
F=lambda a,b:(D(a),(I(b),C(2)))
EA=((D(5),((D(6),C(2)),(I(6),(D(5),C(1))))),(D(6),B(1)))
PAIR_LOOP=((D(1),(I(7),(I(6),C(3)))),(D(6),((I(7),F(6,1)),C(3))))
def UNPAIR(i):return ((D(i),(I(7),(((D(6),B(1)),F(7,6)),C(3)))),F(7,i))

def tree(rows):
    leaves={p:(o,r)for p,o,r in rows}
    def go(p):return leaves[p]if p in leaves else (go(p+'0'),go(p+'1'))
    return go('')
def subtree(t,p):
    for x in p:t=t[int(x)]
    return t
def leaf(n):return isinstance(n[0],str)

class Values:
    def __init__(self):self.nodes=[];self.index={};self.zero=self.num(0)
    def node(self,op,args):
        key=(op,tuple(args))
        if key not in self.index:self.index[key]=len(self.nodes);self.nodes.append(key)
        return self.index[key]
    def num(self,n):return self.node('n',(n,))
    def var(self,name,lower=0):return self.node('v',(name,lower))
    def linear(self,x):
        op,args=self.nodes[x]
        if op=='n':return args[0],{}
        if op=='a':return args[0],dict(args[1])
        return 0,{x:1}
    def sum(self,*terms):
        k=0;items=Counter()
        for coef,x in terms:
            a,z=self.linear(x);k+=coef*a
            for t,c in z.items():items[t]+=coef*c
        z=tuple(sorted((t,c)for t,c in items.items()if c))
        if not z:return self.num(k)
        if k==0 and len(z)==1 and z[0][1]==1:return z[0][0]
        return self.node('a',(k,z))
    def add(self,a,b):return self.sum((1,a),(1,b))
    def plus(self,a,n):return self.add(a,self.num(n))
    def scale(self,a,n):return self.sum((n,a),)
    def pair(self,a,b):
        if a==b==self.zero:return self.zero
        return self.node('p',(a,b))
    @lru_cache(None)
    def concrete(self,a):
        op,z=self.nodes[a]
        if op=='n':return z[0]
        if op=='v':return None
        if op=='a':
            n=z[0]
            for v,c in z[1]:
                vv=self.concrete(v)
                if vv is None:return None
                n+=c*vv
        elif op=='p':
            x,y=map(self.concrete,z)
            if x is None or y is None:return None
            n=(x+y)*(x+y+1)//2+y
        else:return None
        return n if n.bit_length()<=4096 else None
    @lru_cache(None)
    def lower(self,a):
        op,z=self.nodes[a]
        if op=='n':return min(4,z[0])
        if op=='v':return min(4,z[1])
        if op=='a':
            if any(c<0 for v,c in z[1]):return 0
            return max(0,min(4,z[0]+sum(c*self.lower(v)for v,c in z[1])))
        if op=='p':
            x,y=map(self.lower,z);return min(4,(x+y)*(x+y+1)//2+y)
        return 0
    def mod4(self,a):
        k,z=self.linear(a)
        return k%4 if all(c%4==0 for c in z.values())else None
    def equal(self,a,b):
        if a==b:return True
        aa,bb=self.concrete(a),self.concrete(b)
        if aa is not None and bb is not None:return aa==bb
        if aa in(0,1,2,3)and self.lower(b)>aa:return False
        if bb in(0,1,2,3)and self.lower(a)>bb:return False
        if aa is not None and self.mod4(b)is not None and aa%4!=self.mod4(b):return False
        if bb is not None and self.mod4(a)is not None and bb%4!=self.mod4(a):return False
        raise AssertionError(('unresolved symbolic equality',self.nodes[a],self.nodes[b]))
    def residual(self,a,b):
        """max(b-a-1,0), only when justified by exact arithmetic facts."""
        aa,bb=self.concrete(a),self.concrete(b)
        if bb in(0,1)or a==b:return self.zero
        if aa is not None and bb is not None:return self.num(max(bb-aa-1,0))
        if aa==0 and self.lower(b)>0:return self.plus(b,-1)
        if bb is not None and self.lower(a)>=bb:return self.zero
        raise AssertionError(('unresolved residual',a,b))
    def unpair(self,a):
        op,z=self.nodes[a]
        if op=='p':return z
        n=self.concrete(a)
        if n is not None:
            k=(isqrt(8*n+1)-1)//2;y=n-k*(k+1)//2;return self.num(k-y),self.num(y)
        raise AssertionError(('unpair of an arbitrary underlying tail',self.nodes[a]))

@lru_cache(None)
def transfer(node):
    if leaf(node)or node[0][0]!='CD' or not leaf(node[0]):return None
    r=node[0][1];rows=[]
    def walk(n,p=''):
        if leaf(n):rows.append((p,n))
        else:walk(n[0],p+'0');walk(n[1],p+'1')
    walk(node[1])
    if rows[-1][1][0]!='CC' or any(n[0]!='CI'for p,n in rows[:-1]):return None
    p,(_,k)=rows[-1]
    if k-p.count('1')!=1:return None
    counts=Counter(n[1]for p,n in rows[:-1])
    if r in counts:return None
    return r,tuple(counts.items())

class Source:
    def __init__(self,t,v):self.t=t;self.v=v;self.command=subtree(t,'111');self.steps=0;self.accelerated=Counter();self.outcomes=Counter()
    def run(self,node,registers):
        r=list(registers);v=self.v;z=v.zero
        def ev(n):
            self.steps+=1
            if self.steps>1000000:raise RuntimeError('unexpected source loop')
            tr=transfer(n)
            if tr is not None:
                src,dsts=tr;amount=r[src];r[src]=z
                for dst,k in dsts:r[dst]=v.add(r[dst],v.scale(amount,k))
                self.accelerated['transfer']+=1;return 'N',0
            if n==PAIR_LOOP:
                r[7]=v.add(r[7],v.pair(r[6],r[1]));r[1]=r[6]=z
                self.accelerated['pair']+=1;return 'N',0
            for i in(2,8):
                if n==UNPAIR(i):
                    a,b=v.unpair(v.add(r[i],v.pair(r[6],r[7])));r[i]=b;r[6]=a;r[7]=z
                    self.accelerated['unpair']+=1;return 'N',0
            if n==EA:
                equal=v.equal(r[5],r[6]);res=v.residual(r[5],r[6]);r[5]=z;r[6]=res
                self.accelerated['asymmetric']+=1;return ('N',0)if equal else ('B',1)
            if leaf(n):
                op,k=n
                if op=='CI':r[k]=v.plus(r[k],1);return 'N',0
                if op=='CD':
                    if v.equal(r[k],z):return 'B',1
                    r[k]=v.plus(r[k],-1);return 'N',0
                if op=='CB':return 'B',k
                if op=='CC':return 'C',k
                if op=='CH':return 'H',0
                raise ValueError(n)
            while True:
                kind,k=ev(n[0])
                if kind=='B':return ('N',0)if k==1 else ('B',k-1)
                if kind!='N':return kind,k
                kind,k=ev(n[1])
                if kind=='C':
                    if k==1:continue
                    return 'C',k-1
                return kind,k
        result=ev(node)
        return result,r
    def step(self,op,state):
        t,w,d,h=state;v=self.v;r=[v.zero]*9;r[0]=v.num(23);r[1]=t;r[2]=w;r[4]=d;r[5]=h
        if op=='AX0':r[3]=v.num(3)
        elif op=='NIP':r[3]=v.num(2)
        elif op=='DROP':r[3]=v.num(1)
        elif op=='MP1':r[3]=v.zero;r[4]=v.plus(d,1)
        else:raise ValueError(op)
        event,r=self.run(self.command,r)
        if event[0]=='H':return None
        assert event==('N',0),event
        self.outcomes[(op,event)]+=1
        event,r=self.run(F(6,4),r)
        assert event==('N',0) and all(r[i]==v.zero for i in(3,6,7,8))
        assert r[0]==v.num(23)
        return r[1],r[2],r[4],r[5]
    def block(self,ops,state):
        for op in ops:
            state=self.step(op,state)
            if state is None:return None
        return state

def primitive_run(node, registers):
    """Finite reference interpreter with no accelerated macro rules."""
    r=list(registers);steps=0
    def ev(n):
        nonlocal steps
        steps+=1
        if steps>2000000:raise RuntimeError('finite reference step bound')
        if leaf(n):
            op,k=n
            if op=='CI':r[k]+=1;return 'N',0
            if op=='CD':
                if r[k]==0:return 'B',1
                r[k]-=1;return 'N',0
            if op=='CB':return 'B',k
            if op=='CC':return 'C',k
            if op=='CH':return 'H',0
            raise ValueError(n)
        while True:
            kind,k=ev(n[0])
            if kind=='B':return ('N',0)if k==1 else ('B',k-1)
            if kind!='N':return kind,k
            kind,k=ev(n[1])
            if kind=='C':
                if k==1:continue
                return 'C',k-1
            return kind,k
    outcome=ev(node)
    return outcome,r,steps

def acceleration_checks(t):
    """Check every transfer pattern present and each nonlinear acceleration.

    These bounded diagnostics complement the stated loop invariants; they
    do not turn the audit into a proof-assistant kernel certificate.
    """
    from itertools import product
    nodes=set()
    def visit(n):
        if n in nodes:return
        nodes.add(n)
        if not leaf(n):visit(n[0]);visit(n[1])
    visit(t)
    patterns=sorted((n for n in nodes if transfer(n)is not None),key=repr)
    assert EA in nodes and PAIR_LOOP in nodes and all(UNPAIR(i)in nodes for i in(2,8))
    v=Values();s=Source(t,v);counts=Counter();visits=0
    def check(name,n,r):
        nonlocal visits
        out,w,steps=primitive_run(n,r);visits+=steps
        out2,w2=s.run(n,[v.num(x)for x in r])
        assert out==out2 and w==[v.concrete(x)for x in w2],(name,r,out,w,out2,w2)
        counts[name]+=1
    for n in patterns:
        src,_=transfer(n)
        for x in range(17):
            r=list(range(9));r[src]=x;check('transfer',n,r)
    for a,b,c in product(range(7),repeat=3):
        r=list(range(9));r[6]=a;r[1]=b;r[7]=c;check('pair',PAIR_LOOP,r)
    for i in(2,8):
        for n,a,b in product(range(13),range(5),range(5)):
            r=list(range(9));r[i]=n;r[6]=a;r[7]=b;check('unpair',UNPAIR(i),r)
    for a,b in product(range(17),repeat=2):
        r=list(range(9));r[5]=a;r[6]=b;check('asymmetric',EA,r)
    return {'status':'PASS','finite_cases':dict(counts),'distinct_transfer_patterns':len(patterns),'reference_source_node_visits':visits}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    raw=args.sites.read_bytes();rows=json.loads(raw);t=tree(rows);acceleration_receipt=acceleration_checks(t);v=Values();s=Source(t,v);w=v.var('arbitrary_stack');tops=[v.zero,v.num(1),v.var('arbitrary_T_ge_2',2)];ds=[v.zero,v.var('arbitrary_D_ge_1',1)]
    tests=[]
    for top in tops:
        for d in ds:
            initial=(top,w,d,v.zero)
            discard=s.block(['MP1','AX0']+['NIP']*10,initial)
            assert discard==(v.zero,w,v.zero,v.zero),('DISCARD',top,d,discard)
            reset=s.block(['AX0']+['NIP']*10+['DROP','NIP'],initial)
            assert reset is None if top==v.num(1)else reset==(top,w,v.zero,v.zero),('RESET',top,d,reset)
            tests.append({'T_case':v.nodes[top],'D_case':v.nodes[d],'discard':'PASS','reset':'HALTS'if reset is None else 'PASS'})
    starts=0
    for top in tops:
        for d in ds:
            for h in[v.zero,v.num(1),v.var('arbitrary_H_ge_2',2)]:
                out=s.step('AX0',(top,w,d,h));assert out is not None and out[2:]==(v.zero,v.zero);starts+=1
    receipt={'status':'PASS_LITERAL_SOURCE_MACRO_CROSS_AUDIT','source_sha256':hashlib.sha256(raw).hexdigest(),'source_leaf_count':len(rows),'scope':'Actual command-dispatch AST; accelerations only transfer, Cantor pair/unpair, and proved asymmetric comparator. Symbolic current formulas/stack tails/positive parameters; unknown comparisons are errors. Not a TM runtime proof.','acceleration_checks':acceleration_receipt,'discard_reset_cases':tests,'initial_AX0_cases':starts,'source_node_visits':s.steps,'accelerated_calls':dict(s.accelerated),'command_outcomes':[{ 'op':op,'event':event,'count':n} for (op,event),n in s.outcomes.items()],'symbolic_expression_nodes':len(v.nodes)}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
