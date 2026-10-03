"""Deterministic integer/Boolean circuit -> natural-witness quartic SOS.
Every variable is natural. Signed registers have the unique disjoint pair
(v_plus,v_minus). Conditional branches exist only in witness evaluation.
"""
from collections import Counter

def const(v): return {():v} if v else {}
def var(i): return {(i,):1}
def add(a,b):
    c=dict(a)
    for m,v in b.items():
        c[m]=c.get(m,0)+v
        if not c[m]: del c[m]
    return c
def neg(a): return {m:-v for m,v in a.items()}
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    c={}
    for m,v in a.items():
        for k,w in b.items():
            q=tuple(sorted(m+k));c[q]=c.get(q,0)+v*w
    return {m:v for m,v in c.items() if v}
def ev(p,values):
    out=0
    for m,c in p.items():
        for i in m: c*=values[i]
        out+=c
    return out

def dump(p): return [[v,list(m)] for m,v in sorted(p.items())]

class Circuit:
    def __init__(self,inputs):
        self.names=list(inputs);self.input_count=len(inputs);self.rows=[];self.ops=[]
        self.counts=Counter();self.checks=[]
    def fresh(self,name):
        i=len(self.names);self.names.append(name+':'+str(i));return var(i)
    def row(self,p):
        if max(map(len,p),default=0)>2:raise ValueError('nonquadratic residual')
        self.rows.append(p)
    def integer(self,p):
        self.counts['A']+=1
        pos=self.fresh('plus');minus=self.fresh('minus')
        self.ops.append(('integer',p));self.row(sub(sub(pos,minus),p));self.row(mul(pos,minus))
        return sub(pos,minus)
    def add(self,x,y):return self.integer(add(x,y))
    def sub(self,x,y):return self.integer(sub(x,y))
    def scale(self,x,k):return self.integer(mul(x,const(k)))
    def select(self,b,x,y):return self.integer(add(x,mul(b,sub(y,x))))
    def boolean(self,p):
        self.counts['G']+=1;out=self.fresh('bool');self.ops.append(('boolean',p));self.row(sub(out,p));return out
    def AND(self,x,y):return self.boolean(mul(x,y))
    def OR(self,x,y):return self.boolean(sub(add(x,y),mul(x,y)))
    def NOT(self,x):return sub(const(1),x)
    def all(self,items):
        z=const(1)
        for x in items:z=self.AND(z,x)
        return z
    def any(self,items):
        z=const(0)
        for x in items:z=self.OR(z,x)
        return z
    def ge(self,x,y):
        self.counts['I']+=1;d=sub(x,y);b=self.fresh('ge');s=self.fresh('slack')
        self.ops.append(('ge',d));self.row(mul(b,sub(b,const(1))))
        self.row(add(sub(d,mul(sub(mul(const(2),b),const(1)),s)),sub(const(1),b)))
        return b
    def eq(self,x,y):
        # ge(d,0)-ge(d,1) is exactly its zero test, no free inverse.
        return self.boolean(sub(self.ge(x,y),self.ge(x,add(y,const(1)))))
    def le(self,x,y):return self.ge(y,x)
    def interval(self,x,lo,hi):return self.AND(self.ge(x,lo),self.le(x,hi))
    def check(self,p):self.counts['Q']+=1;self.row(p)
    def evaluate(self,inputs,check=True):
        if len(inputs)!=self.input_count or any(type(x)is not int or x<0 for x in inputs):raise ValueError('natural inputs')
        values=list(inputs)
        for op,p in self.ops:
            z=ev(p,values)
            if op=='integer':values.extend((max(z,0),max(-z,0)))
            elif op=='ge':values.extend((int(z>=0),z if z>=0 else -z-1))
            else:
                if z not in (0,1):raise ValueError(('non-Boolean deterministic result',z))
                values.append(z)
        if check:
            for i,p in enumerate(self.rows):
                if ev(p,values):raise ValueError(('nonzero residual',i,ev(p,values)))
        return values
    def score(self,values):return sum(ev(p,values)**2 for p in self.rows)
    def ledger(self):
        q=dict(self.counts);q.update(witnesses=len(self.names)-self.input_count,residuals=len(self.rows),
            residual_monomials=sum(map(len,self.rows)),ordered_sos_term_bound=sum(len(p)**2 for p in self.rows),
            max_residual_degree=max((len(m) for p in self.rows for m in p),default=0),
            max_coefficient_bits=max((abs(v).bit_length() for p in self.rows for v in p.values()),default=0),
            residual_coefficient_bits=sum(abs(v).bit_length() for p in self.rows for v in p.values()),
            residual_coefficient_l1=sum(abs(v) for p in self.rows for v in p.values()))
        if q['witnesses']!=2*q.get('A',0)+2*q.get('I',0)+q.get('G',0):raise RuntimeError('witness ledger')
        if q['residuals']!=2*q.get('A',0)+2*q.get('I',0)+q.get('G',0)+q.get('Q',0):raise RuntimeError('row ledger')
        return q
    def expanded(self):
        p={}
        for r in self.rows:
            for monomial,coefficient in mul(r,r).items():
                p[monomial]=p.get(monomial,0)+coefficient
                if not p[monomial]:del p[monomial]
        return p
