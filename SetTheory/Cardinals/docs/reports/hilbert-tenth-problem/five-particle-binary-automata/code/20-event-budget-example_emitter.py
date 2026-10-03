"""Coefficient-explicit quartic: a full CA step on arbitrary two-particle inputs.

This is the mass-two specialization of the fixed T+K event scheduler in PROOF.md,
not the arbitrary-mass exporter. Standard library only; no source files changed.
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

def plus(a,b):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+c
        if not out[m]:del out[m]
    return out

def scale(a,k):return {m:k*c for m,c in a.items() if k*c}
def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}
def const(c):return {():c} if c else {}
def var(i):return {(i,):1}
def sub(a,b):return plus(a,scale(b,-1))

def evaluate(p,values):
    total=0
    for monomial,coefficient in p.items():
        term=coefficient
        for index in monomial:term*=values[index]
        total+=term
    return total

class Circuit:
    def __init__(self,inputs):
        self.names=[name for name,value in inputs]
        self.values=[value for name,value in inputs]
        self.input_count=len(inputs);self.rows=[]
        self.counts=dict(A=0,I=0,D=0,G=0,Q=0)
        self.events=[]
    def fresh(self,name,value):
        if type(value) is not int or value<0:raise ValueError((name,value))
        i=len(self.values);self.names.append(name+':'+str(i));self.values.append(value)
        return var(i)
    def value(self,x):return evaluate(x,self.values)
    def row(self,p):self.rows.append(p)
    def integer(self,p,name='a'):
        self.counts['A']+=1;v=self.value(p)
        pos=self.fresh(name+'+',max(v,0));neg=self.fresh(name+'-',max(-v,0))
        self.row(sub(sub(pos,neg),p));self.row(mul(pos,neg))
        return sub(pos,neg)
    def add(self,x,y):return self.integer(plus(x,y))
    def subtract(self,x,y):return self.integer(sub(x,y))
    def multiply(self,x,y):return self.integer(mul(x,y))
    def select(self,b,x,y):
        # x if b=0, y if b=1
        return self.integer(plus(x,mul(b,sub(y,x))),'select')
    def ge(self,x,y):
        # Truth bit x >= y; signed affine inputs are allowed.
        self.counts['I']+=1;v=self.value(sub(x,y));bv=int(v>=0)
        b=self.fresh('ge',bv);d=self.fresh('slack',v if bv else -v-1)
        self.row(mul(b,sub(b,const(1))))
        self.row(plus(sub(sub(x,y),mul(sub(scale(b,2),const(1)),d)),sub(const(1),b)))
        return b
    def eq(self,x,y):
        # No output variable: Boolean affine alias.
        return self.boolean(sub(self.ge(x,y),self.ge(x,self.add(y,const(1)))),'eq')
    def boolean(self,p,name):
        self.counts['G']+=1;v=self.value(p)
        if v not in (0,1):raise ValueError(('Not Boolean',name,v))
        out=self.fresh(name,v);self.row(sub(out,p));return out
    def AND(self,x,y):return self.boolean(mul(x,y),'and')
    def OR(self,x,y):return self.boolean(sub(plus(x,y),mul(x,y)),'or')
    def NOT(self,x):return self.boolean(sub(const(1),x),'not')
    def check(self,p):self.counts['Q']+=1;self.row(p)
    def score(self,values=None):
        values=self.values if values is None else values
        return sum(evaluate(p,values)**2 for p in self.rows)
    def expanded(self):
        out={}
        for p in self.rows:out=plus(out,mul(p,p))
        return out
    def ledger(self):
        lengths=[len(p) for p in self.rows]
        return dict(self.counts,witnesses=len(self.values)-self.input_count,
            residuals=len(self.rows),residual_monomials=sum(lengths),
            ordered_sos_term_bound=sum(x*x for x in lengths),
            max_residual_degree=max((len(m) for p in self.rows for m in p),default=0),
            max_witness_bits=max((v.bit_length() for v in self.values[self.input_count:]),default=0),
            max_coefficient_bits=max((abs(c).bit_length() for p in self.rows for c in p.values()),default=0))


def build(h=-10,gap=5,T=1,K=2,target=None):
    if type(h) is not int or type(gap) is not int or gap<1:raise ValueError('input')
    if any(type(v) is not int or v<0 for v in (T,K)):raise ValueError('budgets')
    if target is not None:
        if type(target) not in (tuple,list) or len(target)!=2 or any(type(v) is not int for v in target) or target[0]>=target[1]:
            raise ValueError('target must be two strictly increasing exact integers')
    c=Circuit([('h+',max(h,0)),('h-',max(-h,0)),('gap_minus_one',gap-1)])
    c.check(mul(var(0),var(1)))
    x0=c.subtract(var(0),var(1));d=c.add(var(2),const(1));x1=c.add(x0,d)
    t,cur=const(0),const(0)
    # Fixed source q->halt, side=+1, increment, J=0: D=8, F=95.
    # The only factors that can affect mass two are these four free factors.
    factors=((0,5,6,1,-1),(22,7,8,-1,1),(47,5,6,0,0),(70,7,8,0,0))
    snapshots=[]
    for round_no in range(T+K):
        running=c.ge(const(T-1),t)
        gap_wire=c.subtract(x1,x0)
        best=const(95);by0=x0;by1=x1
        chosen=-1
        for i,a,b,sa,sb in factors:
            qa=c.eq(gap_wire,const(a));qb=c.eq(gap_wire,const(b))
            active=c.OR(qa,qb)
            shift=c.add(c.multiply(qa,const(sa)),c.multiply(qb,const(sb)))
            y0=c.add(x0,shift)
            newgap=c.add(gap_wire,c.add(c.multiply(qa,const(b-a)),c.multiply(qb,const(a-b))))
            y1=c.add(y0,newgap)
            eligible=c.AND(running,c.AND(active,c.ge(const(i),cur)))
            earlier=c.ge(best,const(i+1))
            take=c.AND(eligible,earlier)
            if c.value(take):chosen=i
            best=c.select(take,best,const(i))
            by0=c.select(take,by0,y0);by1=c.select(take,by1,y1)
        changed=c.ge(const(94),best)
        complete=c.AND(running,c.NOT(changed))
        t=c.add(t,complete)
        nextcursor=c.add(best,const(1))
        cur=c.select(changed,const(0),nextcursor)
        x0=c.select(changed,x0,by0);x1=c.select(changed,x1,by1)
        snapshots.append(dict(round=round_no,changed=bool(c.value(changed)),
             chosen=chosen if c.value(changed) else None,completed=bool(c.value(complete)),
             time=c.value(t),cursor=c.value(cur),support=[c.value(x0),c.value(x1)]))
    c.check(sub(t,const(T)))
    if target is not None:
        c.check(sub(x0,const(target[0])));c.check(sub(x1,const(target[1])))
    return c,snapshots,[c.value(x0),c.value(x1)]


def dump_poly(p):return [[coefficient,list(monomial)] for monomial,coefficient in sorted(p.items())]
def main():
    c,rounds,out=build(target=(-9,-4))
    expanded=c.expanded()
    ledger=c.ledger()
    if ledger['witnesses']!=2*ledger['A']+2*ledger['I']+4*ledger['D']+ledger['G']:raise RuntimeError('V ledger')
    if ledger['residuals']!=2*ledger['A']+2*ledger['I']+3*ledger['D']+ledger['G']+ledger['Q']:raise RuntimeError('R ledger')
    if c.score()!=0:raise RuntimeError('Sample is not a zero')
    payload=dict(description='Full mass-two CA, fixed source and T+K scheduler; all residual coefficients explicit',
        source=dict(schema='reversible-two-counter-v1',controls=['q','halt'],start='q',halt='halt',class_cut=0,
             branches=[dict(name='e',source='q',target='halt',side=1,delta=1,guard=dict(op='true'))]),
        T=1,K=2,target=[-9,-4],input_count=c.input_count,variable_names=c.names,input_values=c.values[:c.input_count],
        ledger=ledger,rounds=rounds,output=out,residuals=[dump_poly(p) for p in c.rows],
        expanded_quartic=dump_poly(expanded))
    (HERE/'example-polynomial.json').write_text(json.dumps(payload,separators=(',',':'))+'\n')
    (HERE/'example-witness.json').write_text(json.dumps(c.values[c.input_count:])+'\n')
    receipt=dict(status='passed',ledger=ledger,expanded_monomials=len(expanded),rounds=rounds)
    (HERE/'example-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
