#!/usr/bin/env python3
"""Exact symbolic natural-number DAG for the runtime252 bootstrap investigation.

Arithmetic nodes retain their ordinary integer meaning; pairing/unpairing
cancel structurally. An undecided branch or unpair is reported, never guessed.
"""
import json,math,sys,time
from pathlib import Path
import macro252 as M

NODES=[];INTERN={};VAL={};BITS={}
def node(op,*args):
    key=op,*args
    if key not in INTERN:INTERN[key]=len(NODES);NODES.append(key)
    return N(INTERN[key])
def N0(x):return x if isinstance(x,N) else node('c',int(x))
class Unknown(Exception):pass
class N:
    def __init__(self,i):self.i=i
    def __add__(self,o):return add(self,N0(o))
    __radd__=__add__
    def __sub__(self,o):return sub(self,N0(o))
    def __rsub__(self,o):return sub(N0(o),self)
    def __mul__(self,o):return mul(self,N0(o))
    __rmul__=__mul__
    def __pow__(self,k):
        assert k==2;return mul(self,self)
    def __floordiv__(self,k):
        if literal(self) is not None:return N0(literal(self)//k)
        return node('div',self.i,k)
    def bit_length(self):return bits(self)
    def __repr__(self):return f'N{self.i}'
def literal(x):
    e=NODES[x.i];return e[1] if e[0]=='c' else None
def add(a,b):
    x,y=literal(a),literal(b)
    if x==0:return b
    if y==0:return a
    if x is not None and y is not None and max(abs(x).bit_length(),abs(y).bit_length())<4096:return N0(x+y)
    if a.i>b.i:a,b=b,a
    return node('+',a.i,b.i)
def sub(a,b):
    if a.i==b.i:return N0(0)
    x,y=literal(a),literal(b)
    if y==0:return a
    if x is not None and y is not None:return N0(x-y)
    e=NODES[a.i]
    if e[0]=='+':
        for j,k in ((e[1],e[2]),(e[2],e[1])):
            z=literal(N(j))
            if y is not None and z is not None and z>=y:return add(N(k),N0(z-y))
    if bits(a)<4096 and bits(b)<4096:return N0(evaluate(a)-evaluate(b))
    return node('-',a.i,b.i)
def mul(a,b):
    x,y=literal(a),literal(b)
    if x==0 or y==0:return N0(0)
    if x==1:return b
    if y==1:return a
    if x is not None and y is not None and abs(x).bit_length()+abs(y).bit_length()<4096:return N0(x*y)
    if a.i>b.i:a,b=b,a
    return node('*',a.i,b.i)
def pair(a,b):
    a,b=N0(a),N0(b)
    if literal(a)==0 and literal(b)==0:return N0(0)
    return node('P',a.i,b.i)
def unpair(a):
    a=N0(a);e=NODES[a.i]
    if e[0]=='P':return N(e[1]),N(e[2])
    if bits(a)<4096:
        n=evaluate(a);k=(math.isqrt(8*n+1)-1)//2;b=n-k*(k+1)//2;return N0(k-b),N0(b)
    raise Unknown(f'unpair of non-pair node {a.i}, bound {bits(a)} bits')
def bits(a):
    if a.i in BITS:return BITS[a.i]
    e=NODES[a.i];op=e[0]
    if op=='c':b=abs(e[1]).bit_length()
    elif op=='+':b=max(bits(N(e[1])),bits(N(e[2])))+1
    elif op=='-':b=max(bits(N(e[1])),bits(N(e[2])))+1
    elif op=='*':b=bits(N(e[1]))+bits(N(e[2]))
    elif op=='div':b=bits(N(e[1]))
    elif op=='P':b=2*max(bits(N(e[1])),bits(N(e[2])))+3
    else:raise ValueError(op)
    BITS[a.i]=b;return b
def evaluate(a):
    if a.i in VAL:return VAL[a.i]
    e=NODES[a.i];op=e[0]
    if op=='c':v=e[1]
    elif op in ('+','-','*'):
        x,y=evaluate(N(e[1])),evaluate(N(e[2]));v=x+y if op=='+' else x-y if op=='-' else x*y
    elif op=='div':v=evaluate(N(e[1]))//e[2]
    elif op=='P':
        x,y=evaluate(N(e[1])),evaluate(N(e[2]));v=(x+y)*(x+y+1)//2+y
    else:raise ValueError(op)
    VAL[a.i]=v;return v
def iszero(a):
    # Precondition at every control-flow call: a denotes a natural number.
    # This follows inductively from the nine natural registers: transfer,
    # pair and unpair preserve naturals; an atomic subtraction is applied
    # only after the positive branch has been proved. Statistics may use
    # signed intermediate expressions, but are never branch operands.
    a=N0(a);e=NODES[a.i];op=e[0]
    if op=='c':return e[1]==0
    if op in ('+','P'):return iszero(N(e[1])) and iszero(N(e[2]))
    if op=='*':return iszero(N(e[1])) or iszero(N(e[2]))
    if bits(a)<4096:return evaluate(a)==0
    raise Unknown(f'zero test of {a.i}, op {op}, bound {bits(a)} bits')
def small(a):
    a=N0(a);return evaluate(a) if bits(a)<128 else {'node':a.i,'bit_bound':bits(a)}
def ids(R):return [N0(r).i for r in R]

def run(initial,limit=100000):
    M.P=pair;M.unP=unpair
    p=initial['p'];g=initial['gap'];regs=list(map(N0,initial['regs']));ns=M.m.executor()
    cache={};macrocache={};record=[];counts={};decs=N0(0);steps=N0(0)
    relative_head=0;normal_overflows=0
    def check(case):
        cp,br=case;op,r=M.OPS[cp];key=cp,op,r,br,g
        if key not in cache:cache[key]=M.m.case(ns,*key,exact_gap=True)
        return cache[key]
    def done(reason,detail=None):
        return {'status':reason,'detail':detail,'iteration':i,'path':p,'gap':g,
                'registers':ids(regs),'register_display':[small(r) for r in regs],
                'positive_decrements':decs.i,'rm_steps':steps.i,'nodes':NODES,'record':record,
                'counts':counts,'checked_local_cases':len(cache),'initial':initial,
                'relative_head':relative_head,'normal_overflows':normal_overflows}
    for i in range(limit):
        p=M.canonical(p);op,r=M.OPS[p]
        try:
            if p in M.MACROS:
                mac=M.MACROS[p]
                if p not in macrocache:macrocache[p]=[(c,check(c)) for c in mac['cases'] if not check(c)[0]]
                bad=macrocache[p]
                if bad and mac['kind']!='transfer' and p in M.TRANSFER:
                    mac=M.TRANSFER[p];bad=[(c,check(c)) for c in mac['cases'] if not check(c)[0]]
                if not bad:
                    old=regs;regs=list(map(N0,M.apply_macro(mac,regs)))
                    dd=M.macro_decrements(mac,old);ss=M.macro_rm_steps(mac,old)
                    decs+=dd;steps+=ss;counts[mac['kind']]=counts.get(mac['kind'],0)+1
                    record.append({'kind':mac['kind'],'entry':p,'exit':mac['exit'],'before':ids(old),'after':ids(regs),'decrements':N0(dd).i,'steps':N0(ss).i})
                    p=mac['exit'];continue
                if mac['kind']=='transfer' and not iszero(regs[mac['source']]) and all(c==(p,'z') for c,res in bad):
                    old=regs;regs=list(map(N0,M.apply_macro(mac,regs)));dd=old[mac['source']];ss=mac['cycle_length']*dd
                    decs+=dd;steps+=ss;counts['positive_transfer']=counts.get('positive_transfer',0)+1
                    record.append({'kind':'positive_transfer','entry':p,'exit':p,'before':ids(old),'after':ids(regs),'decrements':dd.i,'steps':ss.i});continue
            br=('z' if iszero(regs[r]) else 'p') if op=='CD' else '-'
            good,rawsucc,res=check((p,br))
            if not good:return done('failed_local_contract',res)
            if op=='CH':return done('halt')
            before=ids(regs)
            if op=='CI':regs[r]+=1
            if op=='CD' and br=='p':regs[r]-=1;decs+=1
            steps+=1;counts['atomic']=counts.get('atomic',0)+1
            record.append({'kind':'atomic','entry':p,'op':op,'r':r,'branch':br,'before':before,'after':ids(regs)})
            if rawsucc is None:
                g+=1;p='';relative_head-=1;normal_overflows+=1
            else:p=rawsucc
            record[-1].update(successor_path=p,gap_after=g,relative_head_after=relative_head)
            if p in ('','0','00','000'):return done('root')
        except Unknown as ex:return done('undecided_symbolic_arithmetic',str(ex))
        if i and i%1000==0:print('lazy',i,'nodes',len(NODES),'maxbits',max(bits(r) for r in regs),'p',p,flush=True)
    return done('fuel')

if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    initial=json.loads((root/'certificates/recovered36.json').read_text())['frame']
    out=run(initial);(root/'certificates/lazy36.json').write_text(json.dumps(out,indent=2)+'\n')
    print({k:v for k,v in out.items() if k not in ('nodes','record','initial','registers')})
