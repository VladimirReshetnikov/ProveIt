#!/usr/bin/env python3
"""Independent checks of the asymmetric comparator and counter-salt compiler.

Standard library only; no repository paths or external packages are required.
The source interpreter uses open-tree break/continue semantics directly.
The block checker is symbolic: formula constructors and arbitrary stack tails
are retained, rather than assigning arbitrary small integer IDs to formulas.
It checks the proof-block compositions from the stated modified abstract
command semantics.  It does not prove the binary TM runtime or replace the
unbounded source/calculus arguments in the accompanying TeX section.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from itertools import product
from math import isqrt
from pathlib import Path

D = lambda i: ('CD', i)
I = lambda i: ('CI', i)
C = lambda i: ('CC', i)
B = lambda i: ('CB', i)
EA = ((D(5), ((D(6), C(2)), (I(6), (D(5), C(1))))), (D(6), B(1)))
L = ((D(5), ((D(6), C(2)), B(1))), D(6))
EW = (L, B(1))
CLEAR = lambda i: (D(i), C(1))
TRANSFER = lambda a,b: (D(a), (I(b), C(2)))
COPY3 = (D(3), (I(7), (I(6), C(3))))

def seq(parts):
    assert parts
    if len(parts)==1:return parts[0]
    return (parts[0],seq(parts[1:]))

def source_run(tree, registers):
    """Direct compositional source semantics, separate from any CFG resolver."""
    r=list(registers);steps=0
    def go(node):
        nonlocal steps
        if isinstance(node[0],str):
            steps+=1
            if steps>100000:raise RuntimeError('unexpected nontermination')
            op,k=node
            if op=='CI':r[k]+=1;return ('N',0)
            if op=='CD':
                if r[k]:r[k]-=1;return ('N',0)
                return ('B',1)
            if op=='CB':return ('B',k)
            if op=='CC':return ('C',k)
            raise ValueError(op)
        while True:
            kind,k=go(node[0])
            if kind=='B':return ('N',0) if k==1 else ('B',k-1)
            if kind!='N':return (kind,k)
            kind,k=go(node[1])
            if kind=='C':
                if k==1:continue
                return ('C',k-1)
            return (kind,k)
    outcome=go(tree)
    return outcome,r,steps

def pair(a,b):return (a+b)*(a+b+1)//2+b
def unpair(n):
    z=(isqrt(8*n+1)-1)//2;b=n-z*(z+1)//2
    return z-b,b

def source_checks():
    checked=0
    for a,b in product(range(17),repeat=2):
        initial=[11,13,17,19,23,a,b,29,31]
        out,r,_=source_run(EA,initial)
        assert out==(('N',0) if a==b else ('B',1))
        assert (r[5],r[6])==(0,max(b-a-1,0))
        assert all(r[i]==initial[i] for i in range(9) if i not in (5,6))
        checked+=1
    gate=seq([COPY3,(EA,CLEAR(1)),CLEAR(6),TRANSFER(7,6),TRANSFER(4,5),(EA,CLEAR(1))])
    wrong_gate=seq([COPY3,(EA,CLEAR(1)),TRANSFER(7,6),TRANSFER(4,5),(EA,CLEAR(1))])
    weak_gate=seq([COPY3,(EW,CLEAR(1)),TRANSFER(7,6),TRANSFER(4,5),(EW,CLEAR(1))])
    gates=0
    for a,b,c in product(range(9),repeat=3):
        initial=[11,97,17,c,a,b,0,0,31]
        out,r,_=source_run(gate,initial)
        assert out==('N',0)
        assert r[1]==(0 if c==a or c==b else 97)
        assert (r[3],r[4],r[5],r[6],r[7])==(0,0,0,max(c-a-1,0),0)
        assert (r[0],r[2],r[8])==(11,17,31)
        gates+=1
    bad=[11,97,17,2,2,0,0,0,31]
    out,bad_result,_=source_run(wrong_gate,bad)
    assert out==('N',0) and bad_result[1]==97 and bad_result[5:7]==[0,0]
    forged=[11,97,17,1,3,0,0,0,31]
    out,forged_result,_=source_run(weak_gate,forged)
    assert out==('N',0) and forged_result[5:7]==[1,0]
    for h in range(17):
        initial=[0]*9;initial[5]=h;initial[6]=1
        out,r,_=source_run(EA,initial)
        assert r[5:7]==[0,0]
        assert out==(('N',0) if h==1 else ('B',1))
    # Use the exact eleven-leaf reader from the source, without factoring its
    # control edges through the mathematical unpair function.
    reader=(D(8),(I(7),(((D(6),B(1)),(D(7),(I(6),C(2)))),C(3))))
    reader=seq([reader,TRANSFER(7,8)])
    readers=0
    for n,d in product(range(33),repeat=2):
        initial=[0]*9;initial[8]=n;initial[6]=d
        out,r,_=source_run(reader,initial)
        assert out==('N',0)
        assert (r[6],r[8])==unpair(n+d*(d+1)//2),(n,d,r)
        assert r[8]<=n and r[7]==0
        readers+=1
    reload=seq([(D(0),(I(8),(I(6),C(3)))),(I(0),(D(6),C(2)))])
    reloads=0
    for n,d in product(range(17),repeat=2):
        initial=[0]*9;initial[0]=n;initial[6]=d
        out,r,_=source_run(reload,initial)
        assert out==('N',0) and (r[0],r[6],r[8])==(n+d+1,0,n)
        reloads+=1
    return dict(comparator_cases=checked,repaired_gate_cases=gates,nip_cases=17,
                dirty_reader_cases=readers,dirty_reload_cases=reloads,
                wrong_gate_example=dict(a=2,b=0,c=2,input_top=97,output_top=bad_result[1],
                                        final_scratch=bad_result[5:7]),
                weak_cache_forgery=dict(a=3,b=0,c=1,final_cache=forged_result[5],
                                       final_scratch6=forged_result[6]))

@dataclass(frozen=True)
class Term:
    op:str
    args:tuple

def sym(name,not_one=False):return Term('symbol',(name,not_one))
def add(a,b):
    if a==0:return b
    if b==0:return a
    if isinstance(a,int) and isinstance(b,int):return a+b
    return Term('add',(a,b))
def residual(a,b):
    """The natural number max(a-b-1,0)."""
    if a==0 or a==b:return 0
    if isinstance(a,int) and isinstance(b,int):return max(a-b-1,0)
    return Term('residual',(a,b))
def code(tag,a,b):
    if tag==0 and a==0 and b==0:return 0
    return Term('code',(tag,a,b))
IMP=lambda a,b:code(0,a,b)
REL=lambda a,b:code(1,a,b)
ALL=lambda a,b:code(2,a,b)
EQU=lambda a,b:code(3,a,b)
NEG=lambda a:IMP(a,1)
EX=lambda a,b:NEG(ALL(a,NEG(b)))

def lower(a):
    if isinstance(a,int):return a
    if a.op=='add':return lower(a.args[0])+lower(a.args[1])
    if a.op=='code':
        tag,x,y=a.args
        return tag+(4 if lower(x)>0 or lower(y)>0 else 0)
    return 0

def nonone(a):
    if isinstance(a,int):return a!=1
    if a.op=='symbol':return a.args[1]
    if a.op=='code':
        tag,x,y=a.args
        return tag!=1 or lower(x)>0 or lower(y)>0
    if a.op=='gate':return True  # exactly 0 or an implication code
    return lower(a)>1

def eqknown(a,b):
    if a==b:return True
    if isinstance(a,int) and isinstance(b,int):return False
    if a==0 and lower(b)>0 or b==0 and lower(a)>0:return False
    if a==1 and nonone(b) or b==1 and nonone(a):return False
    return None

@dataclass(frozen=True)
class Cons:
    head:object
    tail:object

def emit(a,b,c,u):
    r=REL(b,c)
    sub=ALL(c,IMP(REL(c,a),REL(c,b)))
    # Use the literal native expression: Q_b(c -> not Q_b(c -> not R(b,c))).
    w=ALL(b,IMP(c,NEG(ALL(b,IMP(c,NEG(r))))))
    uu=ALL(a,IMP(sub,w))
    h=ALL(b,IMP(r,NEG(ALL(a,IMP(c,NEG(uu))))))
    v=IMP(REL(a,b),ALL(c,REL(a,b)))
    bundle=NEG(IMP(v,ALL(c,IMP(h,NEG(w)))))
    rows=[
      EX(a,EQU(a,b)),
      IMP(ALL(a,IMP(b,c)),IMP(ALL(a,b),ALL(a,c))),
      IMP(EQU(a,b),IMP(REL(c,a),REL(c,b))),
      IMP(ALL(a,ALL(b,c)),ALL(b,ALL(a,c))),
      IMP(EQU(c,a),IMP(REL(c,b),REL(a,b))),
      IMP(EX(a,ALL(a,c)),c),
      IMP(EQU(c,a),IMP(EQU(c,b),ALL(REL(a,b),EQU(a,b)))),
      IMP(IMP(IMP(c,u),a),IMP(IMP(a,c),IMP(b,c))),
    ]
    return rows,bundle

def gate(a,b,c,bundle):
    e1=eqknown(c,a);e2=eqknown(c,b)
    if e1 is True or e2 is True:return 0
    if e1 is False and e2 is False:return bundle
    return Term('gate',(a,b,c,bundle))

MP=lambda x:('MP',x)
AX=lambda c,x=0,y=0,u=0:('AX',c,x,y,u)
DROP=('DROP',)
NIP=('NIP',)
BUILD=lambda x:('BUILD',x)

def step(command,state):
    t,w,d,h=state;op=command[0]
    if op=='BUILD':
        # A premise of the GEN/MP induction, not an actual source command.
        return (command[1],w,0,0)
    if op=='DROP':return (h,Cons(t,w),d,h)
    if op=='NIP':
        if h==1:return None
        if not nonone(h):raise AssertionError(('unresolved falsum test',h))
        if not isinstance(w,Cons):raise AssertionError('popped an arbitrary underlying stack')
        return (t,w.tail,d,w.head)
    if op=='MP':
        a=add(d,command[1]);wanted=IMP(t,a);same=eqknown(wanted,h)
        if same is None:raise AssertionError(('unresolved MP comparison',wanted,h))
        if same:return (a,Cons(0,w),a,0)
        return (0,w,add(a,residual(wanted,h)),0)
    if op=='AX':
        _,c,x,y,u=command;a=add(d,x);b=add(h,y)
        rows,bundle=emit(a,b,c,u)
        w=Cons(t,w);w=Cons(ALL(a,h),w)
        for row in reversed(rows):w=Cons(row,w)
        return (gate(a,b,c,bundle),w,residual(c,a),0)
    raise ValueError(command)

def execute(commands,state):
    for command in commands:
        state=step(command,state)
        if state is None:return None
    return state

DISCARD=[MP(1),AX(0)]+[NIP]*10
RESET=[AX(0)]+[NIP]*10+[DROP,NIP]

def check_blocks():
    W=Term('arbitrary_stack',('W',))
    T=sym('T',True);D0=sym('D');H=sym('H')
    a,b,c,u=(sym(x) for x in 'abcu')
    for t in (0,1,T):
        for d in (0,1,17,D0):
            assert execute(DISCARD,(t,W,d,0))==(0,W,0,0)
            result=execute(RESET,(t,W,d,0))
            assert result is None if t==1 else result==(t,W,0,0)
    rows,bundle=emit(a,b,c,u)
    leaf_results=[]
    for j,target in enumerate(rows,1):
        block=DISCARD+[AX(c,a,b,u)]+[NIP]*j+[DROP]+[NIP]*(11-j)+RESET
        result=execute(block,(T,W,D0,0))
        assert result==(target,W,0,0),(j,result)
        leaf_results.append(dict(row=j,commands=len(block)))
    bundle_block=DISCARD+[AX(c,a,b,u)]+[NIP]*10+RESET
    target=gate(a,b,c,bundle)
    assert execute(bundle_block,(T,W,D0,0))==(target,W,0,0)
    i=sym('i')
    X=sym('X',True)
    gen_cases=0
    for x in (0,1,X):
        gen=[BUILD(x),DROP,NIP,AX(i,i)]+[NIP]*9+[DROP,NIP,NIP]
        assert execute(gen,(T,W,0,0))==(ALL(i,x),W,0,0)
        gen_cases+=1
    mp_cases=0
    for aa,bb in product((0,1,sym('A',True)),(0,1,sym('B',True))):
        prem=IMP(aa,bb)
        block=[BUILD(aa),DROP,BUILD(prem),NIP,DROP,NIP,MP(bb),AX(bb)]+[NIP]*10+[DROP,NIP,NIP]
        result=execute(block,(T,W,0,0))
        if aa==1 or bb==1:assert result is None
        else:assert result==(bb,W,0,0),(aa,bb,result)
        mp_cases+=1
    start=execute([AX(0)],(T,W,D0,H))
    assert start is not None and start[2:]==(0,0)
    assert execute([AX(0),BUILD(1),DROP,NIP,NIP],(T,W,D0,H)) is None
    return dict(status='SYMBOLIC_BLOCK_COMPOSITIONS_PASS',
                discard_cases=12,reset_cases=12,axiom_rows=leaf_results,
                bundle_commands=len(bundle_block),generalization_cases=gen_cases,
                modus_ponens_cases=mp_cases,arbitrary_state_start=True,final_falsum_test=True,
                semantics='Exact symbolic stack/formula expressions under the stated counter-salted abstract commands; unknown comparisons fail the checker.',
                induction_premise='BUILD(X) stands for a previously established block with output(X,w,0,0), with early halting allowed.')

def main():
    if not __debug__:
        raise SystemExit('Run with assertions enabled; omit -O and -OO.')
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path);args=parser.parse_args()
    result=dict(status='PASS',source=source_checks(),blocks=check_blocks(),
                limits='Finite source probes and symbolic block compositions do not certify the binary TM runtime; the all-natural source and logical arguments are supplied separately.')
    raw=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.out:args.out.write_text(raw)
    print(raw,end='')

if __name__=='__main__':main()
