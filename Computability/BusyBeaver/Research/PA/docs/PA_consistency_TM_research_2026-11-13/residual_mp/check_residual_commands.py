#!/usr/bin/env python3
"""Finite regression of the parametric command-interface proof.

AX heads are three explicit safe abstract row models, NOT the native PA196
formulas. Every assertion uses only the interface hypotheses displayed in
residual_command_proof.tex. This is not a machine or proof-assistant checker.
"""
from dataclasses import dataclass
from itertools import product
from math import isqrt
from pathlib import Path
import json,hashlib,sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Verification requires assertions; run Python without -O or -OO.')

def pair(a,b):return (a+b)*(a+b+1)//2+b
def decode(n):
    k=(isqrt(8*n+1)-1)//2;b=n-k*(k+1)//2
    return k-b,b
def imp(a,b):return 4*pair(a,b)
def uni(a,b):return 4*pair(b,a)+2
@dataclass(frozen=True)
class Cell:
    head:int
    tail:object
def push(a,w):return 0 if a==0 and w==0 else Cell(a,w)
def pop(w):return (w.head,w.tail)if isinstance(w,Cell)else decode(w)
def putall(xs,w):
    for x in reversed(xs):w=push(x,w)
    return w

def rows(d,h,c,u,v,model):
    if model==0:rs=[4*(i+1)for i in range(7)]
    elif model==1:rs=[0]*7
    else:rs=[4*((d+h+c+u+v+i)%5)for i in range(7)]
    return rs+[uni(u,v)]
def gate(h,d,c,model):return 0 if c in (h,d)else 4*model
S=('S',);M=('M',)
def A(c,x,y):return ('A',c,x,y)
A0=A(0,0,0)
P=[A0]+[S]*8+[M]
R=[A0]+[S]*10
Z=(P+R)*2
def setter(v):return P+[A(v+1,0,v+1)]+[S]*10

def step(cmd,st,model):
    t,w,d,h=st
    if cmd==S:
        if t+h==1:return None
        x,tail=pop(w);return(h,tail,d,x)
    if cmd==M:return(d,push(0,w),d,0)if imp(t,d)==h else(0,w,d,0)
    if cmd[0]=='HOLE':return(cmd[1],w,cmd[2],0)
    _,c,x,y=cmd;dd=d+x;hh=h+y
    return(gate(hh,dd,c,model),putall(rows(dd,hh,c,d,h,model)+[t],w),max(c-dd-1,0),0)
def run(word,st,model):
    for cmd in word:
        st=step(cmd,st,model)
        if st is None:return None
    return st

def check():
    counts={}
    n=0
    for model,t,w,d,h in product(range(3),range(5),range(7),range(5),range(5)):
        st=(t,w,d,h)
        assert run(P,st,model)==(0,push(t,w),0,0)
        x,tail=pop(w);assert run(R,st,model)==(t,tail,0,x)
        assert run(Z,st,model)==(0,w,0,0)
        for v in range(5):assert run(setter(v),st,model)==(0,w,v,t)
        n+=8
    counts['push_pop_reset_setter']=n
    n=0
    for model,w,d,h,c,x,y in product(range(3),range(4),range(3),range(3),range(3),range(3),range(3)):
        r=rows(d+x,h+y,c,d,h,model)
        st=step(A(c,x,y),(0,w,d,h),model)
        for j in range(1,9):
            z=run([S]*(j+1)+R*(8-j),st,model)
            assert z is not None and z[0]==r[j-1] and z[1]==w and z[3]==0
            n+=1
        z=run(R*9,st,model)
        assert z[0]==gate(h+y,d+x,c,model) and z[1:]==(w,0,0)
        n+=1
    counts['selection']=n
    n=0
    for model,t,w,d,h,B,i in product(range(3),range(2),range(3),range(2),range(2),range(5),range(3)):
        code=[('HOLE',B,7)]+setter(i)+[A0]+[S]*9
        assert run(code,(t,w,d,h),model)==(uni(i,B),w,0,0);n+=1
    counts['generalization']=n
    n=0
    for model,t,w,d,h,a,b in product(range(3),range(2),range(4),range(2),range(2),range(6),range(6)):
        code=[('HOLE',imp(a,b),7)]+P+[('HOLE',a,9)]+setter(b)+[S,M]+R
        got=run(code,(t,w,d,h),model)
        assert got is None if a==1 else got==(b,w,0,0)
        n+=1
    counts['modus_ponens']=n
    n=0
    def enc(word):
        out=0
        for cmd in reversed(word):
            if cmd==S:tag=0
            elif cmd==M:tag=1
            else:
                _,c,x,y=cmd;tag=c+2;out=pair(y,pair(x,out))
            out=1+pair(tag,out)
        return out
    def dec(word):
        out=[]
        while word:
            old=word;tag,word=decode(word-1)
            if tag==0:out.append(S)
            elif tag==1:out.append(M)
            else:
                y,word=decode(word);x,word=decode(word);out.append(A(tag-2,x,y))
            assert word<old
        return out
    # Short words avoid astronomical nested Cantor integers in this finite test.
    alphabet=[S,M,A(0,0,0),A(1,2,3)]
    for length in range(6):
        for ww in product(alphabet,repeat=length):
            assert dec(enc(ww))==list(ww);n+=1
    counts['wire_roundtrip']=n
    n=0
    def raw_first(raw):
        tag,tail=decode(raw)
        if tag==0:return S,tail
        if tag==1:return M,tail
        y,tail=decode(tail);x,tail=decode(tail)
        return A(tag-2,x,y),tail
    for length in range(1,6):
        for ww in product(alphabet,repeat=length):
            continuation=enc(ww)
            # Fresh fetch decodes N; positive continuation decodes L-1.
            fresh=continuation-1
            c1,l1=raw_first(fresh)
            c2,l2=raw_first(continuation-1)
            assert c1==c2==ww[0] and l1==l2==enc(ww[1:])
            n+=1
    counts['fresh_continuation_first_step']=n
    out={'status':'PASS_PARAMETRIC_INTERFACE_REGRESSION','counts':counts,'total':sum(counts.values()),
         'models':3,'native_AX_evaluated':False,'HOLEs':'premise compiler interface assumptions',
         'scope':'Finite regression of universal algebra in residual_command_proof.tex; not a literal machine check or PA proof.'}
    p=Path(__file__).with_name('residual-command-check.json');p.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':check()
