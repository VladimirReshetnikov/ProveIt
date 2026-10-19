#!/usr/bin/env python3
"""Replay generic proof-block stack identities for m helper rows.

Pairs, formulas and unknown old stacks are represented as symbolic terms.
This checks stack identities and off-by-one counts; the accompanying notes
give the quantified proof and specify the required non-falsity hypotheses.
It is not a new numerical-code or proof-assistant equivalence theorem.
"""
import json
from pathlib import Path

def pair(a,b):return 0 if a==b==0 else ('pair',a,b)
def unpair(x):
    if x==0:return 0,0
    assert isinstance(x,tuple) and x[0]=='pair',('unknown pair',x)
    return x[1],x[2]
def imp(a,b):return 0 if a==b==0 else ('imp',a,b)
def allf(a,b):return ('all',a,b)
def plus(a,b):
    if a==0:return b
    if b==0:return a
    if isinstance(a,int) and isinstance(b,int):return a+b
    return ('plus',a,b)
def push(xs,s):
    for x in reversed(xs):s=pair(x,s)
    return s
def rows(m,a,b,c):return [('row',j,a,b,c) for j in range(1,m+1)]
def gate(a,b,c):return 0 if c==a or c==b else ('bundle',a,b,c)

def step(cmd,w,m):
    t,s,d,h=w
    op,*args=cmd
    if op=='BUILD':return args[0],s,0,0
    if op=='MP':
        a=plus(d,args[0])
        return (a,pair(0,s),a,0) if imp(t,a)==h else (0,s,a,0)
    if op=='DROP':return h,pair(t,s),plus(d,args[0]),h
    if op=='NIP':
        if h==1:return None
        top,tail=unpair(s)
        return t,tail,plus(d,args[0]),top
    assert op=='AX'
    c,x,y=args
    a,b=plus(d,x),plus(h,y)
    return gate(a,b,c),push(rows(m,a,b,c)+[allf(a,h),t],s),0,0

def run(cmds,w,m):
    for cmd in cmds:
        w=step(cmd,w,m)
        if w is None:return None
    return w
def nips(n):return [('NIP',0)]*n
def discard(m):return [('MP',1),('AX',1,0,0)]+nips(m+2)
def leaf(m,j,a,b,c):
    return discard(m)+[('AX',c,a,b)]+nips(j)+[('DROP',0)]+nips(m+3-j)
def bundle_leaf(m,a,b,c):return discard(m)+[('AX',c,a,b)]+nips(m+2)
def gen_block(m,i,p):
    return p+[('DROP',0),('NIP',0),('AX',i,i,0)]+nips(m+1)+[('DROP',0),('NIP',0),('NIP',0)]
def mp_block(m,a,b,pa,pab):
    return pa+[('DROP',0)]+pab+[('NIP',0),('DROP',0),('NIP',0),('MP',b),('AX',b,0,0)]+nips(m+2)+[('DROP',0),('NIP',0),('NIP',0)]

def main():
    cases=0
    for m in (1,2,8,10,12):
      for t in (0,1,'T'):
       for s in (0,'S',pair(1,'S')):
        w=t,s,0,0
        assert run(discard(m),w,m)==(0,s,0,0);cases+=1
        for j in range(1,m+1):
            assert run(leaf(m,j,'a','b','c'),w,m)==(('row',j,'a','b','c'),s,0,0);cases+=1
        assert run(bundle_leaf(m,'a','b','c'),w,m)==(('bundle','a','b','c'),s,0,0);cases+=1
        for a in (0,1,'A'):
            assert run(gen_block(m,'i',[('BUILD',a)]),w,m)==(allf('i',a),s,0,0);cases+=1
            for b in (0,1,'B'):
                actual=run(mp_block(m,a,b,[('BUILD',a)],[('BUILD',imp(a,b))]),w,m)
                expected=None if 1 in (a,b) else (b,s,0,0)
                assert actual==expected,(m,a,b,actual,expected);cases+=1
        # A reset AX needs no ignored fourth field. Its first numeric field
        # can carry arbitrary padding before a compiled contradiction block.
        for d,h in (('D','H'),(0,0),(1,1)):
            p=[('AX',0,'padding',0),('BUILD',1),('DROP',0),('NIP',0),('NIP',0)]
            assert run(p,(t,s,d,h),m) is None;cases+=1
    result=dict(status='PASS_SYMBOLIC_STACK_IDENTITIES',cases=cases,
                helper_row_counts=[1,2,8,10,12],KSP_helper_rows=10,
                scope='Generic stack identities; quantified mathematical proof is in foundations_notes.md',
                proof_assistant_checked=False)
    (Path(__file__).resolve().parent/'generic_proof_macros_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
