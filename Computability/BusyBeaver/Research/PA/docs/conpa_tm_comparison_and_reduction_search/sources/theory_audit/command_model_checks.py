#!/usr/bin/env python3
"""Exact-integer regression checks for the proposed command reductions.

These bounded checks supplement the universal manuscript proof. They do not
certify tape simulation or replace PA-internal proof-compiler verification.
"""
import itertools, json, math
from pathlib import Path

def pair(a,b): return (a+b)*(a+b+1)//2+b
def unpair(n):
    s=(math.isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b
def I(a,b):return 4*pair(a,b)
def M(a,b):return I(a,b)+1
def U(a,b):return I(b,a)+2
def E(a,b):return I(a,b)+3
def N(a):return I(a,1)
def AND(a,b):return N(I(a,N(b)))
def EX(a,b):return N(U(a,N(b)))
def rho8(a,b,c,u):return I(I(I(c,u),a),I(I(a,c),I(b,c)))
def gate(a,b,c):
    if c==a or c==b:return 0
    p=I(c,M(c,b))
    sep=U(b,AND(I(M(a,b),p),I(M(c,b),c)))
    q=U(c,I(sep,N(p)))
    return N(I(I(E(a,b),U(c,E(a,b))),I(I(M(a,b),U(c,M(a,b))),q)))
def heads(D,H,A,d,h):
    return [I(U(D,A),I(U(D,I(A,H)),U(D,H))),EX(D,E(H,D)),
      I(E(H,D),I(M(A,H),M(A,D))),I(M(H,D),I(E(H,A),M(A,D))),
      I(U(D,U(A,H)),U(A,U(D,H))),I(EX(D,U(D,H)),H),
      rho8(D,A,H,d),U(d,h)]
def stack(xs,w):
    for x in reversed(xs):w=pair(x,w)
    return w
SHIFT=('s',)
def AX(c,x=0,y=0):return ('a',c,x,y)
def MP(x):return ('m',x)
PUSH=[AX(0)]+[SHIFT]*8+[MP(0)]
DROP=[MP(1),AX(1)]+[SHIFT]*9+[MP(0)]
POP=[AX(0)]+[SHIFT]*10

def step(cmd,s,shift_mode='h',mp_mode='h'):
    t,w,d,h=s
    if cmd[0]=='s':
        if (h==1 if shift_mode=='h' else t+h==1):return None
        a,w=unpair(w)
        return h,w,d,a
    if cmd[0]=='m':
        b=d+cmd[1]
        if I(t,b)==h:
            if mp_mode=='h':return 0,w,0,b
            if mp_mode=='nopush':return b,w,b,0
            return b,pair(0,w),b,0
        return 0,w,b,0
    _,c,x,y=cmd
    D,H=d+x,h+y
    return gate(H,D,c),stack(heads(D,H,c,d,h)+[t],w),0,0
def run(word,s,**opts):
    for cmd in word:
        if s is None:return None
        s=step(cmd,s,**opts)
    return s

def transport_shift_only(word,s):
    """If old word halts, return a new halting word from the same store."""
    cur=s
    for j,cmd in enumerate(word):
        nxt=step(cmd,cur,shift_mode='sum',mp_mode='old')
        if nxt is None:
            assert cmd==SHIFT and cur[0]+cur[3]==1
            suffix=[SHIFT] if cur[3]==1 else POP
            return word[:j]+suffix
        cur=nxt
    return None

def main():
    counts={}
    n=0
    for t,w,d,h in itertools.product(range(3),repeat=4):
        assert run(PUSH,(t,w,d,h))==(0,pair(t,w),0,0)
        n+=1
    counts['push']=n;n=0
    for t,w in itertools.product(range(5),repeat=2):
        assert run(DROP,(t,w,0,0))==(0,w,0,0);n+=1
    counts['drop']=n;n=0
    for t,a,w,d,h in itertools.product(range(2),repeat=5):
        got=run(POP,(t,pair(a,w),d,h))
        assert got==(None if t==1 else (t,w,0,a));n+=1
    counts['pop']=n;n=0
    for a,b,w,t in itertools.product(range(4),repeat=4):
        s=run(DROP+PUSH,(t,w,0,0))
        assert s==(0,pair(0,w),0,0)
        # Supply the recursively compiled implication and antecedent.
        s=run(PUSH,(I(a,b),s[1],0,0))
        s=run(PUSH,(a,s[1],0,0))
        suffix=[SHIFT,SHIFT,MP(b),SHIFT]
        got=run(suffix,s)
        expected=None if a==1 or b==1 else (b,w,0,0)
        assert got==expected,(a,b,w,t,got,expected)
        n+=1
    counts['mp_compiler_clause']=n;n=0
    commands=[SHIFT,MP(0),MP(1),MP(2)]
    for length in range(5):
      for word in itertools.product(commands,repeat=length):
       for t,w,d,h in itertools.product(range(2),repeat=4):
        s=(t,w,d,h)
        if run(word,s,shift_mode='sum',mp_mode='old') is not None:continue
        mapped=transport_shift_only(list(word),s)
        assert mapped is not None
        assert run(mapped,s,shift_mode='h',mp_mode='old') is None
        n+=1
    counts['old_halting_word_transports']=n
    counts['status']='passed; bounded command checks, not a tape or PA certification'
    target=Path(__file__).with_name('command_model_checks.json')
    target.write_text(json.dumps(counts,indent=2)+'\n')
    print(json.dumps(counts,indent=2))
if __name__=='__main__':main()
