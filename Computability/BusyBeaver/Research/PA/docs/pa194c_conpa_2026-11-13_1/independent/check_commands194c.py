#!/usr/bin/env python3
"""Symbolic supplement for the generic nine/ten-entry command-word proof.

Opaque arbitrary stack tails and the exact all-zero Cantor alias are checked.
Undecided formula equalities are errors; no unknown branch is guessed.
"""
from pathlib import Path
from dataclasses import dataclass
from itertools import product
import sys,json
HERE=Path(__file__).resolve().parent
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not run with -O')
sys.path.insert(0,str(HERE/'reference'))
import command_terms as c

@dataclass(frozen=True)
class Stack:
    prefix: tuple
    tail: str='opaque'
    def __post_init__(self):
        if self.tail=='zero':
            p=self.prefix
            while p and p[-1]==0:p=p[:-1]
            object.__setattr__(self,'prefix',p)
    def prepend(self,xs):return Stack(tuple(xs)+self.prefix,self.tail)
    def pop(self):
        if self.prefix:return self.prefix[0],Stack(self.prefix[1:],self.tail)
        if self.tail=='zero':return 0,self
        raise ValueError('Attempted to inspect arbitrary underlying stack')

original_heads=c.heads

def verify_family(family,n):
    gamma=lambda B:c.I(B,c.U(B,B))
    c.heads=lambda D,H,A,d,h:((gamma(A),) if n==10 else ())+original_heads(D,H,A,d,h)
    def gate(a,b,x):
        if x==a or x==b:return 0
        return c.Term('gate',(family,a,b,x))
    c.gate=gate
    SH=c.SH;AX=c.AX;MP=c.MP;run=c.run;Store=c.Store
    PUSH=[AX()]+[SH]*(n-1)+[MP()]
    POP=[AX()]+[SH]*(n+1)
    DISCARD=[MP(1),AX(1)]+[SH]*n+[MP()]
    def offset(i):return []if i==0 else[MP(i)]
    def gen(i):return PUSH+offset(i)+[SH,AX(i)]+[SH]*n
    def select(j,D,H,A):return DISCARD+[AX(A,D,H)]+[SH]*(j+1)+POP*(n-1-j)
    def select_rho(a,b,z,u):return DISCARD+offset(u)+[AX(b,a-u,z)]+[SH]*(n-1)+POP
    def select_gate(a,b,z):return DISCARD+[AX(z,b,a)]+POP*n
    count=0
    def check(name,got,want):
        nonlocal count
        if got!=want:raise AssertionError((family,name,got,want))
        count+=1
    t=c.variable('t');a=c.variable('a');b=c.variable('b')
    d=c.variable('d','arbitrary');h=c.variable('h','arbitrary')
    x=c.variable('x','arbitrary');y=c.variable('y','arbitrary');z=c.variable('z','arbitrary')
    for tail in ['opaque','zero']:
        w=Stack((),tail)
        for top in [0,1,t]:
            st=Store(top,w,d,h)
            check('AX/S^(n-1)',run([AX(z,x,y)]+[SH]*(n-1),st),
                  Store(c.rho(c.add(d,x),z,c.add(h,y),d),w.prepend((top,)),0,c.U(d,h)))
            check('AX/S^n',run([AX(z,x,y)]+[SH]*n,st),Store(c.U(d,h),w,0,top))
            check('Push',run(PUSH,st),Store(0,w.prepend((top,)),0,0))
            for entry in [0,1,a]:
                check('Pop',run(POP,Store(top,w.prepend((entry,)),d,h)),None if top==1 else Store(top,w,0,entry))
            check('Discard',run(DISCARD,Store(top,w,0,0)),Store(0,w,0,0))
            for label in [0,1,c.variable('positive','positive')]:
                check('Gen',run(gen(label),Store(top,w,0,0)),Store(c.U(label,top),w,0,0))
            hh=c.heads(x,y,z,0,0)
            for j in range(1,n-2):
                check('head selector',run(select(j,x,y,z),Store(top,w,0,0)),Store(hh[j-1],w,0,0))
            for u in range(3):
                check('rho selector',run(select_rho(4,7,9,u),Store(top,w,0,0)),Store(c.rho(4,7,9,u),w,0,0))
            for aa,bb,cc in [(a,b,z),(0,0,0),(3,3,4),(4,3,4),(3,4,4)]:
                check('gate selector',run(select_gate(aa,bb,cc),Store(top,w,0,0)),Store(gate(aa,bb,cc),w,0,0))
            if n==10:
                for B in [0,1,z]:
                    check('diagonal head selector',run(select(1,0,0,B),Store(top,w,0,0)),Store(gamma(B),w,0,0))
        for aa,bb in product([0,1,a],[0,1,b]):
            check('MP suffix',run([SH,SH,MP(bb),SH],Store(0,w.prepend((aa,c.I(aa,bb),0)),0,0)),
                  None if aa==1 or bb==1 else Store(bb,w,0,0))
        check('terminal Pop',run(POP,Store(1,w,0,0)),None)
    return dict(family=family,pushed_entries=n,symbolic_cases=count,
                opaque_arbitrary_tail=True,total_zero_stack_and_zero_alias=True,
                all_axiom_selectors_safe=True,pop_halts_iff_preserved_top_one=True,
                mp_suffix_commands=4,scope='symbolic command algebra; universal proof in composite_command_audit.tex')

if __name__=='__main__':
    report=verify_family('PA194C',10)
    assert report['symbolic_cases']==188
    report['scope']='symbolic command algebra; supplementary evidence for the separately supplied uniform command proof'
    report['kernel_checked']=False
    (HERE/'results194c').mkdir(exist_ok=True)
    (HERE/'results194c/composite_commands.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
