#!/usr/bin/env python3
"""Check command compilers with halting relocated to successful MP.

The symbolic checks quantify over free natural-number/stack parameters and
use only explicitly justified arithmetic/constructor rewrites. Separate
integer checks execute the exact commands with Cantor pairing, including
the zero-stack alias. This is not a proof-assistant kernel certificate.
"""
from dataclasses import dataclass
from math import isqrt
from pathlib import Path
from functools import lru_cache
import json
import itertools


@dataclass(frozen=True)
class Term:
    op: str
    args: tuple


def V(name):
    return Term('var', (name,))


class Symbolic:
    def add(self, a, b):
        if a == 0: return b
        if b == 0: return a
        if isinstance(a, int) and isinstance(b, int): return a+b
        return Term('add', (a,b))
    def succ(self, a):
        return a+1 if isinstance(a,int) else Term('succ',(a,))
    def pair(self, a, b):
        return 0 if a == b == 0 else Term('pair',(a,b))
    def head(self, w):
        if w == 0: return 0
        if isinstance(w,Term) and w.op=='pair': return w.args[0]
        return Term('head',(w,))
    def tail(self, w):
        if w == 0: return 0
        if isinstance(w,Term) and w.op=='pair': return w.args[1]
        return Term('tail',(w,))
    def I(self,a,b):
        return 0 if a == b == 0 else Term('I',(a,b))
    def M(self,a,b):
        return 1 if a == b == 0 else Term('M',(a,b))
    def U(self,a,b): return Term('U',(a,b))
    def E(self,a,b): return Term('E',(a,b))
    def gate(self,h,d,a):
        if a==h or a==d: return 0
        return Term('guardedGate',(h,d,a))
    def residue(self,t):
        if isinstance(t,int):return t%4
        return {'I':0,'M':1,'U':2,'E':3,'guardedGate':0}.get(t.op)
    def positive(self,t):
        if isinstance(t,int):return t>0
        if t.op in ('succ','M','U','E'):return True
        if t.op in ('I','pair'):
            return self.positive(t.args[0]) is True or self.positive(t.args[1]) is True
        return None
    def equal(self,a,b):
        if a==b:return True
        if isinstance(a,int) and isinstance(b,int):return False
        if a==0 and self.positive(b) is True:return False
        if b==0 and self.positive(a) is True:return False
        if isinstance(a,Term) and a.op=='succ' and isinstance(b,int):
            return False if b==0 else self.equal(a.args[0],b-1)
        if isinstance(b,Term) and b.op=='succ' and isinstance(a,int):
            return False if a==0 else self.equal(a-1,b.args[0])
        ra,rb=self.residue(a),self.residue(b)
        if ra is not None and rb is not None and ra!=rb:return False
        raise ValueError(('symbolic comparison not justified',a,b))
    def zero(self,k):
        if k==0:return True
        if self.positive(k) is True:return False
        raise ValueError(('zero status is unspecified',k))


class Integer:
    def __init__(self):self.stack_pairs={}
    def add(self,a,b):return a+b
    def succ(self,a):return a+1
    def pair(self,a,b):
        n=(a+b)*(a+b+1)//2+b
        self.stack_pairs[n]=(a,b)
        return n
    def unpair(self,n):
        # Reuse an exact pair construction when available; this avoids an
        # expensive square root of the enormous but irrelevant AX stacks.
        if n in self.stack_pairs:return self.stack_pairs[n]
        s=(isqrt(8*n+1)-1)//2
        b=n-s*(s+1)//2
        return s-b,b
    def head(self,w):return self.unpair(w)[0]
    def tail(self,w):return self.unpair(w)[1]
    def I(self,a,b):return 4*((a+b)*(a+b+1)//2+b)
    def M(self,a,b):return self.I(a,b)+1
    def U(self,a,b):return self.I(b,a)+2
    def E(self,a,b):return self.I(a,b)+3
    @lru_cache(maxsize=256)
    def gate(self,h,d,a):
        if a==h or a==d:return 0
        N=lambda b:self.I(b,1)
        And=lambda b,c:N(self.I(b,N(c)))
        v=self.I(self.M(h,d),self.U(a,self.M(h,d)))
        p=self.I(a,self.M(a,d))
        sep=self.U(d,And(self.I(self.M(h,d),p),self.I(self.M(a,d),a)))
        q=self.U(a,self.I(sep,N(p)))
        return N(self.I(v,q))
    def equal(self,a,b):return a==b
    def zero(self,a):return a==0


HALT='HALT'


class Commands:
    def __init__(self, backend, clear_success_offset=False, target_shift=1,
                 success_offset_fn=None):
        self.b=backend
        self.clear_success_offset=clear_success_offset
        assert target_shift in (0,1)
        self.target_shift=target_shift
        self.success_offset_fn=success_offset_fn
    @lru_cache(maxsize=1024)
    def heads(self,d,h,A,x,y):
        B=self.b
        D,H=B.add(d,x),B.add(h,y)
        I,M,U,E=B.I,B.M,B.U,B.E
        N=lambda b:I(b,1)
        Ex=lambda a,b:N(U(a,N(b)))
        hs=[I(Ex(D,U(D,H)),H),I(U(D,U(A,H)),U(A,U(D,H))),
            I(M(H,D),I(E(H,A),M(A,D))),I(E(H,D),I(M(A,H),M(A,D))),
            Ex(D,E(H,D)),I(U(D,A),I(U(D,I(A,H)),U(D,H)))]
        gamma=I(A,U(A,A))
        rho=I(I(I(H,d),D),I(I(D,H),I(A,H)))
        return [gamma]+hs[::-1]+[rho,U(d,h)]
    def ax(self,A,x,y,s):
        if s==HALT:return HALT
        t,w,d,h=s;B=self.b
        qs=self.heads(d,h,A,x,y)
        stack=B.pair(t,w)
        for q in reversed(qs):stack=B.pair(q,stack)
        return (B.gate(B.add(h,y),B.add(d,x),A),stack,0,0)
    def shift(self,s):
        if s==HALT:return HALT
        t,w,d,h=s
        return (h,self.b.tail(w),d,self.b.head(w))
    def shifts(self,s,n):
        for _ in range(n):s=self.shift(s)
        return s
    def mp(self,x,s):
        if s==HALT:return HALT
        t,w,d,h=s;B=self.b;k=B.add(d,x);b=B.succ(k) if self.target_shift else k
        if not self.target_shift and k==0:
            # Both equality outcomes are literally (0,w,0,0); target0
            # cannot satisfy the singleton halt test. This is a branch join.
            return (0,w,0,0)
        if not B.equal(B.I(t,b),h):return (0,w,k,0)
        if B.zero(k) if self.target_shift else B.equal(k,1):return HALT
        out_d=(self.success_offset_fn(k) if self.success_offset_fn is not None
               else 0 if self.clear_success_offset else k)
        return (b,w,out_d,0)
    def push(self,s):return self.mp(0,self.shifts(self.ax(0,0,0,s),9))
    def pop(self,s):return self.shifts(self.ax(0,0,0,s),11)
    def discard(self,s):return self.mp(0,s)
    def offset(self,i,s):return self.mp(i,s)
    def select(self,j,A,D,H,s):
        s=self.discard(s);s=self.ax(A,D,H,s);s=self.shifts(s,j+1)
        for _ in range(9-j):s=self.pop(s)
        return s
    def gen(self,i,s):
        s=self.push(s);s=self.offset(i,s);s=self.shift(s)
        s=self.ax(i,0,0,s);return self.shifts(s,10)
    def mp_suffix(self,k,s):
        s=self.shifts(s,2);s=self.mp(k,s);return self.pop(s)


def symbolic_checks():
    B=Symbolic();C=Commands(B)
    t,w,d,h,a,A,D,H,i,k=map(V,'t w d h a A D H i k'.split())
    checks=[]
    def ck(name,got,wanted):
        assert got==wanted,(name,got,wanted);checks.append(name)
    ck('Push arbitrary store',C.push((t,w,d,h)),(0,B.pair(t,w),0,0))
    ck('Pop arbitrary store',C.pop((t,B.pair(a,w),d,h)),(t,w,0,a))
    ck('Discard clean caches',C.discard((t,w,0,0)),(0,w,0,0))
    ck('Offset arbitrary index',C.offset(i,(0,w,0,0)),(0,w,i,0))
    ck('Generalization arbitrary index',C.gen(i,(a,w,0,0)),(B.U(i,a),w,0,0))
    qs=C.heads(0,0,A,D,H)
    for j in range(1,8):
        ck(f'Select emitted head {j}',C.select(j,A,D,H,(t,w,0,0)),(qs[j-1],w,0,0))
    # Parameterize the dominance condition a>=u as a=u+x, avoiding a
    # symbolic subtraction oracle. The emitted old offset is exactly u.
    u,x=V('u'),V('x')
    s=C.offset(u,C.discard((t,w,0,0)))
    s=C.ax(A,x,H,s);s=C.pop(C.shifts(s,9))
    q8=C.heads(u,0,A,x,H)[7]
    ck('Dominated-head selector for a=u+x',s,(q8,w,0,0))
    s=C.ax(A,D,H,C.discard((t,w,0,0)))
    for _ in range(10):s=C.pop(s)
    ck('Guarded gate selector',s,(B.gate(H,D,A),w,0,0))
    # Ordinary MP with positive k, hence conclusion k+1 >=2.
    # k is represented as succ(k0), allowing the singleton test to decide.
    for clear in (False,True):
        C=Commands(B,clear);kp=B.succ(k);b=B.succ(kp)
        stack=B.pair(a,B.pair(B.I(a,b),B.pair(0,w)))
        ck(f'MP b>=2, clear_offset={clear}',C.mp_suffix(kp,(0,stack,0,0)),(b,w,0,0))
        stack=B.pair(a,B.pair(B.I(a,1),B.pair(0,w)))
        ck(f'MP conclusion1 halts, clear_offset={clear}',C.mp_suffix(0,(0,stack,0,0)),HALT)
        ck(f'MP conclusion0 shortcut, clear_offset={clear}',C.discard((t,w,0,0)),(0,w,0,0))
    C=Commands(B,success_offset_fn=lambda n:Term('arbitraryNaturalOffset',(n,)))
    kp=B.succ(k);b=B.succ(kp)
    stack=B.pair(a,B.pair(B.I(a,b),B.pair(0,w)))
    ck('MP b>=2 with arbitrary total successful offset',
       C.mp_suffix(kp,(0,stack,0,0)),(b,w,0,0))
    ck('Cantor zero pair alias',B.pair(0,0),0)
    ck('Zero head alias',B.head(0),0)
    ck('Zero tail alias',B.tail(0),0)
    ck('Implication zero alias',B.I(0,0),0)
    ck('Pop zero stack',C.pop((t,0,d,h)),(t,0,0,0))
    ck('Push zero on zero',C.push((0,0,d,h)),(0,0,0,0))
    # Also audit the original-target variant at command level. The
    # literal MPplus201 prototype instead uses target_shift=1 and clears
    # the successful offset. All checks here use the abstract total Shift.
    C=Commands(B,clear_success_offset=True,target_shift=0)
    ck('Unshifted Push arbitrary store',C.push((t,w,d,h)),(0,B.pair(t,w),0,0))
    ck('Unshifted Pop arbitrary store',C.pop((t,B.pair(a,w),d,h)),(t,w,0,a))
    ck('Unshifted Discard arbitrary cache',C.discard((t,w,0,h)),(0,w,0,0))
    ck('Unshifted Offset0',C.offset(0,(0,w,0,0)),(0,w,0,0))
    ip=B.succ(i)
    ck('Unshifted positive Offset',C.offset(ip,(0,w,0,0)),(0,w,ip,0))
    for conclusion in (0,1,B.succ(B.succ(k))):
        stack=B.pair(a,B.pair(B.I(a,conclusion),B.pair(0,w)))
        ck(f'Unshifted MP result {conclusion if isinstance(conclusion,int) else ">=2"}',
           C.mp_suffix(conclusion,(0,stack,0,0)),HALT if conclusion==1 else (conclusion,w,0,0))
    return checks


def integer_checks():
    B=Integer();count=0
    for shift,clear in ((1,False),(1,True),(0,True)):
        C=Commands(B,clear,target_shift=shift)
        # Direct small-store identities, including arbitrary incoming caches.
        for t,w,d,h in [(0,0,0,0),(1,0,0,0),(2,1,1,0),(1,2,0,1),(2,2,1,1)]:
            s=(t,w,d,h)
            assert C.push(s)==(0,B.pair(t,w),0,0)
            assert C.pop(s)==(t,B.tail(w),0,B.head(w))
            count+=2;B.stack_pairs.clear()
        for t,w in itertools.product(range(3),repeat=2):
            assert C.discard((t,w,0,0))==(0,w,0,0);count+=1
        for a,w,i in itertools.product(range(2),repeat=3):
            assert C.gen(i,(a,w,0,0))==(B.U(i,a),w,0,0);count+=1;B.stack_pairs.clear()
        for a,b,w in itertools.product(range(2),range(shift,3),range(2)):
            stack=B.pair(a,B.pair(B.I(a,b),B.pair(0,w)))
            assert C.mp_suffix(b-shift,(0,stack,0,0))==(HALT if b==1 else (b,w,0,0));count+=1;B.stack_pairs.clear()
        for A,D,H,j in [(0,0,0,j) for j in range(1,8)]:
            qs=C.heads(0,0,A,D,H)
            assert C.select(j,A,D,H,(2,3,0,0))==(qs[j-1],3,0,0);count+=1;B.stack_pairs.clear()
    return count


def scheduler_checks():
    # These are checks of unchanged command-word encoding, not a substitute
    # for the stated induction using strict continuation descent.
    B=Integer()
    def encode(word):
        n=0
        for c in reversed(word):
            if c[0]=='S':n=1+B.pair(0,n)
            elif c[0]=='MP':n=1+B.pair(1,B.pair(c[1],n))
            else:
                _,a,x,y=c;n=1+B.pair(a+2,B.pair(y,B.pair(x,n)))
        return n
    def decode(v):
        # A distinct backend forces ordinary square-root inversion, without
        # access to the constructor's memoized inverse pairs.
        C=Integer();tag,r=C.unpair(v)
        if tag==0:return ('S',),r
        if tag==1:
            x,r=C.unpair(r);return ('MP',x),r
        y,r=C.unpair(r);x,r=C.unpair(r)
        return ('AX',tag-2,x,y),r
    alphabet=[('S',),('MP',0),('MP',2),('AX',0,0,0),('AX',1,1,2)]
    count=0
    for length in range(1,4):
        for word in itertools.product(alphabet,repeat=length):
            n=encode(word)
            assert decode(n-1)==(word[0],encode(word[1:]));count+=1
    for v in range(256):
        command,residual=decode(v)
        assert residual<=v;count+=1
    for k in range(8):
        code=encode([('AX',k,0,0),('S',),('MP',0)])
        assert code-1>=k+2;count+=1
    return count


def main():
    assert __debug__,'Run without Python -O.'
    symbolic=symbolic_checks()
    print(f'Checked {len(symbolic)} symbolic identities.',flush=True)
    result={'status':'PASS','symbolic_identities':symbolic,
            'integer_identity_checks':integer_checks(),
            'scheduler_encoding_checks':scheduler_checks(),
            'scope':'Command calculus and compositional proof-word identities; no literal TM or state count certified.',
            'zero_aliases_explicit':True,
            'success_offset_conventions':['retain k','clear to 0','arbitrary total natural r(k), symbolically'],
            'protocols':['target d+x+1, arbitrary total natural success offset r(k)',
                         'target d+x, success offset cleared']}
    out=Path(__file__).with_name('mp_positive_checks.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
