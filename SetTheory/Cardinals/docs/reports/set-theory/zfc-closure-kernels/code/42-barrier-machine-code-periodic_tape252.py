#!/usr/bin/env python3
"""Exact finite periodic-segment TM interpreter; huge lengths use Python ints.

Only monotone finite transition cycles are accelerated. Each skipped cycle
returns to the same state and input-pattern phase, with the checked direction.
"""
from collections import deque
import math,json,sys
from pathlib import Path
import macro252 as mm

def period(w):
    w=tuple(w)
    for k in range(1,len(w)+1):
        if len(w)%k==0 and all(w[i]==w[i%k] for i in range(len(w))):return w[:k]
    return w
def rotate(w,n):
    n%=len(w);return w[n:]+w[:n]
class Segs:
    def __init__(self,segs=()):
        self.a=deque()
        for w,n in reversed(segs):self.push(w,n)
    def push(self,w,n):
        if not n:return
        w=period(w)
        if self.a and len(w)==len(self.a[0][0]) and rotate(w,n)==self.a[0][0]:
            _,m=self.a.popleft();n+=m
        self.a.appendleft((w,n))
    def peek(self):return self.a[0][0][0] if self.a else 0
    def pop(self,n=1):
        if not self.a:
            assert n==1;return (0,)
        w,k=self.a.popleft();assert n<=k
        if n<k:self.a.appendleft((rotate(w,n),k-n))
        return w
    def trim(self):
        while self.a and self.a[-1][0]==(0,):self.a.pop()
    def compact(self):return [(list(w),n) for w,n in self.a]
    def copy(self):return Segs(self.a)

def equiv(A,B):
    A=A.copy();B=B.copy();A.trim();B.trim()
    while A.a or B.a:
        w,n=A.a[0] if A.a else ((0,),sum(k for _,k in B.a))
        v,k=B.a[0] if B.a else ((0,),sum(k for _,k in A.a))
        take=min(n,k);cap=min(take,math.lcm(len(w),len(v)))
        if any(w[i%len(w)]!=v[i%len(v)] for i in range(cap)):return False
        if A.a:A.pop(take)
        if B.a:B.pop(take)
    return True

def build_frame(path,gap,regs,spares,extra):
    segs=[((int(b),),1) for b in path]
    segs += [((0,),gap-len(path)),((1,),1)]
    for r in regs+spares:segs += [((0,),1),((1,),r+1)]
    if extra:segs.append(((0,1),extra*2))
    return Segs([((1,),1)]),Segs(segs)

def parse_dispatch(run):
    run.at_c()
    if not equiv(run.L,Segs([((1,),1)])):return None
    R=run.R.copy();bits=[]
    for i in range(35):bits.append(str(R.peek()));R.pop()
    p,op,r=mm.m.walk(''.join(bits));R=run.R.copy()
    for i in range(len(p)):R.pop()
    gap=len(p)
    while R.peek()==0:
        if not R.a:return None
        w,n=R.a[0]
        take=n if w==(0,) else 1
        R.pop(take);gap+=take
        if gap>10000:return None
    R.pop();regs=[]
    for j in range(9):
        if R.peek()!=0:return None
        R.pop()
        if R.peek()!=1:return None
        n=0
        while R.peek()==1:
            w,k=R.a[0];take=k if w==(1,) else 1;R.pop(take);n+=take
        regs.append(n-1)
    return {'p':p,'op':op,'r':r,'gap':gap,'regs':regs,'tail':R.compact(),'head':run.h,'steps':run.steps}

def tail_blocks(segments):
    R=Segs([(tuple(w),n) for w,n in segments]);R.trim();blocks=[]
    def add(n,k=1):
        if blocks and blocks[-1][0]==n:blocks[-1][1]+=k
        else:blocks.append([n,k])
    while R.a:
        w,n=R.a[0]
        if w==(0,1) and n>=4:
            k=n//2-1;R.pop(2*k);add(0,k);continue
        if R.peek()!=0:return None
        R.pop()
        if R.peek()!=1:return None
        k=0
        while R.peek()==1:
            w,n=R.a[0];take=n if w==(1,) else 1;R.pop(take);k+=take
        add(k-1)
    return blocks

def from_macro_state(st):
    if 'initial_spares' in st:
        return build_frame(st['p'],st['gap'],st['regs'],st['initial_spares'],st['positive_decs'])
    L,R=build_frame(st['p'],st['gap'],st['regs'],[],0)
    tail=Segs([(tuple(w),n) for w,n in st['initial_tail_segments']]);tail.trim()
    return L,Segs(list(R.a)+list(tail.a)+[((0,1),2*st['positive_decs'])])

def recover_collision(source,outfile,limit=200000):
    old=json.loads(Path(source).read_text());st=old['state'];L,R=from_macro_state(st)
    run=Run(mm.m.rows(),96,L,R);visits=0;sample=[]
    for i in range(limit):
        if run.q==254:
            result={'status':'halt','iterations':i,'raw_frame':run.frame(),'bulk':run.bulk};break
        if i and run.q==96:
            visits+=1;f=parse_dispatch(run)
            blocks=tail_blocks(f['tail']) if f else None
            if f and blocks is not None:
                result={'status':'recovered','iterations':i,'dispatch_visits':visits,'frame':f,'tail_blocks':blocks,'raw_frame':run.frame(),'bulk':run.bulk};break
            if len(sample)<8:sample.append(run.frame())
        run.step()
    else:result={'status':'fuel','iterations':limit,'dispatch_visits':visits,'raw_frame':run.frame(),'bulk':run.bulk}
    result['source']=Path(source).name;result['sample_visits']=sample
    Path(outfile).write_text(json.dumps(result,indent=2)+'\n')
    print('RECOVERY',result['status'],result['iterations'],run.steps,{k:v for k,v in result.get('frame',{}).items() if k!='tail'})
    return result

class Run:
    def __init__(self,T,q,L,R,h=0):self.T=T;self.q=q;self.L=L;self.R=R;self.h=h;self.left=False;self.steps=0;self.bulk=[]
    def at_c(self):
        if self.left:
            b=self.L.peek();self.L.pop();self.R.push((b,),1);self.left=False
    def step(self,bulk=True):
        A,B=(self.L,self.R) if self.left else (self.R,self.L)
        outward='L' if self.left else 'R';b=A.peek()
        w,d,q2=self.T[self.q,b]
        if bulk and A.a and A.a[0][1]>1 and d==outward:
            pat,n=A.a[0];q=self.q;outs=[];limit=min(n,len(pat)*len(self.T))
            found=False
            for j in range(limit):
                if (q,pat[j%len(pat)]) not in self.T:break
                wr,dr,qr=self.T[q,pat[j%len(pat)]]
                if dr!=outward:break
                outs.append(wr);q=qr
                if q==self.q and (j+1)%len(pat)==0:
                    k=j+1;rounds=n//k;length=k*rounds
                    A.pop(length);B.push(tuple(reversed(outs)),length)
                    self.h+=(-length if self.left else length);self.steps+=length
                    if length>1000:self.bulk.append({'q':self.q,'input':list(pat),'output':outs,'period':k,'copies':rounds,'direction':outward})
                    found=True;break
            if found:return
        A.pop()
        if d==outward:B.push((w,),1)
        else:A.push((w,),1);self.left=not self.left
        self.q=q2;self.h+=1 if d=='R' else -1;self.steps+=1
    def frame(self):
        self.at_c();return {'q':self.q,'h':self.h,'steps':self.steps,'L':self.L.compact(),'R':self.R.compact()}

def prefix_test():
    T=mm.m.rows()
    # Compare every step with the ordinary sparse simulator on deterministic
    # cases, while the accelerated copy independently checks full tape/frame.
    import random
    rng=random.Random(2026101702);checks=0;bulk_events=0
    for _ in range(30):
        ones={i for i in range(-30,31) if rng.randrange(2)};q=rng.choice(list({q for q,b in T}));h=0
        L=Segs([((int(i in ones),),1) for i in range(-1,-32,-1)])
        R=Segs([((int(i in ones),),1) for i in range(0,32)])
        run=Run(T,q,L,R)
        target=500
        while run.steps<target and run.q!=254:
            before=run.steps;run.step();count=run.steps-before
            for j in range(count):
                if q==254:raise AssertionError('skipped halt')
                w,d,q=T[q,int(h in ones)]
                if w:ones.add(h)
                else:ones.discard(h)
                h+=1 if d=='R' else -1
            run.at_c();assert q==run.q and h==run.h
            lo=min(ones|{h})-1;hi=max(ones|{h})+1
            expectedL=Segs([((int(i in ones),),1) for i in range(h-1,lo-1,-1)])
            expectedR=Segs([((int(i in ones),),1) for i in range(h,hi+1)])
            assert equiv(run.L,expectedL) and equiv(run.R,expectedR)
            checks+=1
        bulk_events+=len(run.bulk)
    return checks

if __name__=='__main__':
    root=Path(__file__).resolve().parents[1]
    print('Sparse cross-checks:',prefix_test())
    recover_collision(root/'certificates/macro32.json',root/'certificates/recovered34.json')
