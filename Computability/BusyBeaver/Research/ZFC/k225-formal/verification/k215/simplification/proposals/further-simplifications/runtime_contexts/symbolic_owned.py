#!/usr/bin/env python3
"""Owned data-only symbolic interpreter, adapted from our earlier independent audit.
Incoming repository Python is never executed. This is not a Lean proof.
"""
from __future__ import annotations
import ast, collections, hashlib, json, re, sys
from pathlib import Path
if not __debug__: raise SystemExit('Assertions must be enabled')
ROOT=Path(__file__).resolve().parent

def read(path): return (ROOT / 'inputs' / path).read_text()
def literal(text):
    return ast.literal_eval(text.replace('true', 'True').replace('false', 'False').replace('none', 'None').replace('some ', ''))

def table_def(text, name, following):
    return literal(text.split('def '+name+' :', 1)[1].split(':=', 1)[1].split(following, 1)[0].strip())

class TreeParser:
    def __init__(self,text):
        self.ts=re.findall(r'\.[A-Za-z]+|\d+|[()]',text)
        assert re.sub(r'\s+','',text)==''.join(self.ts)
        self.i=0
    def pop(self,w=None):
        t=self.ts[self.i];self.i+=1
        if w is not None:assert t==w
        return t
    def tree(self):
        self.pop('(');op=self.pop()
        if op=='.node':out=('node',self.tree(),self.tree())
        else:
            assert op=='.leaf'
            if self.ts[self.i]=='(':
                self.pop('(');k=self.pop()[1:];a=int(self.pop());self.pop(')')
            else:k=self.pop()[1:];assert k=='halt';a=None
            out=('leaf',k,a)
        self.pop(')');return out

def sites():
    text=read('KSource215Data.lean').split('def t215 : Tree :=',1)[1].split('/-- dagPerm',1)[0].strip()
    p=TreeParser(text);tree=p.tree();assert p.i==len(p.ts)
    out=[]
    def walk(t,path):
        if t[0]=='leaf':out.append((path,t[1:]))
        else:walk(t[1],path+(False,));walk(t[2],path+(True,))
    walk(tree,());assert len(out)==4751;return out

def inc(p):
    p=list(p)
    for i in range(len(p)-1,-1,-1):
        if not p[i]:p[i]=True;break
        p[i]=False
    return tuple(p)
def strip(p,b,k):
    i=len(p)
    while k and i:
        i-=1
        if p[i]==b:k-=1
    return p[:i]
def brk(p,k):return inc(strip(p,False,k))
def cont(p,k):return strip(p,True,k)
def bit(b):return ('bit',bool(b))
def run(b,a,c):return ('run',bool(b),a,c)
def box(x):return ('box',x)
PLAIN=('plain','none',None)
SK=[51,36,25,48,32,33,22,55,60]
PHYS=[6,2,0,4,3,7,8,5,1]

def oracle(q,br,x):
    if x==PLAIN:
        if q in SK:
            r=SK.index(q);return (1 if r==0 else 3,('mark',r),False)
    elif x[0]=='mark':
        r=x[1]
        if r<9:
            if q==64:return (40,('plain','inc',r),False)
            if q==0 and br is not None and br[0]==r:
                return (97,PLAIN,False) if br[1] else (40,('plain','dec',r),True)
    return None

def peel(q,onl,b,a,c,l,r):
    if c:
        segs=(bit(b),run(b,a,c-1))
        return ((q,onl,segs+l,r) if onl else (q,onl,l,segs+r),False)
    if a==0:return ((q,onl,l,r),False)
    return None

def sstep(M,br,s):
    q,onl,l,r=s
    if onl:
        if not l:return ((q,False,(),(bit(False),)+r),False)
        x=l[0];tail=l[1:]
        if x[0]=='bit':return ((q,False,tail,(x,)+r),False)
        if x[0]=='box':return None
        _,b,a,c=x;row=M(q,b)
        if row is not None and not row[1] and row[2]==q:return ((q,True,tail,(run(row[0],a,c),)+r),False)
        return peel(q,True,b,a,c,tail,r)
    if not r:return None
    x=r[0];tail=r[1:]
    if x[0]=='bit':
        row=M(q,x[1])
        if row is None:return None
        w,d,n=row
        return ((n,False,(bit(w),)+l,tail) if d else (n,True,l,(bit(w),)+tail),True)
    if x[0]=='run':
        _,b,a,c=x;row=M(q,b)
        if row is not None and row[1] and row[2]==q:return ((q,False,(run(row[0],a,c),)+l,tail),False)
        return peel(q,False,b,a,c,l,tail)
    assert x[0]=='box'
    if tail:return None
    o=oracle(q,br,x[1])
    if o is not None:
        n,y,extra=o;return ((n,True,((bit(True),)+l if extra else l),(box(y),)),False)
    row=M(q,False)
    if row is not None and row[:2]==(False,False):return ((row[2],True,l,r),True)
    return None

def norm(xs):
    acc=[]
    for x in reversed(xs):
        t=run(x[1],0,1) if x[0]=='bit' else x
        if t[0]=='run':
            if t[2:]==(0,0):continue
            if acc and acc[-1][0]=='run' and acc[-1][1]==t[1]:
                old=acc.pop();t=run(t[1],t[2]+old[2],t[3]+old[3])
        acc.append(t)
    return tuple(reversed(acc))
def normL(xs):
    ts=norm(xs)
    return ts[:-1] if ts and ts[-1][0]=='run' and not ts[-1][1] else ts
def matches(s,e):
    return s[:2]==e[:2] and norm(s[3])==norm(e[3]) and normL(s[2])==normL(e[2])
def start(p):return (84,False,(bit(True),),tuple(map(bit,p))+(run(False,1,64-len(p)),bit(True),box(PLAIN)))
def target(p,ovf,x):
    growth=int(x[0]=='plain' and x[1]=='dec')
    assert len(p)<=64+ovf+growth
    return (84,False,(bit(True),),tuple(map(bit,p))+(run(False,1,64+ovf+growth-len(p)),bit(True),box(x)))

def exec_trace(M,br,p,tgt):
    s=start(p);moved=False;out=[]
    for f in range(4000):
        if moved and (s[0]==230 if tgt is None else matches(s,tgt)):return s,out
        step=sstep(M,br,s)
        if step is None:return None,out
        s,m=step;out.append((s,m));moved=moved or m
    return None,out


def verify_inputs():
    pins=json.loads((ROOT/'INPUT_PINS.json').read_text())
    for name,meta in pins['files'].items():
        b=(ROOT/'inputs'/name).read_bytes()
        if len(b)!=meta['bytes'] or hashlib.sha256(b).hexdigest()!=meta['sha256']:
            raise ValueError('Pinned input changed: '+name)
        if hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=meta['git_blob']:
            raise ValueError('Git blob mismatch: '+name)
verify_inputs()
