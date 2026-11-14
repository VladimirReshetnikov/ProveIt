#!/usr/bin/env python3
"""Reproduce PA196's all-natural source-site contracts in Python.

The symbolic rules are a direct executable transcription of the published
M6/Runtime.lean. The four register-file summaries rely on unchanged engine
rows, checked separately. No bounded choice of a register value or gap is made.
"""
from pathlib import Path
import re
import json
from collections import Counter

BASE = Path(__file__).resolve().parents[1] / 'reference' / 'BusyBeaver'
PHYSICAL = [6,2,0,4,3,7,8,5,1]

def source_tree(path=BASE/'PA196/Program.lean'):
    nodes = {}
    token = re.compile(r'\(|\)|\.[A-Za-z]+|[A-Za-z][A-Za-z0-9]*|\d+')
    def parse(ts, i=0):
        t = ts[i]
        if t == '(':
            val,j = parse(ts,i+1)
            assert ts[j] == ')'
            return val,j+1
        if t == '.node':
            l,j=parse(ts,i+1);r,j=parse(ts,j)
            return (l,r),j
        if t == '.leaf':
            op,j=parse(ts,i+1)
            return ('leaf',op),j
        if t in ('.inc','.dec','.breakTo','.continueTo'):
            return (t[1:],int(ts[i+1])),i+2
        if t == '.halt':return ('halt',),i+1
        return nodes[t],i+1
    for line in path.read_text().splitlines():
        m=re.fullmatch(r'def (\w+) : Tree := (.*)',line)
        if m:
            ts=token.findall(m[2]);val,j=parse(ts)
            assert j==len(ts),(m[1],ts[j:])
            nodes[m[1]]=val
    return nodes['trie'],nodes

def flatten(t,p=()):
    if t[0]=='leaf':return [(p,t[1])]
    return flatten(t[0],p+(0,))+flatten(t[1],p+(1,))

def all_sites():
    return flatten(source_tree()[0])

def successor(p):
    for i in range(len(p)-1,-1,-1):
        if p[i]==0:return p[:i]+(1,)+(0,)*(len(p)-i-1)
    return None

def cut(p,b,k):
    if k==0:return p
    for i in range(len(p)-1,-1,-1):
        if p[i]==b:
            k-=1
            if k==0:return p[:i]
    raise ValueError(('bad cut',p,b,k))

def instructions(sites):
    def locate(p):
        if p is None:return 0
        for i,(q,op) in enumerate(sites):
            if q[:len(p)]==p or (p[:len(q)]==q and not any(p[len(q):])):return i
        raise ValueError(('unresolved',p))
    out=[]
    for p,op in sites:
        tag=op[0]
        if tag=='inc':out.append(('inc',op[1],locate(successor(p))))
        elif tag=='dec':out.append(('dec',op[1],locate(successor(cut(p,0,1))),locate(successor(p))))
        elif tag=='breakTo':out.append(('jump',locate(successor(cut(p,0,op[1])))))
        elif tag=='continueTo':out.append(('jump',locate(cut(p,1,op[1]))))
        elif tag=='halt':out.append(('halt',))
        else:raise ValueError(op)
    return out

def load_machine(path=BASE/'data/pa196.tm'):
    machine={}
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.startswith('#'):continue
        q,b,w,d,n=line.split()
        key=int(q),int(b)
        assert key not in machine
        assert d in ('L','R')
        machine[key]=(int(w),1 if d=='R' else -1,int(n))
    return machine

def labels():
    s=(BASE/'PA196/Conjugacy.lean').read_text()
    return json.loads(re.search(r'def labels : List Nat := (\[[^\n]+\])',s)[1])

LABELS=labels()
LITERAL={v:k for k,v in enumerate(LABELS)}
SKIPS={LITERAL[q]:i for i,q in enumerate([51,36,25,48,32,33,22,55,60])}
ROOT=LITERAL[84]
HALT=LITERAL[254]
ENGINE_OLD=[0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198]
ENGINE_ROWS={(LITERAL[q],b) for q in ENGINE_OLD for b in (0,1) if b or q not in (113,198)} | {(LITERAL[198],0)}

def check_engine(machine):
    reference=load_machine()
    return all(machine.get(k)==reference[k] for k in ENGINE_ROWS)

def bit(b):return ('bit',b)
def run(b,a,c):return ('run',b,a,c)
def box(effect='none',reg=-1):return ('box',effect,reg)
def frame(path,extra=0,effect='none',reg=-1):
    return (ROOT,False,(bit(1),),tuple(map(bit,path))+(run(0,1,48+extra-len(path)),bit(1),box(effect,reg)))

def norm(xs,left=False):
    out=[]
    for t in xs:
        if t[0]=='bit':t=run(t[1],0,1)
        if t[0]=='run' and t[2]==0 and t[3]==0:continue
        if out and t[0]=='run' and out[-1][0]=='run' and t[1]==out[-1][1]:
            old=out.pop();t=run(t[1],t[2]+old[2],t[3]+old[3])
        out.append(t)
    if left and out and out[-1][0]=='run' and out[-1][1]==0:out.pop()
    return tuple(out)

def matches(s,t):
    return s[:2]==t[:2] and norm(s[2],True)==norm(t[2],True) and norm(s[3])==norm(t[3])

def oracle(q,br,x):
    tag,effect,r=x
    if effect=='none':
        if q in SKIPS:
            j=SKIPS[q]
            return LITERAL[1 if j==0 else 3],box('mark',j),False
    elif effect=='mark' and r<9:
        if q==LITERAL[64]:return LITERAL[40],box('inc',r),False
        if q==LITERAL[0] and br is not None and br[0]==r:
            if br[1]:return LITERAL[97],box(),False
            return LITERAL[40],box('dec',r),True
    return None

def sstep(machine,br,s,record=None):
    q,onl,l,r=s
    if onl:
        if not l:return (q,False,(),(bit(0),)+r),False
        x,*tail=l;tail=tuple(tail)
        if x[0]=='bit':return (q,False,tail,(x,)+r),False
        if x[0]=='box':return None
        _,b,a,c=x
        row=machine.get((q,b))
        if row and row[1]==-1 and row[2]==q:
            if record is not None:record.append(('scanL',s,(q,b)))
            return (q,True,tail,(run(row[0],a,c),)+r),False
        if c:return (q,True,(bit(b),run(b,a,c-1))+tail,r),False
        if not a:return (q,True,tail,r),False
        return None
    if not r:return None
    x,*tail=r;tail=tuple(tail)
    if x[0]=='bit':
        b=x[1];row=machine.get((q,b))
        if row is None:return None
        if record is not None:record.append(('step',s,(q,b)))
        w,d,n=row
        if d==1:return (n,False,(bit(w),)+l,tail),True
        return (n,True,l,(bit(w),)+tail),True
    if x[0]=='run':
        _,b,a,c=x;row=machine.get((q,b))
        if row and row[1]==1 and row[2]==q:
            if record is not None:record.append(('scanR',s,(q,b)))
            return (q,False,(run(row[0],a,c),)+l,tail),False
        if c:return (q,False,l,(bit(b),run(b,a,c-1))+tail),False
        if not a:return (q,False,l,tail),False
        return None
    if x[0]=='box' and not tail:
        value=oracle(q,br,x)
        if value is not None:
            n,x2,extra=value
            if record is not None:record.append(('oracle',s,(q,x[1],x[2])))
            return (n,True,((bit(1),)+l if extra else l),(x2,)),False
        row=machine.get((q,0))
        if row and row[:2]==(0,-1):
            if record is not None:record.append(('step',s,(q,0)))
            return (row[2],True,l,r),True
    return None

def execute(machine,br,initial,target=None,fuel=1024,record=None):
    s=initial;moved=False
    for k in range(fuel):
        if moved and ((s[0]==HALT) if target is None else matches(s,target)):
            return k,s
        v=sstep(machine,br,s,record)
        if v is None:return None
        s,m=v;moved|=m
    return None

def contracts():
    sites=all_sites();codes=instructions(sites);out=[]
    for i,((p,op),c) in enumerate(zip(sites,codes)):
        initial=frame(p)
        if c[0]=='inc':
            out.append((i,'inc',None,initial,frame(sites[c[2]][0],0,'inc',PHYSICAL[c[1]])))
        elif c[0]=='dec':
            r=PHYSICAL[c[1]]
            out.append((i,'zero',(r,True),initial,frame(sites[c[2]][0])))
            out.append((i,'positive',(r,False),initial,frame(sites[c[3]][0],1,'dec',r)))
        elif c[0]=='jump':out.append((i,'jump',None,initial,frame(sites[c[1]][0])))
        else:out.append((i,'halt',None,initial,None))
    return out

def verify(machine=None,collect=False):
    if machine is None:machine=load_machine()
    assert check_engine(machine),'engine rows changed'
    observations=[];lengths=[]
    for i,branch,br,s,t in contracts():
        trace=[] if collect else None
        result=execute(machine,br,s,t,record=trace)
        if result is None:raise AssertionError(('failed',i,branch))
        lengths.append(result[0])
        if collect:observations.append((i,branch,trace))
    return {'contracts':len(lengths),'max_symbolic_steps':max(lengths),'sum_symbolic_steps':sum(lengths)},observations

if __name__=='__main__':
    import argparse,time
    p=argparse.ArgumentParser();p.add_argument('--table');p.add_argument('--trace',action='store_true')
    a=p.parse_args();start=time.monotonic()
    out,obs=verify(load_machine(a.table) if a.table else None,a.trace)
    out['seconds']=time.monotonic()-start
    print(json.dumps(out,indent=2))
