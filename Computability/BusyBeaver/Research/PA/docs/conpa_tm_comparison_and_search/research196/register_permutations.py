#!/usr/bin/env python3
"""Rebuild the complete unfused decoder and vary physical register locations."""
import sys,json,itertools,time,collections,random
from pathlib import Path
BASE=Path('support')
sys.path.insert(0,str(BASE/'work/optimize196'))
sys.path.insert(0,'research_ipra/newsearch')
import rotation_search as rs
from layout import *
OUT=Path(__file__).resolve().parent/'register_permutations';OUT.mkdir(exist_ok=True)
ENGINE={0,1,2,3,4,5,6,9,10,15,16,22,23,24,25,32,33,34,35,36,40,48,49,51,54,55,60,64,66,74,75,94,97,113,198,302}
OLD,LABELS=machine();TREE=rs.INITIAL
CAT={tuple(k):set(map(tuple,v)) for k,v in json.loads(Path('research_ipra/newsearch/leaf_actions.json').read_text())}
INDEX={};SHAPE={}
def intern(t):
    if not isnode(t):return None
    if t in INDEX:return INDEX[t]
    for x in t:intern(x)
    q=84 if t==TREE else 3000+len(INDEX)
    INDEX[t]=q;SHAPE[q]=t;return q
intern(TREE)
_,BYQ=rs.interfaces(OLD,TREE)
HELPER={q:INDEX[next(iter(ts))] for q,ts in BYQ.items() if len(ts)==1}
HELPER.update({108:INDEX[rs.expand('node0')],42:INDEX[rs.expand('node9')]})
JUMPS=collections.defaultdict(set)
sites,ins=program()
for p,op,arg in sites:
    if op in ('inc','dec'):continue
    q,h=84,0
    for _ in range(500):
        b=p[h];act=OLD[q,b]
        if h==len(p)-1 and act in CAT[op,arg,b]:break
        q=act[2];h+=1 if act[1] else -1
    else:raise ValueError((p,op,arg))
    par=TREE
    for b in p[:-1]:par=par[b]
    w,d,n=act
    if n not in ENGINE|{254}:n=HELPER[n]
    JUMPS[INDEX[par],p[-1]].add((w,d,n))
print('rawnodes',len(INDEX),'ambiguous jump rows',[(k,v) for k,v in JUMPS.items() if len(v)>1],flush=True)
def build_full(physical):
    rows={(q,b):OLD[q,b] for q in ENGINE for b in (0,1)};shape=dict(SHAPE)
    for kind in ('inc','dec'):
      for r in range(9):
        q=4000+(kind=='dec')*9+r
        rows[q,0]=(0,True,49 if kind=='inc' else 24)
        rows[q,1]=(0,True,SK[physical[r]])
        shape[q]=('router',kind,r)
    for t,q in INDEX.items():
      for b,x in enumerate(t):
        if isnode(x):act=(b,True,INDEX[x])
        else:
            _,op,arg=x
            if op in ('inc','dec'):act=(b,True,4000+(op=='dec')*9+arg)
            else:act=min(JUMPS[q,b])
        rows[q,b]=act
    assert len(rows)==426
    return rows,shape
def contracts_for(physical):
    out=[]
    for i,code in enumerate(ins):
        st=frame(sites[i][0])
        if code[0]=='inc':
            _,r,n=code;out.append((i,None,st,canonical(frame(sites[n][0],0,('x','inc',physical[r])))))
        elif code[0]=='dec':
            _,r,z,p=code
            out.append((i,(physical[r],True),st,canonical(frame(sites[z][0]))))
            out.append((i,(physical[r],False),st,canonical(frame(sites[p][0],1,('x','dec',physical[r])))))
        elif code[0]=='jump':out.append((i,None,st,canonical(frame(sites[code[1]][0]))))
        else:out.append((i,None,st,None))
    return out
def folded(rows,shape,goal,cs,limit=50000):
    seen=set();tested=0
    def rec(rr,ss,hist):
        nonlocal tested
        if tested>=limit:return
        if len(hist)>=goal:
            tested+=1;ans=validate(rr,cs)
            if ans['ok']:return rr,hist,ans
            return
        ops=opportunities_fast(rr,ss)
        if len(hist)+len(max_matching(ops))<goal:return
        for a,b,opts in ops:
          for acts in itertools.product(*opts):
            nr=fold(rr,a,b,acts);ns=dict(ss);ns.pop(a)
            key=tuple(sorted(nr.items()))
            if key in seen:continue
            seen.add(key)
            found=rec(nr,ns,hist+[(a,b,acts)])
            if found:return found
    return rec(rows,shape,[])
if __name__=='__main__':
    rows,shape=build_full(PHYSICAL);cs=contracts_for(PHYSICAL)
    ans=validate(rows,cs);ops=opportunities_fast(rows,shape);folds=len(max_matching(ops))
    print('BASE',len(rows)//2,'folds',folds,'validation',ans,flush=True)
    (OUT/'baseline.json').write_text(json.dumps({'rows':[[q,b,*a] for (q,b),a in sorted(rows.items())],'physical':PHYSICAL,'folds':folds,'validation':ans}))
    if not ans['ok']:raise SystemExit(1)
    best=213-folds;hist=collections.Counter();start=time.time();count=0
    perms=list(itertools.permutations([p for p in range(9) if p!=6]));random.Random(195).shuffle(perms)
    for tail in perms:
        physical=(6,)+tail;rr,ss=build_full(physical)
        ops=opportunities_fast(rr,ss);nf=len(max_matching(ops));cost=213-nf;hist[cost]+=1;count+=1
        if cost<best:
            best=cost;print('BEST',best,'physical',physical,'count',count,'seconds',time.time()-start,flush=True)
            (OUT/'best.json').write_text(json.dumps({'physical':physical,'folds':nf,'cost':cost}))
        if cost<196:
            print('POTENTIAL',physical,nf,'checking',flush=True)
            cs=contracts_for(physical);rawcheck=validate(rr,cs)
            print('RAWVALID',rawcheck,flush=True)
            if rawcheck['ok']:
                result=folded(rr,ss,18,cs,10000)
                if result:
                    out,fhist,ans=result
                    (OUT/'candidate195.json').write_text(json.dumps({'rows':[[q,b,*a] for(q,b),a in sorted(out.items())],'physical':physical,'folds':fhist,'validation':ans,'sites':sites}))
                    print('SUCCESS',len(out)//2,physical,ans,flush=True);raise SystemExit()
        if count%1000==0:print('PROGRESS',count,'best',best,'seconds',time.time()-start,flush=True)
    (OUT/'receipt.json').write_text(json.dumps({'count':count,'best':best,'histogram':hist,'seconds':time.time()-start}))
