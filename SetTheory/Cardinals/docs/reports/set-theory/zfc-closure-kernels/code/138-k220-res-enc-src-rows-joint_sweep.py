#!/usr/bin/env python3
"""Fast exact DAG counts for jointly permuted, fixed-position AX rows."""
from pathlib import Path
from functools import cache
import itertools,json,random,time
import search as z

NAMES=list(z.INTERVALS)
PERMS=list(itertools.permutations((3,4,5)))
NODES=[];INDEX={}
def intern(n):
    if n not in INDEX:
        INDEX[n]=len(NODES);NODES.append(n)
    return INDEX[n]

@cache
def old_id(t):
    return intern(t)if z.s.leaf(t)else intern(tuple(map(old_id,t)))

@cache
def permute(k,p):
    n=NODES[k]
    if isinstance(n[0],str):
        op,arg=n
        if op in ('CI','CD')and arg in(3,4,5):arg=PERMS[p][arg-3]
        return intern((op,arg))
    return intern(tuple(permute(c,p)for c in n))

@cache
def length(t):return 1 if z.s.leaf(t)else sum(map(length,t))

def skeleton(t,lo=0):
    hi=lo+length(t)
    for i,name in enumerate(NAMES):
        a,b=z.INTERVALS[name]
        if a<=lo and hi<=b:return ('R',i,tuple(permute(old_id(t),p)for p in range(6)))
    if all(hi<=a or lo>=b for a,b in z.INTERVALS.values()):return ('F',old_id(t))
    assert not z.s.leaf(t)
    return ('N',skeleton(t[0],lo),skeleton(t[1],lo+length(t[0])))

SKEL=skeleton(z.TREE)
BASE_NODES=list(NODES);BASE_INDEX=dict(INDEX)

def getroot(sk,v):
    if sk[0]=='F':return sk[1]
    if sk[0]=='R':return sk[2][v[sk[1]]]
    return intern((getroot(sk[1],v),getroot(sk[2],v)))

def count(v):
    r=getroot(SKEL,v);live={r};todo=[r]
    for k in todo:
        n=NODES[k]
        if isinstance(n[0],str):continue
        for j in n:
            if j not in live:live.add(j);todo.append(j)
    return len(live)

def reset():
    NODES[:]=BASE_NODES;INDEX.clear();INDEX.update(BASE_INDEX)

def as_perms(v):return {n:PERMS[p]for n,p in zip(NAMES,v)if p}

def main():
    result=[];best=208
    assert count((0,)*8)==208
    for i in range(8):
        for p in range(6):
            v=[0]*8;v[i]=p
            _,tree=z.changed(as_perms(v))
            assert count(v)==z.s.metrics(tree)['dag_nodes']
    print('Fast counter validated on all48 individual changes',flush=True)
    def evaluate(v,label):
        nonlocal best
        d=count(v)
        if d<=208:
            r={'indices':list(v),'permutations':as_perms(v),'dag_nodes':d,'search':label}
            result.append(r)
            print(json.dumps(r),flush=True)
            if d<best:
                best=d;print(json.dumps(z.check_variant(as_perms(v))),flush=True)
        if len(NODES)>250000:reset()
        return d
    tested=0
    for i,j in itertools.combinations(range(8),2):
        for p,q in itertools.product(range(1,6),repeat=2):
            v=[0]*8;v[i]=p;v[j]=q;evaluate(v,'pair');tested+=1
    print('pair sweep complete',tested,'best',best,flush=True)
    # All combinations among the smaller row family 1,2,4,6,8, with the
    # three expensive implication/equality rows fixed, permit interactions
    # that a single-coordinate search would miss.
    for positions in [(0,2,4,6,7),(1,3,5)]:
        for ps in itertools.product(range(6),repeat=len(positions)):
            v=[0]*8
            for i,p in zip(positions,ps):v[i]=p
            evaluate(v,'subcube');tested+=1
        print('subcube complete',positions,'tested',tested,'best',best,flush=True)
    # Whole-row relabelings can share with one another even when each
    # separate change is costly.
    for ps in itertools.product(range(6),repeat=2):
        for cut in range(1,8):
            evaluate([ps[0]]*cut+[ps[1]]*(8-cut),'uniform split');tested+=1
    # Coordinate descent from random points, allowing neutral moves.
    rng=random.Random(20261020)
    for restart in range(300):
        v=[rng.randrange(6)for _ in range(8)];d=count(v)
        for turn in range(10):
            moves=[]
            for i in range(8):
                for p in range(6):
                    if p==v[i]:continue
                    w=v.copy();w[i]=p;dd=count(w);tested+=1
                    if dd<=d:moves.append((dd,w))
            if not moves:break
            dd=min(x[0]for x in moves)
            if dd==d and turn>5:break
            v=rng.choice([w for e,w in moves if e==dd]);d=dd
            if d<=208:evaluate(v,'coordinate descent')
            if len(NODES)>250000:reset()
        if restart%50==0:print('restart',restart,'tested',tested,'best',best,flush=True)
    payload={'status':'EXACT_DAG_EXPLORATION_COMPLETE','tested':tested,'best':best,'rows':NAMES,'records':result}
    (z.HERE/'joint_summary.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('complete',tested,'best',best,flush=True)

if __name__=='__main__':main()
