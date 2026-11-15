#!/usr/bin/env python3
"""Sound finite-window closure and exact bounded tape-preserving shortcuts."""
import sys,json,collections,hashlib,time
from pathlib import Path

def parse(p):
    rows={}
    for line in Path(p).read_text().splitlines():
        if line.strip() and not line.startswith('#'):
            q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
    return rows

def closure(rows,start,r):
    width=2*r+1; mask=(1<<width)-1; mid=1<<r
    out={q:set() for q,b in rows};out[start].add(0);todo=collections.deque([(start,0)])
    while todo:
        q,v=todo.popleft();b=(v>>r)&1
        w,d,n=rows[q,b]
        if n not in out:continue
        v=(v|mid) if w else(v&~mid)
        if d==1: a=v>>1;bb=a|(1<<(width-1))
        else: a=(v<<1)&mask;bb=a|1
        for v2 in (a,bb):
            if v2 not in out[n]:out[n].add(v2);todo.append((n,v2))
    return out

def possibilities(rows,q,v,r,cap=21):
    orig=v;h=r;ans={};bound=2*r+1
    for nsteps in range(1,cap+1):
        if not 0<=h<bound or(q,(v>>h)&1)not in rows:break
        w,d,q=rows[q,(v>>h)&1];v=(v|(1<<h))if w else(v&~(1<<h));h+=d
        if abs(h-r)==1 and ((v^orig)&~(1<<r))==0:
            a=((v>>r)&1,h-r,q)
            if a not in ans:ans[a]=nsteps
    return ans

def shortcuts(rows,seen,r,cap):
    hits=[]
    for q in sorted(seen):
        for b in (0,1):
            windows=[v for v in seen[q]if (v>>r)&1==b]
            if not windows:continue
            common=None;dur={}
            for v in windows:
                pp=possibilities(rows,q,v,r,cap);pp.pop(rows[q,b],None)
                if common is None:common=set(pp)
                else:common.intersection_update(pp)
                if not common:break
                for a in common:dur[a]=max(dur.get(a,0),pp[a])
            if common:
                hits.append({'row':[q,b],'old':rows[q,b],'choices':[{'action':a,'max_steps':dur[a]}for a in sorted(common)],'contexts':len(windows)})
    return hits
if __name__=='__main__':
    path=Path(sys.argv[1]);r=int(sys.argv[2])if len(sys.argv)>2 else 3
    # Native tables use74. Dense tables use0.
    start=int(sys.argv[3])if len(sys.argv)>3 else 74
    rows=parse(path);t=time.time();seen=closure(rows,start,r);print('closure',r,sum(map(len,seen.values())),time.time()-t,flush=True)
    hits=shortcuts(rows,seen,r,31);out={'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'radius':r,'state_count':len(seen),'abstract_configurations':sum(map(len,seen.values())),'empty_states':[q for q in seen if not seen[q]],'shortcuts':hits,'seconds':time.time()-t}
    print(json.dumps(out,indent=2),flush=True)
    Path(sys.argv[4]if len(sys.argv)>4 else'shortcuts.json').write_text(json.dumps(out,indent=2)+'\n')
