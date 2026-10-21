#!/usr/bin/env python3
"""Finite product abstract interpretation of K215's source. Standard library only."""
import argparse,json,hashlib,gzip
from collections import deque,Counter
if not __debug__: raise RuntimeError('Run with assertions enabled, without -O.')
from pathlib import Path

def graph(rows):
    leaves={p:i for i,(p,o,a) in enumerate(rows)};D=max(map(len,leaves))
    def locate(p):
        w=p+'0'*D
        for n in range(1,D+1):
            if w[:n] in leaves:
                assert '1' not in p[n:];return leaves[w[:n]]
        raise ValueError(p)
    def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b') if p else ''
    def cut(p,b,k):
        at=[i for i,c in enumerate(p)if c==b]
        return p[:at[-k]] if len(at)>=k else ''
    out=[]
    for p,o,a in rows:
        if o=='CI':to=[locate(inc(p))]
        elif o=='CD':to=[locate(inc(cut(p,'0',1))),locate(inc(p))]
        elif o=='CB':to=[locate(inc(cut(p,'0',a)))]
        elif o=='CC':to=[locate(cut(p,'1',a))]
        else:assert o=='CH';to=[]
        out.append(to)
    return out

def image(mask,op,K):
    z=0
    for j in range(K+1):
        if mask>>j&1:
            if op=='CI':z|=1<<min(j+1,K)
            elif j>0:
                z|=1<<(j-1)
                if j==K:z|=1<<K
    return z

def edges(rows,G,I,i,K):
    if I[i] is None:return []
    p,op,a=rows[i];v=list(I[i]);out=[]
    if op=='CI':v[a]=image(v[a],op,K);out=[(G[i][0],tuple(v))]
    elif op=='CD':
        if v[a]&1:
            v0=v.copy();v0[a]=1;out.append((G[i][0],tuple(v0)))
        if v[a]&~1:
            v[a]=image(v[a],op,K);out.append((G[i][1],tuple(v)))
    elif op in ('CC','CB'):out=[(G[i][0],tuple(v))]
    return out

def analyze(rows,K):
    G=graph(rows);I=[None]*len(rows);I[0]=tuple(1<<min(n,K)for n in [4,0,0,0,0,0,0,0,0]);q=deque([0]);queued={0};ticks=0
    while q:
        i=q.popleft();queued.remove(i);ticks+=1
        for j,v in edges(rows,G,I,i,K):
            w=v if I[j] is None else tuple(a|b for a,b in zip(I[j],v))
            if w!=I[j]:
                I[j]=w
                if j not in queued:q.append(j);queued.add(j)
    for i in range(len(rows)):
        for j,v in edges(rows,G,I,i,K):assert I[j] is not None and all(a&~b==0 for a,b in zip(v,I[j]))
    return I,G,ticks

def main():
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--cutoff',type=int,default=2);a=ap.parse_args()
    raw=a.source.read_bytes();rows=json.loads(raw);I,G,ticks=analyze(rows,a.cutoff)
    impossible=[]
    for i,(p,o,r)in enumerate(rows):
        for positive in ((False,True)if o=='CD'else(False,)):
            possible=I[i] is not None and (o!='CD' or (I[i][r]&~1 if positive else I[i][r]&1))
            if not possible:impossible.append((i,positive))
    report={'source_sha256':hashlib.sha256(raw).hexdigest(),'cutoff':a.cutoff,'source_sites':len(rows),'source_cases':sum(2 if x[1]=='CD' else 1 for x in rows),'fixed_point_visits':ticks,'unreachable_sites':sum(x is None for x in I),'unreachable_cases':impossible,'known_zero_registers':sum(v==1 for x in I if x is not None for v in x),'singleton_registers':sum(v>0 and v&(v-1)==0 and v!=1<<a.cutoff for x in I if x is not None for v in x),'invariants':I}
    a.output.parent.mkdir(exist_ok=True,parents=True);a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items()if k not in ['invariants','unreachable_cases']},indent=2))
    print('Unreachable guarded cases:',len(impossible))
if __name__=='__main__':main()
