from pathlib import Path
from collections import deque
import sys,json,time
sys.path.insert(0,str(Path(__file__).parent/'input'))
import permutation252_phase_analysis as p
sites,cases,targets,first=p.program_graph((Path(__file__).parent/'input/Prog254.v').read_bytes())
by=[[] for _ in sites]
for i,c in enumerate(cases): by[c[0]].append(i)

def calculate(K):
    top=1<<K; small=top-1; allmask=2*top-1
    def step(v,c):
        _,_,op,r,z=c; out=list(v)
        if op=='CI':out[r]=((out[r]&small)<<1)|(out[r]&top)
        elif op=='CD':
            if z:
                if not out[r]&1:return
                out[r]=1
            else:
                if not out[r]&~1:return
                out[r]=((out[r]&small)>>1)|((top|(top>>1)) if out[r]&top else 0)
        return tuple(out)
    v=[None]*len(sites);v[first]=(1,)*9;q=deque([first]);queued={first};n=0
    t=time.monotonic()
    while q:
        i=q.popleft();queued.remove(i);n+=1
        for ci in by[i]:
            dst=targets[ci]
            if dst is None:continue
            w=step(v[i],cases[ci])
            if w is None:continue
            old=v[dst];new=w if old is None else tuple(x|y for x,y in zip(old,w))
            if new!=old:
                v[dst]=new
                if dst not in queued:q.append(dst);queued.add(dst)
    excluded=[]
    for ci,c in enumerate(cases):
        w=None if v[c[0]] is None else step(v[c[0]],c)
        if w is None:excluded.append(ci)
        elif targets[ci] is not None:assert all(x&~y==0 for x,y in zip(w,v[targets[ci]]))
    result=dict(K=K,pops=n,seconds=time.monotonic()-t,excluded=excluded,values=v)
    (Path(__file__).parent/f'value-analysis-{K}.json').write_text(json.dumps(result))
    print({k:result[k] for k in result if k!='values'},flush=True)

if __name__=='__main__':
    for K in map(int,sys.argv[1:] or ['3','4','8','16','32']):calculate(K)
