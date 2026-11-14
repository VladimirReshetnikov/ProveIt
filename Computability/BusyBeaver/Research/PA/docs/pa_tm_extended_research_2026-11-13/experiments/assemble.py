from pathlib import Path
exec(Path('joint_anneal.py').read_text().split('meta=(0,0,tuple(range(6)),(0,)*6)')[0])
from functools import lru_cache

def decode(d):
    if 'terminal' in d:return tuple(d['terminal']) if isinstance(d['terminal'],list) else d['terminal']
    rs=d['rules']
    def rec(x):
        if isinstance(x,list):return tuple(x)
        if x in rs:return tuple(rec(y) for y in rs[x])
        return x
    return rec(d['root'])

start=time.time();best=62
import sys
arg=sys.argv[1] if len(sys.argv)>1 else 'transport_candidates.json'
iters=int(sys.argv[2]) if len(sys.argv)>2 else 12000
for cidx,c in enumerate(json.loads(Path(arg).read_text())):
    parts=list(map(decode,c['parts']));n=len(parts);aa=list(map(attrs,parts))
    @lru_cache(None)
    def splits(i,j,b):
        if i+1==j:return (-1,) if aa[i][1]<=b and aa[i][2]<=6 else ()
        if b<=0:return ()
        return tuple(k for k in range(i+1,j) if splits(i,k,b-1) and splits(k,j,6))
    if not splits(0,n,6):print('INFEASIBLE',cidx,flush=True);continue
    def sample(i,j,b):
        if i+1==j:return parts[i]
        kk=splits(i,j,b)
        k=random.choice(kk)
        return sample(i,k,b-1),sample(k,j,6)
    print('CANDIDATE',cidx,'parts',n,c['meta'],flush=True)
    localbest=999
    for it in range(iters):
        t=sample(0,n,6);cc=cost(t)
        if cc[0]<localbest:
            localbest=cc[0]
            print('localbest',cidx,cc[:3],'iter',it,'secs',time.time()-start,flush=True)
            out=encode(t);out['meta']=c['meta'];out['cost']=cc[:3]
            Path(f'{Path(arg).stem}_local_{cidx}.json').write_text(json.dumps(out,indent=2))
        if cc[0]<best:
            best=cc[0]
            print('BEST',best,'raw',cc[1],'folds',cc[2],'candidate',cidx,'iter',it,'secs',time.time()-start,flush=True)
            out=encode(t);out['meta']=c['meta'];out['cost']=cc[:3]
            Path(f'transport_effective_{best}.json').write_text(json.dumps(out,indent=2))
            if best<62:raise SystemExit()
    print('finished',cidx,'best',best,'secs',time.time()-start,flush=True)
