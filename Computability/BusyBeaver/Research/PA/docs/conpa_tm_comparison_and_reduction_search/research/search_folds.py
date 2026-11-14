#!/usr/bin/env python3
"""Sound finite-window reachability and local state-fold search (scratch)."""
from pathlib import Path
from collections import deque,defaultdict
import itertools,json,time

BASE=Path(__file__).resolve().parents[1]

def read_table(path):
    rows={}
    for ln in Path(path).read_text().splitlines():
        if not ln.strip() or ln.startswith('#'):continue
        q,b,w,d,n=ln.split()
        rows[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
    return rows

def reachable(rows,k=3,start=0,all_tapes=False):
    """Window integer's bit i represents tape cell i-k."""
    n=max(q for q,b in rows)+1
    width=2*k+1; full=(1<<width)-1; mid=1<<k; high=1<<(width-1)
    reach=[set() for _ in range(n+1)]
    reach[start]=set(range(1<<width)) if all_tapes else {0}
    todo=deque((start,v) for v in reach[start])
    while todo:
        q,v=todo.popleft()
        if (q,(v>>k)&1) not in rows:continue
        w,d,t=rows[q,(v>>k)&1]
        u=v&~mid | (w<<k)
        if d==1: u=u>>1; variants=(u,u|high)
        else: u=(u<<1)&full; variants=(u,u|1)
        for z in variants:
            if z not in reach[t]:
                reach[t].add(z);todo.append((t,z))
    return reach

def local_check(rows,a,b,replacements,reach,k=3,limit=25,branches=(0,1),forbid=None):
    """Check all abstract windows at merged states without reading outside.
    Original one step is simulated in 1..limit new steps. All tape writes
    and head changes are compared literally. Target state b is renamed a.
    """
    mp=lambda q:a if q==b else q
    def delta(q,x):
        w,d,t=replacements.get((q,x),rows[q,x])
        return w,d,mp(t)
    lengths=defaultdict(set)
    for q in (a,b):
      for v in reach[q]:
        tape={i-k:(v>>i)&1 for i in range(2*k+1)}
        old=tape.copy();read=old[0]
        if read not in branches:continue
        w,d,t=rows[q,read];old[0]=w;t=mp(t)
        nq=mp(q);h=0
        for step in range(1,limit+1):
            if h not in tape or (nq,tape[h]) not in rows:return None
            if forbid is not None and (nq,tape[h])==forbid:return None
            w,nd,nq=delta(nq,tape[h]);tape[h]=w;h+=nd
            if nq==t and h==d and tape==old:
                lengths[q,read].add(step);break
        else:return None
    return {str(key):sorted(v) for key,v in lengths.items()}

def search(rows,reach,k=3):
    """Try preserving common branches and replacing others with left detours."""
    n=len(reach)-1
    pairs=[]
    for a in range(1,n):
      for b in range(a+1,n):
        differences=[x for x in (0,1) if rows[a,x]!=rows[b,x]]
        if len(differences)>1:continue
        if not differences:
            pairs.append((a,b,{},'identical'));continue
        x=differences[0]
        # Unchanged common branch plus a return-to-history branch.
        prev_a={((v>>(k-1))&1) for v in reach[a] if ((v>>k)&1)==x}
        prev_b={((v>>(k-1))&1) for v in reach[b] if ((v>>k)&1)==x}
        # cheap candidate selection; allow long paths afterwards
        for aa,bb in ((a,b),(b,a)):
          for helper,w,d in itertools.product(range(n),(x,1-x),(-1,1)):
            if helper == bb:continue
            repl={(aa,x):(w,d,helper)}
            lens=local_check(rows,aa,bb,repl,reach,k)
            if lens:
                result={'a':aa,'b':bb,'symbol':x,'helper':helper,'write':w,'move':d,'lengths':lens,'prev_a':sorted(prev_a),'prev_b':sorted(prev_b)}
                print(json.dumps(result),flush=True);pairs.append(result)
    return pairs

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--k',type=int,default=3);args=ap.parse_args()
    rows=read_table(BASE/'sources/bb196/data/pa196.tm')
    t=time.time();reach=reachable(rows,args.k)
    print('reach',sum(map(len,reach)),'seconds',time.time()-t,flush=True)
    print('restricted',[ (q,len(v)) for q,v in enumerate(reach) if len(v)<2**(2*args.k+1)],flush=True)
    found=search(rows,reach,args.k)
    (BASE/'research/folds.json').write_text(json.dumps(found,indent=2))
    (BASE/'research/reach.json').write_text(json.dumps({'k':args.k,'windows':[sorted(v) for v in reach]}))
    print('DONE',len(found),time.time()-t,flush=True)
