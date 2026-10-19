"""Search coordinated exact-word cut/reparse moves over the fine-atom grammar.

Unlike single rotations, one proposal can replace every private descendant of
a selected grammar word. All routed projections and fixed bootstrap equations
are checked after reconstruction. This is a bounded heuristic, not a global
smallest-grammar decision procedure.
"""
from functools import cache
from pathlib import Path
import argparse,json,random,time
from grammar_model import load
from prepare_fine_search import norm,expansions

HERE=Path(__file__).resolve().parent

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=HERE/'cut-best.json');parser.add_argument('--seed',type=int,default=10);parser.add_argument('--rounds',type=int,default=10);args=parser.parse_args()
    rng=random.Random(args.seed)
    data,original,old,roots,allowed,groups,exprs,orig,atomExpr,locks=load()
    g={norm(w):(norm(a),norm(b)) for w,(a,b) in original.items()}
    old={norm(w):(norm(a),norm(b)) for w,(a,b) in old.items()}
    roots=[norm(w) for w in roots]
    groups=[(q,b,norm(w),[(p,norm(t))for p,t in cs]) for q,b,w,cs in groups]
    routes=[norm(r['word']) for r in data['routes']]
    exprs=[['W',norm(e[1])] if e[0]=='W' else e for e in exprs]
    atoms={expansions[c]:atomExpr[c] for c in atomExpr}
    allowed={expansions[c]:mask for c,mask in allowed.items()}
    locks={norm(w):tuple(norm(t)for t in ts) for w,ts in locks.items()}
    rootsall=set(roots+routes)
    def closure(graph,stop=None):
        out=set();stack=list(rootsall)
        while stack:
            w=stack.pop()
            if w in atoms or w in out or w==stop:continue
            out.add(w);stack.extend(graph[w])
        return out
    def props(graph):
        def join(a,b):return 1+a[0],max(1+a[0],a[1],b[1]),1+max(a[2],b[2])
        @cache
        def wp(w):
            if w in atoms:return ep(atoms[w])
            a,b=graph.get(w,old.get(w));return join(wp(a),wp(b))
        @cache
        def ep(i):
            e=exprs[i]
            return (0,0,0) if e[0]=='L' else wp(e[1]) if e[0]=='W' else join(ep(int(e[1])),ep(int(e[2])))
        return ep(orig),wp
    def valid(graph):
        try:
            for w,ab in locks.items():
                if graph.get(w)!=ab:return False
            for (_,_,_,cs),r in zip(groups,routes):
                for p,t in cs:
                    w=r
                    for b in p:w=graph[w][int(b)]
                    if w!=t:return False
            p,_=props(graph)
            return p[1]<=6 and p[2]<=64
        except (KeyError,RecursionError,TypeError):return False
    def dump(graph,stats):
        p,_=props(graph)
        d=dict(data,status='FINE_ATOM_ROUTING_GRAMMAR_ONLY',rules_count=len(graph),properties=list(p),roots=roots,rules=[[w,*graph[w]]for w in sorted(graph)],routes=[dict(source=q,read=b,word=r)for(q,b,w,cs),r in zip(groups,routes)],cut_reparse=stats)
        args.output.write_text(json.dumps(d,indent=2)+'\n')
    visited=0;improved=0;best=len(g);begin=time.monotonic()
    for roundn in range(args.rounds):
        order=list(g);rng.shuffle(order)
        stats=[]
        p,wp=props(g)
        for q in order:
            if q not in g or q in locks:continue
            outside=closure(g,q)
            removed=len(g)-len(outside)
            if removed<2:continue
            dictionary=outside|set(atoms)
            usable=[]
            for w in dictionary:
                try:pp=wp(w)
                except (KeyError,RecursionError):continue
                if pp[1]<=6:usable.append((w,allowed.get(w,3),pp))
            n=len(q)
            matches=[[]for _ in range(n+1)]
            for w,mask,pp in usable:
                pos=q.find(w)
                while pos>=0:
                    end=pos+len(w)
                    if (pos>0 or mask&1 and pp[0]<6) and (end<n or mask&2):matches[pos].append((end,w,mask,pp))
                    pos=q.find(w,pos+1)
            dist=[10**6]*(n+1);dist[n]=0
            for pos in range(n-1,-1,-1):
                if matches[pos]:dist[pos]=min(1+dist[e]for e,*_ in matches[pos])
            if dist[0]>removed:continue
            # Random tie paths explore alternative reusable tiles with the same
            # minimum segment count; allow one extra tile if still improving.
            stats.append((len(q),removed,dist[0]))
            for rep in range(24):
                tiles=[];pos=0;budget=removed+(rep%3==2)
                while pos<n:
                    opts=[x for x in matches[pos]if 1+dist[x[0]]<=budget-len(tiles)]
                    if not opts:break
                    x=rng.choice(opts);end,w,mask,pp=x;tiles.append((w,mask,pp));pos=end
                if pos<n:continue
                m=len(tiles)
                # Per interval keep the shallowest binary parse at each exact
                # leading-zero count. Each chosen implementation is concrete.
                dp={}
                for i,(w,mask,pp) in enumerate(tiles):dp[i,i+1]={pp[0]:(pp[2],w,None,mask)}
                for size in range(2,m+1):
                    for i in range(m-size+1):
                        j=i+size;out={};word=''.join(t[0]for t in tiles[i:j])
                        for k in range(i+1,j):
                            for lead,(depth,a,ta,ma) in dp[i,k].items():
                                if not ma&1 or lead>=6:continue
                                for rb,(rd,b,tb,mb) in dp[k,j].items():
                                    if not mb&2:continue
                                    nd=1+max(depth,rd);nl=lead+1
                                    if nd<=64 and (nl not in out or nd<out[nl][0]):out[nl]=(nd,word,(a,b,ta,tb),3)
                        dp[i,j]=out
                candidates=list(dp[0,m].values());rng.shuffle(candidates)
                for depth,w,tree,mask in candidates:
                    if tree is None:continue
                    ng={w:g[w]for w in outside}
                    def install(w,tree):
                        if tree is None:return
                        a,b,ta,tb=tree
                        if w in atoms:return
                        if w not in ng:ng[w]=(a,b)
                        install(a,ta);install(b,tb)
                    install(q,tree)
                    try:live=closure(ng);ng={w:ng[w]for w in live}
                    except KeyError:continue
                    visited+=1
                    if len(ng)<=len(g) and valid(ng):
                        g=ng;p,wp=props(g)
                        if len(g)<best:
                            improved+=1;best=len(g);dump(g,dict(round=roundn,visited=visited,seed=args.seed,seconds=time.monotonic()-begin,removed=removed,tiles=m));print('BEST',best,'round',roundn,'visited',visited,'time',time.monotonic()-begin,flush=True)
                            if best<=127:return
                        break
        print('ROUND',roundn,'best',best,'proposals',visited,'zones',len(stats),'elapsed',round(time.monotonic()-begin,3),flush=True)
    dump(g,dict(rounds=args.rounds,visited=visited,seed=args.seed,seconds=time.monotonic()-begin,improved=improved))

if __name__=='__main__':main()
