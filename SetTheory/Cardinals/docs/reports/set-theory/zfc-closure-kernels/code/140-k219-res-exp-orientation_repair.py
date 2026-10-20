#!/usr/bin/env python3
"""Recompress independently oriented postfix emitters over closed atoms.

RePair here is an exploratory heuristic.  Every chosen binary concatenation
is closed, and the exact complete CFG is compared with the oriented source
after generation.  No state-count or runtime claim follows from a score.
"""
import argparse,collections,itertools,json,random,sys,time
from functools import cache
from pathlib import Path
import orientation_postfix as o
z=o.z
from nonlocal_reassociate import Dag

OUT=z.ROOT/'research_calculus/generated/orientation_repair'

def trial(mask,seed,budget=4):
    d=Dag();baseline=d.intern(z.TREE)
    outside=o.splice(z.TREE,135,4563,None)
    outsideid=d.intern(outside)
    word=sum((o.postfix(f,mask)for f in o.FORMULAS),[])
    seq=[d.intern(a)for m in word for a in o.atoms(o.M[m])]
    available=d.reach(outsideid)
    for a in seq:available.update(d.reach(a))
    rng=random.Random(seed);spans=list(range(len(seq)))
    while len(seq)>1:
        counts=collections.Counter(zip(seq,seq[1:]));ranks=[]
        for p,ct in counts.items():
            a,b=p
            if 1+d.leading[a]>6:continue
            q=d.index.get(p)
            cost=0 if q in available else 1
            # Prefer existing source grammar ties, with a small reproducible
            # random tie bias.  All actual costs are measured after parsing.
            score=ct-cost+(.05 if q is not None else 0)+rng.random()*.8
            ranks.append((score,p))
        ranks.sort(reverse=True)
        applied=False
        for _,p in ranks:
            a,b=p
            new=[];ns=[];i=0;used=0
            while i<len(seq):
                allowed=(i!=0 or len(seq)==2) and (i+2==len(seq) or 1+d.leading[a]<6)
                if i+1<len(seq)and(seq[i],seq[i+1])==p and allowed and(not(i==0)or 1+d.leading[a]<=budget):
                    q=d.add(p);new.append(q);ns.append(spans[i]);used+=1;i+=2
                else:new.append(seq[i]);ns.append(spans[i]);i+=1
            if used:
                available.add(q);seq,spans=new,ns;applied=True;break
        if not applied:return None
    ax=d.tree(seq[0]);tree=o.extra_commands(o.splice(z.TREE,135,4563,ax),mask)
    return tree

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--trials',type=int,default=100)
    ap.add_argument('--only',default=None);ap.add_argument('--out',type=Path,default=OUT)
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    summary=[];start=time.monotonic()
    for bits in itertools.product([False,True],repeat=4):
        mask={op for op,yes in zip('IQER',bits)if yes}
        name=''.join(op if op in mask else '-'for op in'IQER')
        if args.only is not None and args.only!=name:continue
        best=999;besttree=None;bestseed=None;hist=collections.Counter()
        for seed in range(args.trials):
            tree=trial(mask,seed,4 if seed%2 else 3)
            if tree is None:continue
            met=z.s.metrics(tree);score=met['dag_nodes'];hist[score,met['maximum_zero_run']]+=1
            if met['maximum_zero_run']>6:continue
            if score<best:
                best=score;besttree=tree;bestseed=seed
                print('BEST',name,seed,met,'seconds',round(time.monotonic()-start,1),flush=True)
        result=dict(name=name,best_nodes=best,bestseed=bestseed,trials=args.trials,
                    histogram=[[a,b,n]for(a,b),n in sorted(hist.items())])
        if besttree is not None:
            dest=args.out/name;dest.mkdir(exist_ok=True);sites=z.s.sites(besttree)
            ref,words=o.make(mask);rr=z.s.sites(ref)
            assert z.flat(besttree)==z.flat(ref)
            graph=z.s.graph_arithmetic(sites)[0]
            assert graph==z.s.graph_intervals(sites)==z.s.graph_arithmetic(rr)[0]
            result['metrics']=z.s.metrics(besttree)
            (dest/'sites.json').write_bytes(z.s.compact(sites))
            try:
                table,m=z.compile_tree(z.T,z.TREE,besttree);result['compiler']=m
                (dest/'candidate.tm').write_bytes(z.b.table_bytes(table))
            except Exception as e:result['compile_error']=repr(e)
            (dest/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
        summary.append(result);print('MASK',json.dumps(result),flush=True)
    (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')

if __name__=='__main__':main()
