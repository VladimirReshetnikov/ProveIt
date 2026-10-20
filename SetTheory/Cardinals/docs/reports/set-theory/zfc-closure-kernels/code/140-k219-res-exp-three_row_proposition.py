#!/usr/bin/env python3
"""Measure safe three-variable replacements for the fourth-field rho8 row.

The replacements are standard complete propositional bases.  This is a
source-size experiment: no successful finite screen is itself a correctness
proof for the resulting enumerator or Turing table.
"""
import argparse,collections,itertools,json,sys,time
from pathlib import Path
import orientation_postfix as o
z=o.z
I,N=o.I,o.N
a,b,c='a','b','c'
K=I(a,I(b,a))
S=I(I(a,I(b,c)),I(I(a,b),I(a,c)))
P=I(I(I(a,b),a),a)
B=I(I(a,b),I(I(b,c),I(a,c)))
D=I(N(N(a)),a)
BASES={'KSP':[K,S,P],'KBP':[K,B,P],'KSD':[K,S,D]}

def rename(t,ren):
    if not isinstance(t,tuple):return ren.get(t,t)
    return(t[0],rename(t[1],ren),rename(t[2],ren))

def combine(ts,shape):
    if len(ts)==1:return ts[0]
    if shape=='right':return(ts[0],combine(ts[1:],shape))
    if shape=='left':return(combine(ts[:-1],shape),ts[-1])
    n=len(ts)//2;return(combine(ts[:n],shape),combine(ts[n:],shape))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=z.ROOT/'research_calculus/generated/three_row_proposition')
    ap.add_argument('--retain',type=int,default=16);args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    perms=list(itertools.permutations('abc'));summary=[];kept=[];hist=collections.Counter();start=time.monotonic()
    for basis,forms in BASES.items():
        best=999;nt=0
        for pp in itertools.product(perms,repeat=3):
            fs=[rename(f,dict(zip('abc',p)))for f,p in zip(forms,pp)]
            for order in itertools.permutations(range(3)):
                words=[o.postfix(fs[i],set())for i in order]
                for shape in ['right','left','balanced']:
                    blocks=[combine([o.M[m]for m in w],shape)for w in words]
                    new=combine(blocks,shape);tree=o.splice(z.TREE,135,486,new)
                    met=z.s.metrics(tree);score=met['dag_nodes'];nt+=1;hist[basis,score,met['maximum_zero_run']]+=1
                    if score<best:
                        best=score;print('BEST',basis,pp,order,shape,met,'seconds',round(time.monotonic()-start,2),flush=True)
                    if met['maximum_zero_run']<=6:
                        info=dict(basis=basis,permutations=pp,order=order,shape=shape,source_metrics=met,postfix=words,
                                  old_stack_output_count=10,new_stack_output_count=12,removed_fourth_field=True)
                        key=(score,met['maximum_depth'])
                        if len(kept)<args.retain or key<kept[-1][0]:
                            kept.append((key,info,tree));kept.sort(key=lambda x:x[0]);kept=kept[:args.retain]
        summary.append(dict(basis=basis,best_dag_nodes=best,trials=nt))
    for ix,(key,info,tree)in enumerate(kept):
        dest=args.out/f'candidate{ix:03d}';dest.mkdir(exist_ok=True);sites=z.s.sites(tree)
        assert z.s.graph_arithmetic(sites)[0]==z.s.graph_intervals(sites)
        (dest/'sites.json').write_bytes(z.s.compact(sites))
        try:
            table,m=z.compile_tree(z.T,z.TREE,tree);info['compiler']=m
            (dest/'candidate.tm').write_bytes(z.b.table_bytes(table))
        except Exception as e:info['compile_error']=repr(e)
        (dest/'receipt.json').write_text(json.dumps(info,indent=2)+'\n')
        print('RETAIN',ix,json.dumps(info),flush=True)
    (args.out/'summary.json').write_text(json.dumps(dict(summary=summary,histogram=[[a,b,c,n]for(a,b,c),n in sorted(hist.items())]),indent=2)+'\n')

if __name__=='__main__':main()
