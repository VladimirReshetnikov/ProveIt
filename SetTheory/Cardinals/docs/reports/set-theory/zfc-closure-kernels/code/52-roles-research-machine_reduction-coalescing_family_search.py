"""Measure shared-DAG cost, not copy count, for selective coalescing families."""
from pathlib import Path
from collections import Counter,defaultdict
import json,time,random,itertools
import dynamic_renaming as d
import static_coalescing as c
ROOT=Path(__file__).parent
seen,edges,masks,variables,uf,adj,copies=c.graph()
weights={q:Counter() for q in adj}
for (site,r),v in variables.items():weights[uf.find(v)][r]+=1
families=sorted({(r,t) for _,_,_,r,t in copies})

def evaluate(selected):
    chosen=[x for x in copies if (x[3],x[4]) in selected]
    result,colors=c.coalesce(adj,chosen,weights=weights)
    allocation={site:[colors[uf.find(variables[site,r])] if (site,r) in variables else None for r in range(9)] for site in seen}
    recipes={};counts=Counter()
    for site,out in edges.items():
        dst,kind=out[0] if out else (None,None)
        if kind is None:continue
        if kind[0]=='move':
            r,t=kind[1:];a=allocation[site][r];b=allocation[dst][t]
            recipes[site]=('erase',) if a is None or b is None or a==b else ('move',a,b)
            counts[recipes[site][0]]+=1
        else:
            _,_,op,r,z=d.cases[kind[1]]
            if op=='CI':recipes[site]=('I',allocation[site][r] if allocation[site][r] is not None else allocation[dst][r])
            elif op=='CD':
                color=allocation[site][r]
                if color is None:
                    free=set(range(9))-set(allocation[site]);color=r if r in free else min(free)
                recipes[site]=('D',color)
    nodes={};intern={}
    def node(a,b):
        pair=(a,b)
        if pair not in intern:
            n=len(nodes);nodes[n]=pair;intern[pair]=n
        return ('N',intern[pair])
    def emit(n,path):
        if (site:=d.lookup.get(path+'0')) in d.swaps:
            rec=recipes[site]
            if rec[0]=='erase':return ('B',0)
            _,a,b=rec
            return node(('D',a),node(('I',b),('C',2)))
        pair=[]
        for bit,e in enumerate(d.dag['nodes'][str(n)]):
            p=path+str(bit)
            if e[0]=='N':pair.append(emit(e[1],p))
            elif e[0] in 'ID':pair.append(recipes.get(d.lookup[p],tuple(e)))
            else:pair.append(tuple(e))
        return node(*pair)
    root=emit(d.dag['root'],'')
    summary=dict(families=sorted(selected),colors=result['colors'],dag_nodes=len(nodes),copies=dict(counts),coalesces=result['accepted'],ranges=result['coalesced_ranges'])
    return summary,allocation,nodes,root

def main():
    allsets=[frozenset()]
    allsets.extend(frozenset(x) for k in (1,2) for x in itertools.combinations(families,k))
    rng=random.Random(0)
    allsets.extend(frozenset(x for x in families if rng.randrange(2)) for _ in range(180))
    allsets.append(frozenset(families));allsets=list(dict.fromkeys(allsets))
    results=[];best=None;start=time.monotonic()
    for i,selected in enumerate(allsets):
        summary,allocation,nodes,root=evaluate(selected);results.append(summary)
        key=(summary['colors']>9,summary['dag_nodes'],-summary['copies']['erase'])
        if best is None or key<best[0]:
            best=(key,summary,allocation,nodes,root)
            print('best',i,summary,flush=True)
        if i%40==0:print('progress',i,len(allsets),time.monotonic()-start,flush=True)
    result=dict(seconds=time.monotonic()-start,family_options=families,results=results,best=best[1],allocation=best[2],nodes=best[3],root=best[4])
    (ROOT/'coalescing-family-search.json').write_text(json.dumps(result))
    print('complete',len(allsets),result['seconds'],best[1],flush=True)

if __name__=='__main__':main()
