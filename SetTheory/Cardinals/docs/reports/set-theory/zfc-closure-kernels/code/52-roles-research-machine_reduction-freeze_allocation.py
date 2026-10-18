"""Reproduce the frozen unweighted seed-0 static allocation, without a search."""
from pathlib import Path
import json
import static_coalescing as c
ROOT=Path(__file__).parent
seen,edges,masks,variables,uf,adj,copies=c.graph()
result,colors=c.coalesce(adj,copies,mode='optimistic',seed=0)
assert result['accepted']==596 and result['colors']==9
summary=dict(sites=len(seen),edges=sum(map(len,edges.values())),variables=len(variables),ranges=len(adj),interference_edges=sum(map(len,adj.values()))//2,candidate_copies=len(copies),copy_conflicts=sum(b in adj[a] for _,a,b,_,_ in copies))
data=dict(summary=summary,best=result,allocation={str(site):[colors[uf.find(variables[site,r])] if (site,r) in variables else None for r in range(9)] for site in sorted(seen)},frozen_variant='unweighted optimistic seed0:598 total erasedmoves;917DAGnodes expected')
(ROOT/'static-coalescing.json').write_text(json.dumps(data))
print({k:v for k,v in result.items() if k not in ('accepted_sites','rejections')})
