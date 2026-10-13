"""Check the exact graph-domination reduction on all simple graphs up to 5 vertices."""
import itertools as it
import json
from pathlib import Path
from private_cocore import compile_program, build_atlas, query_atlas
checks=graphs=0
for v in range(6):
    possible=list(it.combinations(range(v),2))
    for bits in it.product((0,1),repeat=len(possible)):
        edges=[e for e,bit in zip(possible,bits) if bit]
        rows=[{} for _ in range(v)]
        neighbors=[set() for _ in range(v)]
        for h,(u,w) in enumerate(edges):
            rows[u][h]=rows[w][h]=1
            neighbors[u].add(w); neighbors[w].add(u)
        atlas=build_atlas(compile_program([],len(edges),[]),rows,v)
        for size in range(v+1):
            for ds in it.combinations(range(v),size):
                d=set(ds)
                dominates=all(i in d or bool(neighbors[i]&d) for i in range(v))
                private=query_atlas(atlas,d)
                succeeds=all(i in d or h>=0 for i,h in enumerate(private))
                assert dominates==succeeds
                checks+=1
        graphs+=1
result={'graphs':graphs,'graph_deletion_pairs':checks,'maximum_vertices':5,'status':'PASS'}
Path('data/domination-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(result)
