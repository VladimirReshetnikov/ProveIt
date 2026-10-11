"""Observe whether the frozen eager index finishes on three actual diagrams."""
from hashlib import sha256
import json
from pathlib import Path
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from causal_research.cover_oracle import baseline,diagram_cases
from fastunknot import Diagram
old,_=baseline();module=old['pachner_cover_search'];build=module._build_index;records=[]
for name in ('optimized-positive','genus-one-miss','trefoil'):
    source=next(s for s in diagram_cases()if s['name']==name);observed={}
    def track(*args):
        observed['index_completed']=False
        try:
            result=build(*args);observed['index_completed']=True;return result
        finally:observed['index_stats']=dict(args[4])
    with patch.object(module,'_build_index',side_effect=track):
        answer=old['normal_pachner_search'].pachner_seed_decide(Diagram.from_pd(source['pd']),
            max_upward=1,max_region_size=6,max_nodes=1000,max_work=200000,shellings=True,optimize=True)
    assert answer['status']=='INCONCLUSIVE'and observed['index_completed']is False
    records.append(dict(name=name,status=answer['status'],work=answer['work'],**observed))
result=dict(records=records,baseline='ce7fb0737a31636e97859fdde19f18c0e42d486b',
    driver_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
(ROOT/'synthesis/data/cover-oracle-index-probe.json').write_text(json.dumps(result,indent=2)+'\n')
print([(r['name'],r['index_completed'],r['index_stats']['regions_indexed'])for r in records])
