from unittest.mock import patch
from time import perf_counter
from hashlib import sha256
import json
from fastunknot import Diagram
from fastunknot.pachner_epochs import pachner_epoch_seed_decide
from fastunknot.normal_transport_verify import verify_transport_disk_certificate
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.cocycle_lex import _prepared_minimize_edge_span
from fastunknot.cocycle_gauge_verify import verify_cocycle_gauge
from causal_research.native import diagram_cases
import fastunknot.pachner_epochs as epochs

def edge_gauge(raw,h,*,check):
 p=_prepare(raw,check);result=_prepared_minimize_edge_span(p,h,None,check)
 labels=result['certificate']['vertex_ids'];potential=dict(zip(labels,result['potential']))
 rows=[]
 for t,row in enumerate(h):
  shifted=[row[j]+potential[p['vertex_roots'][4*t+j]]for j in range(4)]
  rows.append([x-shifted[0]for x in shifted])
 proof=dict(schema='cocycle-vertex-gauge-v1',source_sha256=sha256(json.dumps(raw,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
  potential=[[v,potential[v]]for v in sorted(potential)],heights=rows)
 assert verify_cocycle_gauge(raw,h,proof,check=check)
 original=[[x-row[0]for x in row]for row in h]
 return dict(heights=rows,certificate=proof,changed=rows!=original,stats=result['stats'])

for name in ('optimized-positive','genus-one-miss','survivor-08'):
 source=next(s for s in diagram_cases()if s['name']==name);d=Diagram.from_pd(source['pd']);start=perf_counter()
 with patch.object(epochs,'optimize_cocycle_gauge',side_effect=edge_gauge):
  r=pachner_epoch_seed_decide(d,shellings=True,optimize=True,max_epochs=64,regauge_interval=4,max_work=2000000)
 if r['status']=='UNKNOT':assert source['expected']=='UNKNOT'and verify_transport_disk_certificate(d,r['certificate'])
 print(name,r['status'],r['work'],r['stats']['epochs'],r['stats']['gauge_queries'],r['stats']['gauge_changes'],perf_counter()-start,flush=True)
