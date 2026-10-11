from time import perf_counter
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.normal_cocycle import rank_one_cocycle_seed,_Budget,CocycleLimit,local_coordinates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_gauge import optimize_cocycle_gauge
from fastunknot.pachner_cover_search import find_pachner_descent
from fastunknot.pachner_cover_verify import inspect_pachner_descent
from fastunknot.normal_disk_kernel import normal_compressing_disk_count,verify_normal_disk_count_certificate
from fastunknot.sector_residual import search_sector_window
from causal_research.native import diagram_cases
for name in ('optimized-positive','survivor-08'):
 source=next(s for s in diagram_cases()if s['name']==name);d=Diagram.from_pd(source['pd'])
 budget=_Budget(lambda:None,2000000);epochs=queries=0;start=perf_counter();status='INCONCLUSIVE'
 try:
  raw=shell_boundary(diagram_exterior(d,check=budget.tick),check=budget.tick)['triangulation']
  seed=rank_one_cocycle_seed(raw,check=budget.tick);h=seed['heights']
  result=minimize_cocycle_span(seed['vertices'],h,check=budget.tick)
  p=dict(zip(result['certificate']['vertex_ids'],result['certificate']['potential']))
  h=[[x+p[v]for x,v in zip(row,vs)]for row,vs in zip(h,seed['vertices'])]
  while True:
   coordinates=[local_coordinates(row)for row in h]
   count=normal_compressing_disk_count(raw,coordinates,record_certificate=True,check=budget.tick)
   if count['status']!='COMPLETE':break
   if count['contains_compressing_disk']:status='COHERENT_DISC';break
   if epochs%4==0:
    stats={};queries+=1
    candidate=search_sector_window(raw,coordinates,radius=2,stats=stats,check=budget.tick)
    print(name,'window',epochs,stats.get('sectors_queried'),stats.get('rays'),budget.work,flush=True)
    if candidate['status']=='DISC_FOUND':
     assert verify_normal_disk_count_certificate(raw,candidate['coordinates'],candidate['disc_certificate'])
     status='WINDOW_DISC';break
   step=find_pachner_descent(raw,h,max_upward=1,max_nodes=200,check=budget.tick)
   if step['status']!='DESCENT_FOUND':break
   replay=inspect_pachner_descent(raw,h,step['certificate'],max_upward=1,check=budget.tick);assert replay
   raw=replay['triangulation'];h=replay['heights'];epochs+=1
   if epochs%4==0:h=optimize_cocycle_gauge(raw,h,check=budget.tick)['heights']
 except CocycleLimit:pass
 print('SUMMARY',name,status,epochs,queries,budget.work,perf_counter()-start,flush=True)
