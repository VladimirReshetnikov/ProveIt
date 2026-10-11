from time import perf_counter
from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.boundary_shellings import shell_boundary
from fastunknot.boundary_shellings_verify import verify_boundary_shellings
from fastunknot.normal_cocycle import rank_one_cocycle_seed,_Budget,CocycleLimit,local_coordinates
from fastunknot.cocycle_span import minimize_cocycle_span
from fastunknot.cocycle_gauge import optimize_cocycle_gauge
from fastunknot.cocycle_transport_verify import _check_signed_edges
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.pachner_cover_search import find_pachner_descent
from fastunknot.pachner_cover_verify import inspect_pachner_descent
from fastunknot.normal_disk_kernel import normal_compressing_disk_count
from causal_research.native import diagram_cases
for name in ('optimized-positive','genus-one-miss','survivor-08'):
 source=next(s for s in diagram_cases()if s['name']==name);d=Diagram.from_pd(source['pd'])
 budget=_Budget(lambda:None,2000000);epochs=shell_moves=0;start=perf_counter();status='INCONCLUSIVE'
 try:
  raw=shell_boundary(diagram_exterior(d,check=budget.tick),check=budget.tick)['triangulation']
  seed=rank_one_cocycle_seed(raw,check=budget.tick);h=seed['heights']
  result=minimize_cocycle_span(seed['vertices'],h,check=budget.tick)
  p=dict(zip(result['certificate']['vertex_ids'],result['certificate']['potential']))
  h=[[x+p[v]for x,v in zip(row,vs)]for row,vs in zip(h,seed['vertices'])]
  while True:
   result=normal_compressing_disk_count(raw,[local_coordinates(row)for row in h],record_certificate=True,check=budget.tick)
   if result['status']!='COMPLETE':break
   if result['contains_compressing_disk']:status='CANDIDATE_DISC';break
   step=find_pachner_descent(raw,h,max_upward=1,max_nodes=200,check=budget.tick)
   if step['status']!='DESCENT_FOUND':break
   replay=inspect_pachner_descent(raw,h,step['certificate'],max_upward=1,check=budget.tick);assert replay
   raw=replay['triangulation'];h=replay['heights'];epochs+=1
   shell=shell_boundary(raw,check=budget.tick)
   if shell['moves']:
    assert verify_boundary_shellings(raw,shell['triangulation'],shell['moves'],check=budget.tick)
    removed=set(shell['moves']);h=[row for i,row in enumerate(h)if i not in removed];raw=shell['triangulation'];shell_moves+=len(removed)
    assert _check_signed_edges(_prepare(raw,budget.tick),h,budget.tick)
    print(name,'shell',epochs,len(shell['moves']),'T',len(raw['tetrahedra']),budget.work,flush=True)
   if epochs%4==0:h=optimize_cocycle_gauge(raw,h,check=budget.tick)['heights']
 except CocycleLimit:pass
 print('SUMMARY',name,status,epochs,shell_moves,budget.work,perf_counter()-start,flush=True)
