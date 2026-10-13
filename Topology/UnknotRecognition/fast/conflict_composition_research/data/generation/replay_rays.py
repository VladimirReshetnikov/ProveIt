"""Solver-free source authentication, original STANDARD ranks, and packing."""
import argparse
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
import json
from time import monotonic
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from boundary_transversal_research.replay import observation
from prepare import HERE,pins,digest
from fixtures import BASES, slot_preserving_edge_map
from fastunknot.interlace import visible_factors_interlacement, verify_interlacement_certificate


def packing(edges,check):
 edges=tuple(sorted(set(tuple(x) for x in edges),key=lambda x:(len(x),x)))
 masks=tuple(sum(1<<j for j in edge) for edge in edges)
 @lru_cache(None)
 def solve(available):
  check()
  if not available:return ()
  i,*tail=available
  without=solve(tuple(tail));with_i=(i,)+solve(tuple(j for j in tail if not masks[i]&masks[j]))
  return with_i if len(with_i)>len(without) else without
 return [list(edges[i]) for i in solve(tuple(range(len(edges))))]


def hitting(edges,check):
 edges=tuple(sorted(set(tuple(x) for x in edges),key=lambda x:(len(x),x)))
 def search(chosen,left):
  check();remaining=[e for e in edges if chosen.isdisjoint(e)]
  if not remaining:return sorted(chosen)
  if left==0:return None
  for v in remaining[0]:
   answer=search(chosen|{v},left-1)
   if answer is not None:return answer
  return None
 for k in range(len(edges)+1):
  answer=search(frozenset(),k)
  if answer is not None:return answer


def main():
 p=argparse.ArgumentParser();p.add_argument('case');p.add_argument('--seconds',type=float,default=20);a=p.parse_args();path=HERE/(a.case+'-state.json');state=json.loads(path.read_text());started=monotonic();before=pins()
 def check():
  if monotonic()-started>a.seconds:raise TimeoutError('cooperative replay ceiling')
 fixture_path=HERE/'fixtures.json';fixtures=json.loads(fixture_path.read_text());fixture=next(r for r in fixtures['records'] if r['id']==a.case)
 diagram=Diagram.from_pd(state['input_pd']);assert fixture['pd']==state['input_pd'];assert fixture['pd_sha256']==digest(diagram.pd)
 factors,cert=visible_factors_interlacement(diagram);assert cert==fixture['factor_certificate'];assert verify_interlacement_certificate([dart//4 for dart in diagram.traversal()],cert)
 assert len(factors)==len(fixture['factors'])
 for factor,expected in zip(factors,fixture['factors']):
  assert [list(r) for r in factor.pd]==expected['factor_pd'];assert slot_preserving_edge_map(Diagram.from_braid(*BASES[expected['base']]),factor)==expected['base_edge_to_factor_edge']
 assert verify_crushing_chain(diagram,state['chain'],check=check)
 authenticated={digest(state['chain']['shelling']['triangulation'])}
 authenticated.update(digest(step['successor']) for step in state['chain']['steps'])
 result=dict(case=a.case,native_sha256=before,state_sha256=digest(state),chain_verified=True,diagram_factor_certificate_verified=True,factor_fixture_sha256=digest(fixtures),factor_ids=[r['base'] for r in fixture['factors']],records=[])
 for key,rays in state['raw_rays'].items():
  check();assert key in authenticated;source=state['stage_sources'][key];assert digest(source)==key
  record=dict(source_sha256=key,tetrahedra=len(source['tetrahedra']),witnesses=[],negative_cone_verified=False)
  edges=[]
  for index,ray in enumerate(rays):
   check();obs,rank=observation(source,ray['coordinates']);assert obs['canonical_euler']==ray['euler_characteristic']>0;assert obs['conflicts']==ray['conflicts']
   record['witnesses'].append(dict(index=index,coordinates_sha256=digest(ray['coordinates']),observation=obs,rank_proof=rank))
   if obs['conflicts']:edges.append(obs['conflicts'])
  record['disjoint_conflicts']=packing(edges,check)
  record['packing_lower_bound']=len(record['disjoint_conflicts'])
  record['minimum_known_conflict_hitting_set']=hitting(edges,check)
  record['known_hypergraph_lower_bound']=len(record['minimum_known_conflict_hitting_set'])
  lower=record['known_hypergraph_lower_bound'];universe=list(range(len(source['tetrahedra'])));excluded=0;coverage=sha256();counts=[0]*len(edges)
  if lower:
   for candidate in combinations(universe,lower-1):
    check();miss=next(i for i,edge in enumerate(edges) if set(candidate).isdisjoint(edge));excluded+=1;counts[miss]+=1;coverage.update((str(candidate)+':'+str(miss)+'\n').encode())
  assert all(not set(record['minimum_known_conflict_hitting_set']).isdisjoint(edge) for edge in edges)
  record['independent_smaller_subset_exclusions']=excluded
  record['smaller_subset_first_disjoint_witness_counts']=counts
  record['smaller_subset_coverage_sha256']=coverage.hexdigest()
  record['conflict_vertex_universe']=universe
  record['has_retained_compatible_positive']=any(not r['conflicts'] for r in rays)
  if state.get('independent_recognition') and digest(state['chain']['triangulation'])==key:
   assert verify_crushing_recognition(Diagram.from_pd(state['input_pd']),state['certificate'],check=check)
   record['negative_cone_verified']=True
   B=sorted({node['tetrahedron'] for node in state['certificate']['exhaustion']['nodes'] if node['kind']=='split'})
   record['resolving_set']=B;record['h_upper_bound']=len(B)
   if len(B)==record['known_hypergraph_lower_bound']:record['exact_h']=len(B)
  result['records'].append(record)
 result['native_pins_unchanged']=pins()==before;result['passed']=True
 (HERE/(a.case+'-ray-replay.json')).write_text(json.dumps(result,indent=2)+'\n')
 for r in result['records']:print({k:r[k] for k in r if k!='witnesses'},flush=True)

if __name__=='__main__':main()
