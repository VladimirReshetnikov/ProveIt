"""One monitored supplied-source native search, retaining every returned ray."""
import argparse
from copy import deepcopy
import json
from pathlib import Path
from time import monotonic
from fastunknot.diagram import Diagram
from fastunknot.integer_codec import json_safe
from fastunknot.normal_euler_tree import _EulerMaskOracle
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.positive_ray import extract_positive_ray
from fastunknot.normal_crushing import crush_normal_ray
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from prepare import HERE,pins,digest


def main():
 p=argparse.ArgumentParser();p.add_argument('case');p.add_argument('--seconds',type=float,default=20);p.add_argument('--nodes',type=int,default=128);p.add_argument('--pivots',type=int,default=5000);p.add_argument('--anchors',type=int,default=10000);a=p.parse_args()
 path=HERE/(a.case+'-state.json');state=json.loads(path.read_text());source=state['chain']['triangulation'];key=digest(source);before=pins();started=monotonic()
 source_rays=state['raw_rays'].setdefault(key,[]);seen={digest(r['coordinates']) for r in source_rays};counts={'positive_returns':0,'new_rays':0};last_stats={}
 def save():path.write_text(json.dumps(json_safe(state),indent=2)+'\n')
 def check():
  if monotonic()-started>a.seconds:raise TimeoutError('cooperative per-query research ceiling')
 original=_EulerMaskOracle.attempt
 def traced(self,mask):
  last_stats['value']=self.stats
  result=original(self,mask)
  if result['status']=='POSITIVE':
   counts['positive_returns']+=1;d=digest(result['coordinates'])
   if d not in seen:
    seen.add(d);counts['new_rays']+=1
    source_rays.append(dict(coordinates=result['coordinates'],euler_characteristic=result['euler_characteristic'],conflicts=result['conflicts'],mask=[list(x) for x in mask],coordinates_sha256=d,origin='native mask oracle basic point; full-source extremality still requires independent replay'))
  return result
 _EulerMaskOracle.attempt=traced
 config=dict(strategy='envelope',candidate_policy='conflicts',max_nodes=a.nodes,max_pivots=a.pivots,max_anchors=a.anchors,max_hitting_subsets=10000,max_ellipsoid_iterations=10000,max_feasibility_calls=10000)
 attempt=dict(source_sha256=key,tetrahedra=len(source['tetrahedra']),config=config,seconds_ceiling=a.seconds,native_sha256=before)
 state['attempts'].append(attempt);save()
 try:
  result=search_euler_transversal(source,check=check,**config)
  attempt['result']=result;attempt['status']=result['status']
 except TimeoutError as error:
  attempt.update(status='TIMEOUT',reason=str(error),partial_stats=deepcopy(last_stats.get('value',{})))
 finally:_EulerMaskOracle.attempt=original
 attempt['recorded_returns']=counts;attempt['native_pins_unchanged']=pins()==before;save()
 # Each proof below is replayed independently of discovery. Its work is not a
 # timing sample; allow one separately monitored 20-second verification phase.
 started=monotonic()
 if attempt['status']=='POSITIVE_EULER':
  extraction=extract_positive_ray(source,attempt['result']['coordinates'],check=check)
  crushed=crush_normal_ray(source,extraction['coordinates'],check=check)
  chain=deepcopy(state['chain']);chain['steps'].append(crushed['certificate']);chain['triangulation']=crushed['successor'];chain['status']='REDUCED' if crushed['successor'] is not None else 'UNKNOT'
  diagram=Diagram.from_pd(state['input_pd']);assert verify_crushing_chain(diagram,chain,check=check)
  attempt.update(extraction=extraction,crushing=crushed,independent_chain=True)
  state['chain']=chain;state['source_sha256']=digest(chain['triangulation']);state['source_tetrahedra']=len(chain['triangulation']['tetrahedra']) if chain['triangulation'] is not None else 0
  state['stage_sources'][state['source_sha256']]=chain['triangulation'];state['status']='REDUCED'
 elif attempt['status']=='NO_POSITIVE_EULER':
  proof=attempt['result']['certificate'];assert verify_euler_branch_tree(source,proof,check=check)
  certificate=dict(schema='diagram-crushing-recognition-v2',status='KNOTTED',chain=state['chain'],exhaustion=proof)
  assert verify_crushing_recognition(Diagram.from_pd(state['input_pd']),certificate,check=check)
  state.update(status='KNOTTED',certificate=certificate,independent_recognition=True)
  attempt['independent_negative_tree']=True
 save()
 print(dict(case=a.case,status=attempt['status'],input_tetrahedra=attempt['tetrahedra'],current_tetrahedra=state['source_tetrahedra'],rays=len(source_rays),new_rays=counts['new_rays'],state_status=state['status'],pins=attempt['native_pins_unchanged']),flush=True)
 print(attempt.get('result',{}).get('stats',attempt.get('partial_stats')),flush=True)

if __name__=='__main__':main()
