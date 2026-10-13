"""Resume one explicit resolving-set candidate, retaining source duals and tree.

Research-only scheduling. Partial trees never constitute negative evidence.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from time import monotonic
from fastunknot.diagram import Diagram
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_sector import _assemble_sector_kernel
from fastunknot.normal_euler import _euler_model
from fastunknot.normal_euler_tree import _EulerMaskOracle,_euler_search_stats
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.integer_codec import json_safe
from prepare import HERE,pins,digest


def main():
 p=argparse.ArgumentParser();p.add_argument('case');p.add_argument('--B',required=True);p.add_argument('--seconds',type=float,default=20);p.add_argument('--pivots',type=int,default=10000);p.add_argument('--cache-from');a=p.parse_args()
 B=sorted({int(x) for x in a.B.split(',')});path=HERE/(a.case+'-state.json');state=json.loads(path.read_text());source=state['chain']['triangulation'];key=digest(source);n=len(source['tetrahedra']);full=tuple((t,q) for t in range(n) for q in range(3));before=pins();started=monotonic();deadline=started+a.seconds
 target=HERE/(a.case+'-candidate-'+'-'.join(map(str,B))+'.json')
 if target.exists():job=json.loads(target.read_text());assert job['source_sha256']==key and job['status']=='PAUSED'
 else:job=dict(source_sha256=key,B=B,pending=[[full,0]],nodes=[],phases=[],status='PAUSED')
 if a.cache_from and 'cache' not in job:
  donor=json.loads(Path(a.cache_from).read_text());assert donor['source_sha256']==key
  job['cache']=donor['cache'];job['cycle_rows_sha256']=donor['cycle_rows_sha256'];job['cache_origin']=a.cache_from
 def check():
  if monotonic()>deadline:raise TimeoutError('cooperative candidate phase ceiling')
 prepared=_prepare(source,check);kernel=_assemble_sector_kernel(source,prepared,full,check);linear,weights=_euler_model(kernel,check);stats=_euler_search_stats();stats['kernel_preparations']=1
 oracle=_EulerMaskOracle(source,prepared,strategy='envelope',model='source',max_pivots=a.pivots,max_anchors=10000,check=check,stats=stats,max_ellipsoid_iterations=10000,max_feasibility_calls=10000)
 oracle.source_context=(kernel,linear,weights)
 if 'cache' in job:
  assert job['cycle_rows_sha256']==digest(kernel.cycle_rows)
  oracle.source_cache=[(tuple(Fraction(*p) for p in bound),dual) for bound,dual in job['cache']]
 else:oracle.source_cache=[(tuple(0 for _ in full),[[0,1] for _ in kernel.cycle_rows])]
 phase=dict(native_sha256=before,seconds_ceiling=a.seconds,max_pivots=a.pivots);job['phases'].append(phase)
 rays=state['raw_rays'].setdefault(key,[]);seen={digest(r['coordinates']) for r in rays}
 while job['pending']:
  mask,depth=job['pending'].pop();mask=tuple(tuple(x) for x in mask)
  stats['nodes_attempted']+=1;stats['maximum_depth']=max(stats['maximum_depth'],depth)
  try:answer=oracle.attempt(mask)
  except TimeoutError as error:
   job['pending'].append([mask,depth]);phase['reason']=str(error);break
  if answer['status']=='INCONCLUSIVE':
   job['pending'].append([mask,depth]);phase['reason']=answer['reason'];break
  if answer['status']=='NEGATIVE':
   stats['negative_leaves']+=1;job['nodes'].append(dict(kind='negative',certificate=answer['certificate']));continue
  stats['positive_relaxations']+=1;d=digest(answer['coordinates'])
  if d not in seen:
   seen.add(d);rays.append(dict(coordinates=answer['coordinates'],euler_characteristic=answer['euler_characteristic'],conflicts=answer['conflicts'],coordinates_sha256=d,mask=[list(x) for x in mask],origin='native explicit-candidate mask oracle; independent full-source rank replay pending'))
  if not answer['conflicts']:
   job.update(status='POSITIVE_EULER',positive=answer);break
  stats['incompatible_positive_points']+=1
  choices=sorted(set(B).intersection(answer['conflicts']))
  if not choices:job.update(status='REFUTED',refuter=answer);break
  t=choices[0];qs=[q for tet,q in mask if tet==t];assert len(qs)>1
  job['nodes'].append(dict(kind='split',tetrahedron=t));stats['branch_splits']+=1
  for q in reversed(qs):job['pending'].append([tuple(pair for pair in mask if pair[0]!=t or pair[1]==q),depth+1])
 else:job['status']='NO_POSITIVE_EULER'
 phase['stats']=stats;phase['native_pins_unchanged']=pins()==before
 job['cycle_rows_sha256']=digest(kernel.cycle_rows)
 job['cache']=[([[Fraction(x).numerator,Fraction(x).denominator] for x in bound],dual) for bound,dual in oracle.source_cache]
 if job['status']=='NO_POSITIVE_EULER':
  proof=dict(schema='normal-euler-branch-tree-v1',status='NO_POSITIVE_EULER',source_sha256=key,allowed_types=[list(x) for x in full],nodes=job['nodes'])
  assert verify_euler_branch_tree(source,proof)
  certificate=dict(schema='diagram-crushing-recognition-v2',status='KNOTTED',chain=state['chain'],exhaustion=proof)
  assert verify_crushing_recognition(Diagram.from_pd(state['input_pd']),certificate)
  state.update(status='KNOTTED',certificate=certificate,independent_recognition=True);job['independent_negative_tree']=True
 state['attempts'].append(dict(kind='explicit_candidate',B=B,source_sha256=key,status=job['status'],candidate_file=str(target),phase=phase))
 path.write_text(json.dumps(json_safe(state),indent=2)+'\n');target.write_text(json.dumps(json_safe(job),indent=2)+'\n')
 print(dict(case=a.case,B=B,status=job['status'],nodes=len(job['nodes']),pending=len(job['pending']),rays=len(rays),pins=phase['native_pins_unchanged']),flush=True)
 print(stats,flush=True)
 if 'refuter' in job:print('refuter',job['refuter']['conflicts'],flush=True)
 if 'positive' in job:print('compatible positive Euler',job['positive']['euler_characteristic'],flush=True)

if __name__=='__main__':main()
