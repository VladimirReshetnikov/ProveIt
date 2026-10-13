"""One capped native Euler query per retained strict32 terminal source."""
from hashlib import sha256
import json
from pathlib import Path
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from conflict_composition_research.standard import observation
from fastunknot.integer_codec import json_safe

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
def pins():return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}
def digest(x):return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
CONFIG=dict(strategy='envelope',candidate_policy='conflicts',max_nodes=256,
            max_pivots=10000,max_anchors=10000,max_hitting_subsets=10000,
            lp_policy='polynomial',lp_fast_path_pivots=None,
            max_ellipsoid_iterations=10000,max_feasibility_calls=10000)

def verify(source,result):
 status=result['status']
 if status=='NO_POSITIVE_EULER':
  packet=result['certificate']
  assert packet['allowed_types']==[[t,q] for t in range(len(source['tetrahedra'])) for q in range(3)]
  assert verify_euler_branch_tree(source,packet)
  return dict(status=status,negative_full_root_verified=True,
              complete_proof_nodes=len(packet['nodes']),resolving_set=result['resolving_set'])
 if status=='POSITIVE_EULER':
  obs,ranks=observation(source,result['coordinates'])
  assert obs['canonical_euler']==result['euler_characteristic']>0 and obs['conflicts']==[]
  return dict(status=status,positive_canonical_admissible_root_verified=True,
              observation=obs,rank_proof=ranks)
 assert status=='INCONCLUSIVE'
 assert type(result['reason']) is str
 return dict(status=status,complete_cone_result_verified=False,reason=result['reason'])

def main():
 path=HERE/'scan.json';raw=path.read_bytes();scan=json.loads(raw);before=pins()
 out=dict(schema='scratch-pachner32-euler-queries-v1',passed=False,native_sha256=before,
          scan_file_sha256=sha256(raw).hexdigest(),config=CONFIG,records=[],unreturned_calls=[],
          wall_limit_seconds=None,scope='One capped supplied-source query per terminal successor; no full maintained v3 recognition packet or h monotonicity claim.')
 for item in scan['records']:
  source=item['final_source']
  try:result=search_euler_transversal(source,**CONFIG)
  except BaseException as error:
   out['unreturned_calls'].append(dict(id=item['id'],error_type=type(error).__name__,work_complete=False))
   (HERE/'euler-queries.json').write_text(json.dumps(json_safe(out),separators=(',',':'))+'\n');raise
  replay=verify(source,result)
  out['records'].append(dict(id=item['id'],source=source,source_sha256=digest(source),
      tetrahedra=len(source['tetrahedra']),result=result,replay=replay))
  assert pins()==before
  (HERE/'euler-queries.json').write_text(json.dumps(json_safe(out),separators=(',',':'))+'\n')
  print(item['id'],len(source['tetrahedra']),result['status'],result['stats'],replay,flush=True)
 out['passed']=True;out['native_pins_unchanged']=True
 (HERE/'euler-queries.json').write_text(json.dumps(json_safe(out),separators=(',',':'))+'\n')
if __name__=='__main__':main()
