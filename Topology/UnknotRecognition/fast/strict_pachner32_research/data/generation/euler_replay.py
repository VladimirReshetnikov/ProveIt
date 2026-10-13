"""Fresh verifier-only replay of the three capped negative source queries."""
from hashlib import sha256
import json
from pathlib import Path
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
def pins():return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}
def digest(x):return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def main():
 before=pins();raw=(HERE/'euler-queries.json').read_bytes();query=json.loads(raw);scan=json.loads((HERE/'scan.json').read_bytes())
 assert query['passed'] is True and query['unreturned_calls']==[]
 assert query['scan_file_sha256']==sha256((HERE/'scan.json').read_bytes()).hexdigest()
 assert len(query['records'])==3
 records=[]
 caps={'max_nodes':'nodes_attempted','max_pivots':'lp_pivots','max_anchors':'anchors_tested','max_hitting_subsets':'hitting_subsets_tested','max_ellipsoid_iterations':'lp_ellipsoid_iterations','max_feasibility_calls':'lp_feasibility_calls'}
 for old,r in zip(scan['records'],query['records']):
  assert r['id']==old['id'] and r['source']==old['final_source'];source=r['source'];assert digest(source)==r['source_sha256']
  result=r['result'];assert result['status']=='NO_POSITIVE_EULER';packet=result['certificate']
  assert packet['allowed_types']==[[t,q] for t in range(len(source['tetrahedra'])) for q in range(3)]
  assert verify_euler_branch_tree(source,packet)
  B=sorted({node['tetrahedron'] for node in packet['nodes'] if node['kind']=='split'})
  assert B==result['resolving_set']
  for cap,field in caps.items():assert type(result['stats'][field]) is int and 0<=result['stats'][field]<=query['config'][cap]
  records.append(dict(id=r['id'],tetrahedra=r['tetrahedra'],source_sha256=digest(source),negative_full_root_verified=True,h_upper_bound=len(B),resolving_set=B,final_proof_nodes=len(packet['nodes']),nodes_attempted=result['stats']['nodes_attempted'],pivots=result['stats']['lp_pivots']))
 assert before==pins();out=dict(passed=True,query_file_sha256=sha256(raw).hexdigest(),native_sha256=before,records=records,discovery_used=False,native_pins_unchanged=True)
 (HERE/'euler-replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(passed=True,records=records)))
if __name__=='__main__':main()
