"""Solver-free replay of initial chains and all supplied Pachner packets."""
from hashlib import sha256
import json
from pathlib import Path
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare,_EDGES,NormalOrbitError
from fastunknot.pachner32_verify import verify_pachner_32

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
def digest(x):return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def pins():return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}
def edge_candidates(source):
 p=_prepare(source,lambda:None);classes={}
 for i,key in enumerate(p['edge_roots']):classes.setdefault(key,[]).append(i)
 boundary={p['edge_roots'][6*t+i] for t,f in p['boundary_faces'] for i,e in enumerate(_EDGES) if f not in e}
 answer=[]
 for key,locals in classes.items():
  if key in boundary or len(locals)!=3 or len({i//6 for i in locals})!=3:continue
  inc=[[i//6,*_EDGES[i%6]] for i in locals];t,a,b=min(inc)
  answer.append(dict(tetrahedron=t,vertices=[a,b],edge_root=key,incidences=inc))
 return sorted(answer,key=lambda c:(c['tetrahedron'],c['vertices']))

def main():
 raw=(HERE/'scan.json').read_bytes();saved=json.loads(raw);before=pins();out=[]
 assert saved['passed'] is True
 for r in saved['records']:
  assert verify_crushing_chain(Diagram.from_pd(r['input_pd']),r['chain'])
  source=r['chain']['triangulation'];assert source==r['initial_source'];assert digest(source)==r['initial_source_sha256']
  assert len(r['rounds'])==len(r['steps'])+1
  for stage,step in zip(r['rounds'],r['steps']):
   assert stage['source_sha256']==digest(source)==step['source_sha256']
   assert stage['eligible_candidates']==edge_candidates(source)
   assert step['candidate']==stage['eligible_candidates'][0]
   assert len(stage['attempts'])==1 and stage['attempts'][0]['status']=='ACCEPTED'
   assert verify_pachner_32(source,step['successor'],step['certificate'])
   assert len(step['successor']['tetrahedra'])==len(source['tetrahedra'])-1
   assert _prepare(step['successor'],lambda:None)['vertices']==1
   source=step['successor'];assert digest(source)==step['successor_sha256']
  assert source==r['final_source'];assert digest(source)==r['final_source_sha256']
  assert r['rounds'][-1]['eligible_candidates']==edge_candidates(source)==[]
  out.append(dict(id=r['id'],trace=r['tetrahedron_trace'],moves=len(r['steps']),terminal_eligible_edges=0))
 # The existing checker catches a caller NormalOrbitError raised during source
 # preparation. Retain an explicit old-interface control for the wrapper design.
 r=saved['records'][0];step=r['steps'][0];calls=[0];error=NormalOrbitError('caller identity control')
 def check():
  calls[0]+=1
  if calls[0]==2:raise error
 swallowed=verify_pachner_32(r['initial_source'],step['successor'],step['certificate'],check=check)
 assert swallowed is False
 assert pins()==before
 result=dict(passed=True,scan_sha256=sha256(raw).hexdigest(),native_sha256=before,
             native_pins_unchanged=True,records=out,lp_used=False,producer_called=False,
             legacy_callback_control=dict(exception_class='NormalOrbitError',call=2,returned_false=True,
                 desired_new_contract='propagate original caller exception unchanged'))
 (HERE/'replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(passed=True,records=out,legacy_callback_swallowed=True)))
if __name__=='__main__':main()
