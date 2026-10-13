"""Bounded authenticated native preprocessing of visible connected sums."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
from time import monotonic
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.integer_codec import json_safe

HERE=Path(__file__).resolve().parent
FAST=Path.cwd()
CASES={'tt':(3,[1,1,1,2,2,2]),'tf':(4,[1,1,1,2,-3,2,-3]),'ff':(5,[1,-2,1,-2,3,-4,3,-4])}

def pins():
 return {str(p.relative_to(FAST)):sha256(p.read_bytes()).hexdigest() for p in sorted((FAST/'fastunknot').rglob('*.py'))}

def digest(x):
 return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def main():
 p=argparse.ArgumentParser();p.add_argument('case',choices=CASES);p.add_argument('--seconds',type=float,default=20);a=p.parse_args()
 diagram=Diagram.from_braid(*CASES[a.case]);before=pins();started=monotonic()
 record=dict(case=a.case,braid=CASES[a.case],input_pd=[list(r) for r in diagram.pd],native_sha256=before,config=dict(max_tree_nodes=0,max_pivots=0,max_anchors=0,sector_method='transversal',transversal_candidate_policy='conflicts'),attempts=[],raw_rays={})
 def check():
  if monotonic()-started>a.seconds:raise TimeoutError('cooperative preprocessing ceiling')
 try:
  result=recognize_by_crushing(diagram,check=check,**record['config'])
  record['preparation']=result
  assert result['status']=='INCONCLUSIVE'
  chain=result['partial_chain'];assert verify_crushing_chain(diagram,chain)
  source=chain['triangulation'];obs=_prepare(source,lambda:None);assert obs['vertices']==1
  record.update(chain=chain,chain_verified=True,source_sha256=digest(source),source_tetrahedra=len(source['tetrahedra']))
  record['stage_sources']={digest(source):source}
  record['status']='PREPARED'
 except TimeoutError as e:
  record.update(status='PREPARATION_TIMEOUT',reason=str(e))
 record['native_pins_unchanged']=pins()==before
 assert record['native_pins_unchanged']
 (HERE/(a.case+'-state.json')).write_text(json.dumps(json_safe(record),indent=2)+'\n')
 print({k:record.get(k) for k in ('case','status','source_tetrahedra','source_sha256','chain_verified')},flush=True)
 if 'preparation' in record:print(record['preparation']['stats'],flush=True)

if __name__=='__main__':main()
