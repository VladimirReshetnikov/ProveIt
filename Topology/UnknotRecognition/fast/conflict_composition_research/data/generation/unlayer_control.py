"""Fresh zero-search comparison of optional inverse layering preprocessing."""
import json
from time import monotonic
from pathlib import Path
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.boundary_unlayer import unlayer_boundary_once
from fastunknot.integer_codec import json_safe
from prepare import HERE,pins,digest

state=json.loads((HERE/'tt-state.json').read_text()); before=pins();started=monotonic()
def check():
 if monotonic()-started>30:raise TimeoutError('cooperative zero-search preprocessing control ceiling')
config=dict(unlayer_boundary=True,sector_method='transversal',transversal_candidate_policy='conflicts',max_tree_nodes=0,max_pivots=0,max_anchors=0)
diagram=Diagram.from_pd(state['input_pd']);result=recognize_by_crushing(diagram,check=check,**config)
assert result['status']=='INCONCLUSIVE';chain=result['partial_chain'];assert chain['schema']=='diagram-crushing-v2';assert verify_crushing_chain(diagram,chain,check=check)
source=chain['triangulation'];assert source==state['chain']['triangulation'];assert chain['steps']==state['chain']['steps'];p=_prepare(source,check);assert p['vertices']==1
unlayer=unlayer_boundary_once(source,check=check);assert unlayer['status']=='UNCHANGED';assert result['stats']['boundary_unlayerings']==0
out=dict(passed=True,config=config,native_sha256=before,native_pins_unchanged=pins()==before,old_state_sha256=digest(state),source_sha256=digest(source),source_tetrahedra=len(source['tetrahedra']),source_vertices=p['vertices'],boundary_faces=p['boundary_faces'],same_labelled_source=True,same_crushing_steps=True,chain_verified=True,unlayer_probe=unlayer,result=result)
assert out['native_pins_unchanged'];(HERE/'tt-unlayer-control.json').write_text(json.dumps(json_safe(out),indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ('result','native_sha256')});print(result['stats'])
