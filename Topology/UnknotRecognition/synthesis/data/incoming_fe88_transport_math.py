"""Recheck report 68 transport identities and the disconnected primitive fibre."""
from pathlib import Path
from types import ModuleType
from itertools import product
from hashlib import sha256
import json,sys
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'fast'))
for name in ('cocycle_transport_verify','cocycle_transport'):
 path=root/'reports/68/fast/fastunknot'/f'{name}.py'
 m=ModuleType('fastunknot.'+name);m.__package__='fastunknot';sys.modules[m.__name__]=m
 exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__)
from fastunknot.cocycle_transport_verify import verify_cocycle_transport
from fastunknot.cocycle_transport import bipyramid_cocycle_score
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
source=json.loads((root/'reports/68/synthesis/data/cocycle-transport-splitting.json').read_text())
before=source['preparation'];after=source['collapse']
assert verify_cocycle_transport(source['initial_triangulation'],source['initial_heights'],before['triangulation'],before['transport'])
assert verify_cocycle_transport(before['triangulation'],before['transport']['heights'],after['triangulation'],after['transport'])
for name,step in [('before_census',before),('after_census',after)]:
 assert verify_normal_component_certificate(step['triangulation'],step['transport']['coordinates'],source[name]['certificate'])
 spectra=normal_topology_spectrum(step['triangulation'],step['transport']['coordinates'],record_certificate=True)
 assert verify_normal_topology_spectrum(step['triangulation'],step['transport']['coordinates'],spectra['certificate'])
 if name=='before_census': assert spectra['components']==1 and spectra['euler_characteristic']==1
 else: assert spectra['components']==3 and spectra['euler_characteristic']==5
span=lambda *v:max(v)-min(v)
for heights in product(range(-2,3),repeat=5):
 c,d,e,a,b=heights
 pieces=span(a,b,c,d)+span(a,b,d,e)+span(a,b,e,c)-span(a,c,d,e)-span(b,c,d,e)
 arcs=span(a,b,c)+span(a,b,d)+span(a,b,e)-span(c,d,e)
 score=bipyramid_cocycle_score(heights)
 assert pieces==score['normal_disc_increase'] and abs(a-b)-arcs+pieces==-score['euler_loss']
result=dict(source_splitting_sha256=sha256((root/'reports/68/synthesis/data/cocycle-transport-splitting.json').read_bytes()).hexdigest(),
 source_bound_moves=2,source_component_certificates=2,current_type_certificates=2,local_height_cases=3125,
 before=dict(components=1,euler=1,pieces=24),after=dict(components=3,euler=5,pieces=19),
 scope='current native verification plus delivered transport verifier on scratch module imports; no transport production dispatcher installed')
(root/'synthesis/data/incoming-fe88-transport-math.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
