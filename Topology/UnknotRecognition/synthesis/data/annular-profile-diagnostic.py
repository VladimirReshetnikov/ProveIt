"""Run from the repository root; profile feasibility only, no topology verdict."""
import json,sys
from pathlib import Path
from collections import Counter
root=Path('Topology/UnknotRecognition');sys.path.insert(0,str(root/'fast'))
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from normal_orbit_research.seeds import sources
pins=sources()
audit=json.loads((root/'synthesis/data/disk-absorption-audit.json').read_text())
ids={c['id'] for c in audit['cases'] if c['native_reason']=='annular_core_attachment'}
bank=json.loads((root/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
records=[];types=Counter()
for c in bank:
 if c['id'] not in ids:continue
 p=normal_cut_parallelity(c['triangulation'],c['coordinates'])
 w=normal_parallelity_boundary_words(c['triangulation'],c['coordinates'])
 profiles=p['summary']['base_profiles'];owner={port:i for i,b in enumerate(profiles) for port in b['core_ports']}
 circles=Counter(owner[abs(a['word'][0])-1] for a in w['skeleton']['attachment_components'] if a['kind']=='circle')
 data=[]
 for i,a in sorted(circles.items()):
  b=profiles[i]
  if b['euler_characteristic']==1 and b['boundary_components']==1:continue
  record=dict(base_profile=i,chi=b['euler_characteristic'],boundary=b['boundary_components'],orientable=b['orientable'],circles=a,original_boundary_edges=b['original_boundary_edges'])
  data.append(record);types[b['euler_characteristic'],b['boundary_components'],b['orientable'],a]+=1
 records.append(dict(id=c['id'],nondisk_bases=data))
assert sources()==pins
output=dict(scope='Profile diagnostic only; no additional topology certificates',native_source_sha256=pins,cases=records,types=[dict(chi=k[0],boundary=k[1],orientable=k[2],circles=k[3],count=n)for k,n in sorted(types.items())])
Path('Topology/UnknotRecognition/synthesis/data/annular-profile-diagnostic.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps(output['types']))
