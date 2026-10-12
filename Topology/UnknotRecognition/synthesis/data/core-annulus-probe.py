"""Run from repo root; passive intersection feasibility only, not a certificate."""
import json,sys
from pathlib import Path
root=Path('Topology/UnknotRecognition');sys.path.insert(0,str(root/'fast'))
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.disk_bundle_absorption import absorb_disk_bundles
from fastunknot.core_handlebody import core_handlebody_certificate, _occurrences
from normal_orbit_research.seeds import sources
pins=sources()
audit=json.loads((root/'synthesis/data/primitive-annuli-audit.json').read_text())
ids={c['id'] for c in audit['cases'] if c['native_reason']=='annular_core_attachment'}
bank=json.loads((root/'fast/marked_parallelity_research/corpus.json').read_text())['cases']
records=[]
for c in bank:
 if c['id'] not in ids:continue
 p=normal_cut_parallelity(c['triangulation'],c['coordinates'])
 b=normal_parallelity_boundary_words(c['triangulation'],c['coordinates'])
 profiles=p['summary']['base_profiles'];g=p['geometry'];sk=b['skeleton']
 nondisks={i for i,x in enumerate(profiles) if (x['euler_characteristic'],x['boundary_components'])!=(1,1)}
 # Skip all nondisks only for this diagnostic. No primitive proof is claimed.
 augmented,_,_=absorb_disk_bundles(g,p['summary'],sk,primitive_bases=nondisks)
 core=core_handlebody_certificate(augmented)
 record=dict(id=c['id'],core_status=core['status'],reason=core.get('reason'))
 if core['status']!='COMPLETE':records.append(record);continue
 tree=set(core['certificate']['forest']);active=_occurrences(augmented,tree,lambda:None)
 owner={v:i for i,x in enumerate(profiles) for v in x['core_ports']}
 passive={}
 for i,a in enumerate(sk['attachment_components']):
  if a['kind']!='circle' or owner[abs(a['word'][0])-1] not in nondisks:continue
  row={}
  for letter in a['word']:
   port=g['ports'][abs(letter)-1];h=port['core_handle']
   if port['core_dimension']==1 and h not in tree:row[h]=min(2,row.get(h,0)+1)
  passive[i]=row
 for r,h in core['certificate']['cancellations']:
  donor=active.pop(r);assert donor.pop(h)==1
  for row in list(active.values())+list(passive.values()):
   count=row.pop(h,0)
   if count:
    for v,n in donor.items():row[v]=min(2,row.get(v,0)+count*n)
 assert not active
 private={i:[h for h,n in row.items() if n==1 and all(h not in other for j,other in passive.items() if j!=i)]for i,row in passive.items()}
 record.update(annuli=len(passive),all_private=all(private.values()),private_columns=private,passive_rows=passive)
 records.append(record)
assert sources()==pins
report=dict(scope='Algebraic diagnostic only; no source transport certificate',native_source_sha256=pins,cases=records,private_families=sum(c.get('all_private',False) for c in records))
Path('Topology/UnknotRecognition/synthesis/data/core-annulus-probe.json').write_text(json.dumps(report,indent=2)+'\n')
for c in records:print({k:v for k,v in c.items() if k!='passive_rows'})
