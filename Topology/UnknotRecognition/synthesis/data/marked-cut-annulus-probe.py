"""Run from the repository root; stdout is a feasibility diagnostic, not a proof.

The experiment appends unsigned candidate rows for disk-base annuli to the
authenticated core incidence matrix. It does not build or verify the missing
source-chart absorption certificate and must not supply a topology verdict.
"""
import sys,json
from pathlib import Path
sys.path.insert(0,str(Path.cwd()/'Topology/UnknotRecognition/fast'))
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.core_handlebody import _forest,_occurrences,leaf_cancellation_plan,capped_cancellation_plan
from fastunknot.integer_codec import json_safe
from normal_orbit_research.seeds import sources
source_pins = sources()
bank=json.loads(Path('Topology/UnknotRecognition/fast/marked_parallelity_research/corpus.json').read_text())['cases']
audit=json.loads(Path('Topology/UnknotRecognition/synthesis/data/marked-cut-audit.json').read_text())
ids={c['id'] for c in audit['cases'] if c['native_reason']=='annular_core_attachment'}
records=[]
for c in bank:
 if c['id'] not in ids:continue
 p=normal_cut_parallelity(c['triangulation'],c['coordinates'])
 b=normal_parallelity_boundary_words(c['triangulation'],c['coordinates'])
 g=p['geometry'];profiles=p['summary']['base_profiles'];sk=b['skeleton']
 by_port={v:i for i,x in enumerate(profiles) for v in x['core_ports']}
 circles=[a for a in sk['attachment_components'] if a['kind']=='circle']
 if not all(profiles[by_port[abs(a['word'][0])-1]]['euler_characteristic']==1 and profiles[by_port[abs(a['word'][0])-1]]['boundary_components']==1 for a in circles):continue
 tree,owners=_forest(g['core'],lambda:None);counts=_occurrences(g['core'],tree,lambda:None)
 for a in circles:
  row={}
  for letter in a['word']:
   port=g['ports'][abs(letter)-1]
   if port['core_dimension']==1 and port['core_handle'] not in tree:
    h=port['core_handle'];row[h]=min(2,row.get(h,0)+1)
  counts[len(counts)]=row
 l=leaf_cancellation_plan(counts)
 q=l if not l['remaining_rows'] else capped_cancellation_plan(counts)
 records.append(dict(id=c['id'],absorbed=len(circles),rows=len(counts),columns=len(g['core']['handles1'])-len(tree),all_rows_removed=not q['remaining_rows']))
assert sources() == source_pins
print(json.dumps(dict(scope='Algebraic feasibility diagnostic only; no source-chart absorption certificate',eligible=len(records),all_rows_removed=sum(x['all_rows_removed'] for x in records),cases=records,native_source_sha256=source_pins),indent=2))
