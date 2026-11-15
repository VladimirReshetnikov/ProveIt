#!/usr/bin/env python3
from pathlib import Path
import csv,json,sys
from collections import Counter
from census import parse,canonical,sha,encode,traverse
B=Path(__file__).resolve().parents[1];I=B/'incoming_extracted';O=B/'census_work/results';P='7c0bb454cf73c29ca1c385f9fec856ddd236a7cb'
base=I/'pa194_symmetric_witness_research_2026-11-14/pa194_symmetric_witness_research_2026-11-14/comparison'
base2=I/'pa194_research_2026-11-15/pa194_research_2026-11-15/comparison'
a=list(csv.DictReader((base/'named_designs_current.csv').open()));named={r['name']:r for r in csv.DictReader((base2/'named_designs91.csv').open())}
classes=json.loads((O/'classes.json').read_text())
occ=json.loads((O/'class_occurrences.json').read_text())
rows=[]
for r in a:
 n=r['name']; nr=named.get(n) or named.get(n.split(' = ')[0],{})
 ch=r['canonical_class'];assert ch in classes
 src=sorted(occ[ch],key=lambda s:(not s.startswith('Computability/'),s.count('!'),len(s)))[0]
 rows.append({'name':n,'family':nr.get('family','AX11 with cache-only guard' if 'QH' in n else 'AX11 with explicit binder and cache-only guard'),'graph_class':ch,'representative_normalized_sha256':classes[ch]['normalized_sha256'],'states':194,'mechanism':r['mechanism'],'role':r['role'],'proof_status':nr.get('proof_status','Attributed written relative or absolute claim; no new independent end-to-end proof audit.'),'source':src,'source_attribution':r['attribution'],'incoming_addition':False})
extras=[
('PA194ORH','PA194ORH_research_2026-11-15/PA194ORH_research/machines/PA194ORH/machine.tm','Operand-reader reassociation','Reassociate the operand reader while repairing its shared history-selector use; preserves all resolved AX11H primitive instructions.','Relative iPRA simulation to AX11H; absolute endpoint inherits revised written calibration.'),
('PA194OR','PA194ORH_research_2026-11-15/PA194ORH_research/machines/PA194OR/machine.tm','Operand-reader reassociation','Apply the repaired operand-reader reassociation to the primary original command protocol.','Relative iPRA simulation to primary PA194; absolute endpoint retains primary calibration obligations.'),
('PA194AX11HC4','pa194_ax11hc4_c32_research_2026-11-15/pa194_ax11hc4_c32_research_2026-11-15/construction/ax11hc4/machine/pa194_ax11hc4.tm','Physical register placement','Four-cycle of physical register positions, six selector rows; exact AX11H source preserved.','Relative full-frame simulation; revised AX11H written calibration inherited.'),
('PA194C32','pa194_ax11hc4_c32_research_2026-11-15/pa194_ax11hc4_c32_research_2026-11-15/construction/cycle32/pa194_cycle32.tm','Physical register placement','Three-cycle and two-cycle of physical register positions, seven rows; primary PA194 source preserved.','Relative full-frame equivalence to primary source; absolute iPRA calibration not newly supplied.'),
('PA194LCSF3 = PA194LCAX11HSF3','pa194_new_designs_research_2026-11-15/pa194_new_designs_research/construction/candidate/machine.tm','Guarded physical shortcuts','Third return shortcut at native190/1 on a loop-continuation, selector-and-shortcut AX11H implementation.','Written relative iPRA1/3-step simulation; absolute endpoint inherits AX11H, LC and SF transfers.'),
('PA194MP = PA194AX11HMP','pa194_new_designs_research_2026-11-15/pa194_new_designs_research/mp_construction/candidate/machine.tm','Operand-reader reassociation','Reassociate MP operands ((A,B),(C,D)) to (A,(B,(C,D))); all3671 resolved instructions preserved;87 source addresses change.','Written relative iPRA full-frame simulation to AX11H; revised calibration inherited.'),
('PA194GD_SF','pa194_research_2026-11-14(1)/pa194_research_2026-11-14/machines/PA194GD_SF/machine.tm','Selector plus guarded acceleration','Compose direct history selection and two guarded shortcuts with the independent binder/diagonal GD source.','Written positive local simulation to GD; source/calibration ancestry inherited.'),
('PA194GDH_SF','pa194_research_2026-11-14(1)/pa194_research_2026-11-14/machines/PA194GDH_SF/machine.tm','Selector plus guarded acceleration','Same physical composition on the independent binder/diagonal GDH source with cache-only halt guard.','Written positive local simulation to GDH; source/calibration ancestry inherited.'),
('PA194GDHS_SF','pa194_research_2026-11-14(1)/pa194_research_2026-11-14/machines/PA194GDHS_SF/machine.tm','Selector plus guarded acceleration','Same physical composition on GDHS with symmetric cache comparison.','Written positive local simulation to GDHS; source/calibration ancestry inherited.'),
('PA194H5X_MF','pa194_research_2026-11-15/pa194_research_2026-11-15/machines/PA194H5X_MF/machine.tm','Witness source with separated marker and acceleration','Two guarded3-to1 shortcuts plus separate marker/history selector on independent-consequent H5X.','Relative witness maps H_parent(t)→H_child(5t), H_child(t)→H_parent(3t); calibration inherited.'),
('PA194JH5X_MF','pa194_research_2026-11-15/pa194_research_2026-11-15/machines/PA194JH5X_MF/machine.tm','Witness source with separated marker and acceleration','Same marker/shortcut composition on coupled first-head/witness JH5X.','Relative witness maps H_parent(t)→H_child(5t), H_child(t)→H_parent(3t); calibration inherited.'),
('PA194H5XS','pa194_symmetric_witness_research_2026-11-14/pa194_symmetric_witness_research_2026-11-14/machines/PA194H5XS/machine.tm','Symmetric witness Shift','Compare (1,h) instead of (h,1), eliminating cache restoration after destructive comparison; independent witness consequent retained.','Written relative source+physical iPRA transfer; H5X and revised AX11H calibrations inherited.'),
('PA194JH5XS','pa194_symmetric_witness_research_2026-11-14/pa194_symmetric_witness_research_2026-11-14/machines/PA194JH5XS/machine.tm','Symmetric witness Shift','Symmetric Shift with the coupled first-head/witness JH5X calculus; emitter unchanged.','Written relative source+physical iPRA transfer; JH5X and revised AX11H calibrations inherited.')]
newchs=[]
for name,path,fam,mech,status in extras:
 p=I/path;data=p.read_bytes();rr,ss,dec=parse(data);assert len(ss)==194
 ch=sha(encode(canonical(rr,ss)));assert ch in classes
 assert ch not in {r['graph_class'] for r in rows},(name,'duplicate')
 raw=sha(data);a0=path.split('/',1)[0]+'.zip';member=path.split('/',1)[1]
 rows.append({'name':name,'family':fam,'graph_class':ch,'representative_normalized_sha256':classes[ch]['normalized_sha256'],'states':194,'mechanism':mech,'role':'Current incoming principal/supplementary positive-claim construction','proof_status':status+' Not a newly completed Lean/Rocq endpoint.','source':'docs/incoming/'+a0+'!'+member,'source_attribution':'Current incoming top-level README and retained report; new exact graph identity recomputed.','incoming_addition':True})
 newchs.append({'name':name,'graph_class':ch,'raw_sha256':raw,'rooted_action_class':sha(encode(traverse(rr,ss,0)[0])),'local_path':str(p)})
rows.sort(key=lambda r:(r['family'],r['name']))
with (O/'named_designs104.csv').open('w') as f:
 w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(O/'new_incoming_designs13.json').write_text(json.dumps(newchs,indent=2)+'\n')
fams=Counter(r['family'] for r in rows)
(O/'named_summary.json').write_text(json.dumps({'named_classes':len(rows),'new_incoming':len(extras),'family_count_for_this_editorial_grouping':len(fams),'families':dict(sorted(fams.items()))},indent=2)+'\n')
print('named',len(rows),'families',len(fams),'new',len(extras))
