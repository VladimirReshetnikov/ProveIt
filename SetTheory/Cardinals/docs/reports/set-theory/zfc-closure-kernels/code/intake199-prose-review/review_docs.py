#!/usr/bin/env python3
"""Own bounded metadata and link reader for four fully read batch199 pages."""
from pathlib import Path
import json,re,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels';P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
docs=[H/'intake-199.md',H/'intake-199-reproduction.md',R/'Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/composed/README.md',R/'Computability/BusyBeaver/Research/ZFC/candidate-k216/alternatives/rho6/README.md'];links=[]
for p in docs:
 for link in re.findall(r'\]\(([^)]+)\)',p.read_text()):
  if link.startswith(('http:','https:','#')):continue
  q=(p.parent/link.split('#')[0]).resolve();assert q.exists(),(p,link);links.append({'source':str(p.relative_to(R)),'link':link})
a=load(H/'data/intake199-source162/actual.json');b=load(H/'data/intake199-source163/fresh1/actual.json');c=load(H/'data/intake199-source164/actual.json')
assert a['status']=='SEVEN_SELECTED_SOURCE162_LEAVES_PASS' and a['inputs_unchanged'] and len(a['before'])==26
assert b['status']=='ALL_FOUR_SELECTED_LEAVES_PASS' and b['original_unchanged'] and b['original_files']==95 and b['final_files']==97
assert c['status']=='PASS_PROCESS_AND_INPUT_BINDINGS' and c['inputs_unchanged'] and len(c['before'])==29
assert[len(x['jobs'])for x in(a,b,c)]==[7,4,7]
for x in(a,b,c):
 for j in x['jobs']:assert j.get('returncode',j.get('exit_code'))==0 and not j['timed_out']
r=load(H/'data/intake199-source162/root-review.json');assert[r[k]for k in('cases','symbolic_rules','minimum_duration','covered_rows','block_rows')]==[6176,1698790,6,430,12]
assert r['blank']['stored_events']==95726 and r['blank']['canonical_state']==83 and r['source164_transfer']['all430_rows'] and not r['source164_transfer']['fresh_full_runtime']
s=load(H/'data/intake199-source163/actual-review.json');assert s['result_counts']['blank_steps']==313133 and s['result_counts']['matrix_schema_assignments']==207 and s['result_counts']['matrix_inference_pairs']==18
q=load(H/'data/intake199-source164/actual-review.json');assert q['projection']=={'nodes':3728,'terms':5160,'leaves':1260,'roots':7,'minimum_fixed_certificate_cover':9,'optimal_covers':6};assert q['matrix']['finite_homomorphism']==9216 and q['matrix']['raw_family_cases']==524288 and not q['matrix']['full_native_model'];assert q['residual_interface_cases']==4619 and q['scanner']['old_successor']==43 and q['scanner']['mutated_successor']==66
place=load(H/'data/intake199-placement.json');assert place['counts']=={'archive-only':20,'new':207,'existing-alias':156,'history-alias':7,'batch-alias':13};assert sum(place['counts'].values())==403
text=docs[0].read_text();assert 'four restricted implicational schema checks' in ' '.join(text.split()) and 'P(a,b)≥max(a,b)' in text
rec={'status':'INDEPENDENT_INTAKE199_FOUR_DOCUMENT_PROSE_PEER_PASS','findings':[],'role_disclosure':'Reviewer authored/executed Source162 selected launcher and earlier accepted215 source composition. Not the author of these four pages or Source163/164 reviews. This is a prose/API/selected-metadata peer, not another execution or independent Source162 runtime audit.','scope':'All four documents read in full against own frozen Source162 dossier, full Source163/164 dossiers and actual summaries. All local links checked. Portable CLI flag/status names inspected statically; no supplied helper, machine, source checker or proof compiler invoked. Placement totals compared as metadata only, no archive/checksum census.','documents':{str(p.relative_to(R)):sha(p)for p in docs},'links_checked':len(links),'corrections_preserved':['Initial wording called four restricted-schema checks four matrices; root clarified that two algebras are reused.','Pairing hypothesis made explicit: effective bijective pairing, P(a,b)≥max(a,b), P(0,0)=0.'],'checks':['Distinct215 allocation vs exact162/164 isomorphism and one-runtime transfer','Fresh1627jobs/26inputs, full6176/1698790/all430 and complete95726 blank correctly scoped','Source1634finite leaves and delivered fullruntime kept separate; old protected-credit command ordering caveat retained','Source164 projection minimality limited to fixed certificate; GEN failure prevents full-model claim','ResidualMP tests retain safe-row and induction-oracle limits; binary splice remains research','Ordinary ZFC equivalence distinguished from exact Lean/internalPA, absolute consistency, minimum and214 target','Fourteen-line selected command interfaces and expected status names match current portable sources'],'reader_completion':'Root statically corrected Source164 exit-code key and whitespace-sensitive prose assertion in the unfinished peer reader, then executed it. Independent full prose review was already delivered by opening_encoder; this execution adds metadata/link checks only.','reader_sha256':sha(Path(__file__))}
(P/'review.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2));print('SHA',sha(P/'review.json'))
if __name__=='__main__':pass
