#!/usr/bin/env python3
"""Independent source/static comparison only; no imports from delivered code."""
from pathlib import Path
import hashlib,json,re
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p))
inv=json.loads((B/'source-inventory.json').read_text())
checks=0
def check(x):
 global checks
 assert x
 checks+=1
def transform(s,numbers):
 s=re.sub(r'\b(?:244|245)\b',lambda m:numbers.get(m[0],m[0]),s)
 for a,b in [('Routing245','Rotation244'),('Compensated244','Combined243'),('compensated244','combined243'),('exceptionalRow244','exceptionalRow243'),('embedState244','embedState243'),('embedAction244','embedAction243'),('embedConfig244','embedConfig243')]:s=s.replace(a,b)
 return s
stripdoc=lambda s:re.sub(r'/\-!.*?\-/','',s,count=1,flags=re.S)
bindings=[]
for u in inv['units']:
 paths={k:Path(u[k]['path']) for k in ['source','audit','passed_predecessor_source','passed_predecessor_audit']}
 for k,p in paths.items():check(sha(p)==u[k]['sha256']);bindings.append(desc(p))
 new=paths['source'].read_text();old=paths['passed_predecessor_source'].read_text()
 check(stripdoc(new)==stripdoc(transform(old,u['numeric_state_count_substitutions'])))
 aud=transform(paths['passed_predecessor_audit'].read_text(),u['numeric_state_count_substitutions'])
 aud=re.sub(r'^#print axioms (\w+)$',lambda m:'#print axioms SetTheory.BusyBeaver.ZFC.'+u['name']+'.'+m[1],aud,flags=re.M)
 check(aud==paths['audit'].read_text())
 check(re.findall(r'^#print axioms (\S+)$',aud,re.M)==u['qualified_probes'])
 check(len(re.findall(r'^example\b',aud,re.M))==u['callers'])
 check(not re.search(r'\b(?:sorry|admit|native_decide|set_option)\b',stripdoc(new)))

tabletext='\n'.join((B/p).read_text()for p in ['table-rotation/TableRotation244.lean','table-combined/TableCombined243.lean'])
decls=set(re.findall(r'^(?:def|theorem|abbrev) (\w+)',tabletext,re.M))
for api in inv['expected_table_api']:check(api in decls)
check('embedConfig243 (initial 243) = initial 244' in tabletext)
check('  | 95 => 0' in (B/'table-rotation/TableRotation244.lean').read_text())
check('  if h : q.val < 112 then' in tabletext)
for folder,module in [('table-rotation','TableRotation244'),('table-combined','TableCombined243')]:
 ti=json.loads((B/folder/'source-inventory.json').read_text())
 for k in ['source','audit']:check(sha(ti[k]['path'])==ti[k]['sha256']);bindings.append(ti[k])

source=Path('/tmp/zfc243-combined-candidate/static-combination-review.json')
c=json.loads(source.read_text());check(c['checked_block_row_count']==23 and c['common_action_and_next_exclusion'] and c['patches_commute'])
for r in c['all_checked_block_row_bindings']:
 side={'Routing245':'Rotation244','Compensated244':'Combined243'}[r['side']]
 bo=lambda v:'true'if v else'false'
 w,d,t=r['action'];pat=rf'theorem foldRow{side}_old{r["state"]}_{bo(r["bit"])} :\s*machine{side}\.transition \(oldState{side} {r["state"]}\) {bo(r["bit"])} =\s*⟨{bo(w)}, \.{"left"if d=="L"else"right"}, some \(oldState{side} {t}\)⟩'
 check(re.search(pat,tabletext) is not None)
check(c['source_leaves']==6459 and c['source_guarded_cases']==8390)
out=dict(status='INDEPENDENT_SOURCE_ONLY_PORT_REVIEW_PASS',findings=[],reviewer_source=desc(Path(__file__)),
 source_inventory=desc(B/'source-inventory.json'),inputs=bindings,static_combination=desc(source),checks=checks,
 scope='All three complete Lean sources/audits read; exact proof-body mechanical correspondence to passed245→compensated244, full23 row support, all requested APIs and seed embedding checked. No compiler/elaboration/current-object claim.',
 mathematical_findings=['Invariant incoming68/81/167 unaffected by rotation, initialold95 vacuous.',
 'Seven matched blocks retain exact list tapes, including identical two-cell write order in81/read1 branch.',
 'Global relation includes original-side invariant and excludes newold92 checkpoint; all ordinary actions avoid92.',
 'Both matched durations positive; generic actual halt equivalence applies after separate kernel acceptance.',
 'Conclusion only Rotation244↔Combined243 blank/old95 finite-support runs; no automatic inherited245 calibration or PA claim.'],
 reviewer_role='Independent of three dependent port sources; author of two proposed table sources and static combination. No supplied script/compiler run.')
dest=B/'independent-port-source-review.json';check(not dest.exists());dest.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(desc(dest)))
