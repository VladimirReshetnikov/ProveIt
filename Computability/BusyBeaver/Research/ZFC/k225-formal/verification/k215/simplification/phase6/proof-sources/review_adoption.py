"""Read-only source adoption audit; no object, compiler or full-build claim."""
from pathlib import Path
import json,hashlib,re
O=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');A=Path('/tmp/k215-proof-phase6/adoption.json');MAP=Path('/tmp/k215-fast-sites-migration/combined-adoption-map.json');INV=Path('/tmp/k215-proof-phase6/pre-run-inventory.json');OLD=Path('/tmp/k215-proof-phase5/lean-run1/inventory.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads(A.read_text());m=json.loads(MAP.read_text());inv=json.loads(INV.read_text());old=json.loads(OLD.read_text())
assert len(a['files'])==21 and a['source_map_sha256']==sha(MAP)
assert a['files'][:20]==m['rows']
rows=[]
for r in a['files']:
 src=Path(r['source']);dst=R/r['destination'];assert not src.is_symlink()and not dst.is_symlink();assert sha(src)==sha(dst)==r['sha256'];assert src.stat().st_size==dst.stat().st_size==r['bytes']
 rows.append({'destination':r['destination'],'sha256':r['sha256'],'source':r['source']})
assert len(m['regenerated_unchanged'])==16
for r in m['regenerated_unchanged']:assert sha(R/r['destination'])==sha(Path(r['source']))==r['sha256']==r['before_sha256']
assert len(inv['modules'])==187 and inv['external_imports']==['Init']
byname={r['module']:r for r in inv['modules']};oldnames={r['module']for r in old['modules']}
assert set(byname)-oldnames=={'BusyBeaver.ZFC.RMNormalizedBisim','BusyBeaver.ZFC.KSource215Program','BusyBeaver.ZFC.KFastSites215'}and oldnames<=set(byname)
for r in inv['modules']:
 p=Path(r['source']);assert sha(p)==r['source_sha256'];actual=re.findall(r'^import (\S+)',p.read_text(),re.M);assert actual==r['imports'],r['module']
adopted={str(R/r['destination']) for r in a['files']};unchanged=0
for r in old['modules']:
 if r['source']not in adopted:assert sha(Path(r['source']))==r['source_sha256'];unchanged+=1
L=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
for name in ['RMBisim.lean','KSim.lean','KTable215.lean','KFast215.lean','KBoot215.lean']:
 r=next(x for x in old['modules']if Path(x['source'])==L/name);assert sha(L/name)==r['source_sha256']
# The final endpoint has only the separately required import addition.
prev=Path('/tmp/k215-normalized-migration/baseline/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean').read_bytes()
assert(L/'KEndpoint215.lean').read_bytes()==b'import BusyBeaver.ZFC.KSource215\n'+prev
result={'status':'PASS_SOURCE_ADOPTION_BINDINGS_ONLY','adoption_sha256':sha(A),'combined_map_sha256':sha(MAP),'pre_run_inventory_sha256':sha(INV),'phase5_inventory_sha256':sha(OLD),'adopted_files':rows,'regenerated_unchanged_check_files':16,'current_project_sources':187,'new_project_modules':sorted(set(byname)-oldnames),'phase5_project_sources_unchanged':unchanged,'endpoint_body_unchanged':True,'machine_program_semantics_not_changed':True,'compiler_or_object_execution':False,'combined_phase6_status':'not assessed; root owns live build'}
(O/'adoption-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='adopted_files'},indent=2))
