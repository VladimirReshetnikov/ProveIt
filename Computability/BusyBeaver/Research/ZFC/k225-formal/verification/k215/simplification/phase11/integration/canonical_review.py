"""Read-only phase11 adoption/source/object check; old producer inputs stay historical."""
from pathlib import Path
import hashlib,importlib.util,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=Path(__file__).resolve().parent;F=Path('/tmp/k215-generic-cd58-check/inline-full-run1')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
assert sha(F/'result.json')=='53a7307848e6445a46b13e39b4283e335f5793660ca23f46659dc26c8f8e794d'
r=read(F/'result.json');before=read(F/'before.json');done=read(F/'completed.json');rows=read(F/'inventory.json')['modules'];a=read(P/'adoption.json')
H=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py';assert sha(H)=='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
spec=importlib.util.spec_from_file_location('inventory_helper',H);h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h);inv=h.inventory(R);assert len(inv['modules'])==192 and len(rows)==len(done)==197
ledger={}
for x in rows:
 m=x['module'];rec=done[m];paths=[R/root/(m.replace('.','/')+'.lean')for root in h.ROOTS];paths=[p for p in paths if p.is_file()];assert len(paths)==1
 src=paths[0];assert sha(src)==x['source_sha256']==rec['source_sha256']==sha(F/'workspace'/(m.replace('.','/')+'.lean'))
 assert sha(F/'objects'/(m.replace('.','/')+'.olean'))==rec['object_sha256'];assert sha(rec['log'])==rec['log_sha256'];assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
 assert rec['dependencies']=={d:done[d]['object_sha256']for d in x['imports']if d!='Init'}
 log=Path(rec['log']).read_text();assert 'error:'not in log and 'sorryAx'not in log
 ledger[m]={'canonical':str(src.relative_to(R)),'source':sha(src),'object':rec['object_sha256'],'log':rec['log_sha256']}
new={str(R/x['target']):x for x in a['files']};retired={str(R/x['target']):x for x in a['tombstones']};boundary=read('/tmp/k215-generic-cd58-check/producer-boundary.json');old={x['canonical']:x for x in boundary['files']};changed=[]
for path,pin in before['inputs'].items():
 if path in new:
  x=new[path];assert pin==x['before_sha256'];assert sha(old[path]['phase10_snapshot'])==pin;assert sha(path)==x['sha256'];changed.append(path)
 elif path in retired:
  x=retired[path];assert x['current_absent']and not Path(path).exists();assert sha(x['archived_before'])==pin==x['before_sha256']==sha(old[path]['phase10_snapshot']);changed.append(path)
 else:assert sha(path)==pin,path
assert len(changed)==3
for x in a['files']:
 assert sha(R/x['target'])==sha(x['source'])==x['sha256']
 if x['target'].endswith('.lean'):assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',h.without_comments_strings((R/x['target']).read_text()))
for x in a['tombstones']:assert not(R/x['target']).exists()and sha(x['archived_before'])==x['before_sha256']
for audit in r['audits']:
 q=F/('audit-'+audit['module']);assert sha(q/(audit['module']+'.olean'))==audit['object_sha256'];assert sha(q/(audit['module']+'.lean'))==sha(audit['source'])==audit['source_sha256'];assert sha(audit['log'])==audit['log_sha256']
assert len(r['fresh_modules'])==8 and len(r['phase10_reused_modules'])==189 and len(r['audits'])==2
result={'status':'PASS_CURRENT_PHASE11_ADOPTION','current_Lean_modules':197,'endpoint_modules':192,'fresh_modules':8,'exact_phase10_providers':189,'replacement_files':2,'retired_unused_templates':2,'current_source_changes':1,'all_current_sources_objects_logs_dependencies_checked':True,'both_audit_objects_checked':True,'three_old_producer_inputs_explicitly_historical':changed,'all_other_before_inputs_current_exact':True,'full_result_sha256':sha(F/'result.json'),'adoption_sha256':sha(P/'adoption.json'),'reviewer_sha256':sha(__file__),'ledger':ledger,'scope':'Worktree source/object/log binding check; two templates are absent by registered retirement and exact old blobs remain. Raw before.inputs unedited. No compiler execution or index claim by this reader.'}
(P/'canonical-review.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='ledger'},indent=2))
