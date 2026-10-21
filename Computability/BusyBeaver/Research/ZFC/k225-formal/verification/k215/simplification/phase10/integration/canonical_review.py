"""Read-only current source/object/log check, with explicit historical producer replacements."""
from pathlib import Path
import hashlib,importlib.util,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');P=Path(__file__).resolve().parent;F=P/'full-run1'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
assert sha(F/'result.json')=='6bc3039524d69a976c8c3b726ccbe9b47e884877e682bcf2d0f79555caa96a58'
r=read(F/'result.json');rows=read(F/'inventory.json')['modules'];done=read(F/'completed.json');before=read(F/'before.json');a=read(P/'adoption.json')
H=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py';spec=importlib.util.spec_from_file_location('inventory',H);h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
inv=h.inventory(R);assert len(inv['modules'])==192 and len(rows)==len(done)==197
ledger={}
for x in rows:
 m=x['module'];rec=done[m];paths=[R/root/(m.replace('.','/')+'.lean')for root in h.ROOTS];paths=[p for p in paths if p.is_file()];assert len(paths)==1
 src=paths[0];assert sha(src)==x['source_sha256']==rec['source_sha256']==sha(F/'workspace'/(m.replace('.','/')+'.lean'))
 assert sha(F/'objects'/(m.replace('.','/')+'.olean'))==rec['object_sha256'];assert sha(rec['log'])==rec['log_sha256'];assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
 assert rec['dependencies']=={d:done[d]['object_sha256']for d in x['imports']if d!='Init'}
 log=Path(rec['log']).read_text();assert 'error:'not in log and 'sorryAx'not in log
 ledger[m]={'canonical':str(src.relative_to(R)),'source':sha(src),'object':rec['object_sha256'],'log':rec['log_sha256']}
history={x['canonical']:x for x in read(P/'producer-before.json')['files']};adopted={str(R/x['target']):x for x in a['files']};replaced=[]
for path,pin in before['inputs'].items():
 if path in adopted:
  x=adopted[path];assert pin==x['before_sha256'];old=history[path];assert old['sha256']==pin==sha(old['historical_snapshot']);assert sha(path)==x['sha256'];replaced.append(path)
 else:assert sha(path)==pin,path
assert len(replaced)==3
for x in a['files']:
 assert sha(R/x['target'])==sha(x['source'])==x['sha256']
 if x['target'].endswith('.lean'):
  assert not re.search(r'\b(?:sorry|admit|axiom|native_decide)\b',h.without_comments_strings((R/x['target']).read_text()))
for audit in r['audits']:
 q=F/('audit-'+audit['module']);assert sha(q/(audit['module']+'.olean'))==audit['object_sha256'];assert sha(q/(audit['module']+'.lean'))==sha(audit['source'])==audit['source_sha256'];assert sha(audit['log'])==audit['log_sha256']
assert len(r['fresh_modules'])==8 and len(r['isolated_reused_modules'])==189
out={'status':'PASS_CURRENT_PHASE10_CANONICAL_ADOPTION','selected_union':197,'endpoint_modules':192,'fresh_modules':8,'unchanged_phase9_providers':189,'adopted_files':4,'current_Lean_source_changes':1,'historical_producer_inputs':replaced,'historical_inputs_exact_snapshots_checked':True,'all_other_before_inputs_current_exact':True,'all_current_sources_objects_logs_dependencies_checked':True,'two_audit_objects_checked':True,'full_result_sha256':sha(F/'result.json'),'adoption_sha256':sha(P/'adoption.json'),'reviewer_sha256':sha(__file__),'ledger':ledger,'scope':'Raw build inputs remain unchanged in run record; three intentionally replaced producer paths use exact pre-adoption snapshots plus registered current replacements. No compiler execution by this reader.'}
(P/'canonical-review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='ledger'},indent=2))
