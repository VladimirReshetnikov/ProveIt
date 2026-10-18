"""Independent source-only successor review; no emitter, freezer, guard or Lean calls."""
from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-routing245-lean/coverage-production');V=B/'v2'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(Path(p).resolve()),sha256=sha(p))
checks=0
def yes(c):
 global checks
 assert c;checks+=1
names={'generate_sites_routing245_v2.py':'2aa18532c04bc991ddef938c51df0cf08988a614a0278ea9f2261226a7e95576','check-production-v2.template.py':'eac5b5523594a34633e9e38a9d1e6bebfb1924518294daf2f7209f3390c6e8ed','freeze_guard_v2.py':'8922987d3f86bc7daf9cad4f62737a92e3e583134414e4271334c4d009a2f926'}
for n,h in names.items():yes(sha(V/n)==h);ast.parse((V/n).read_text())
def funcs(path):return {n.name:ast.dump(n,include_attributes=False)for n in ast.parse(Path(path).read_text()).body if isinstance(n,ast.FunctionDef)}
fg,og=funcs(V/'generate_sites_routing245_v2.py'),funcs(B/'generate_sites_routing245.py')
for n in ['sha','desc','need','bits','goal','imports','routed_tree','checked_pilots','footer','audit']:yes(fg[n]==og[n])
sg=(V/'check-production-v2.template.py').read_text();old=(B/'check-production.py').read_text()
# Only base-boundary path moves one directory deeper inside the execution body;
# comments do not alter AST. Launcher, snapshots and checks are otherwise exact.
normalized=sg.replace("HERE.parent.parent/'coverage-subtree-pilots/boundary-plan.json'","HERE.parent/'coverage-subtree-pilots/boundary-plan.json'")
gf={n.name:ast.dump(n,include_attributes=False)for n in ast.parse(normalized).body if isinstance(n,ast.FunctionDef)};of=funcs(B/'check-production.py')
for n in ['sha','need','imports','first_path','descriptor','run_unit','successful_receipt']:yes(gf[n]==of[n])
plan=json.loads((B/'sources/generation.json').read_text());batch=json.loads((B/'all-run1/batch.json').read_text());inventory=json.loads((V/'static-plan-inventory.json').read_text())
yes(sha(B/'sources/generation.json')=='acc22343a70173e143ccf7cef76c9c7dfa7632b2526d3ca5735cb7d582062f24')
yes(sha(B/'all-run1/batch.json')=='46c14a9f5225cfb93abbe7d07afe98239e974710ea1045638f6fbbfcb222e62c')
yes(batch['status']=='FAIL'and batch['failed_unit']==13 and [r['unit_index']for r in batch['completed_units']]==list(range(13)))
unique={};reused={};raw_records=[]
for row in batch['completed_units']:
 i=row['unit_index'];u=plan['units'][i];p=Path(row['record']['path']);yes(sha(p)==row['record']['sha256']);d=json.loads(p.read_text())
 yes(d['status']=='PASS'and not d['prepare_only']and d['before']==d['after']and d['all_input_provider_postchecks']and d['source_object_recorded_before_audit']and d['all_fresh_objects_unchanged_after_audit'])
 yes((d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']))
 for path,h in d['before'].items():
  if path in unique:yes(unique[path]==h)
  else:yes(sha(path)==h);unique[path]=h
 yes([c['label']for c in d['commands']]==['source','audit'])
 for c in d['commands']:yes(c['exit_code']==0 and not c['timed_out']);yes(Path(c['log']).read_text()==c['output'])
 for role in ('source','audit'):
  q=d[role];yes(sha(q['path'])==sha(q['snapshot'])==q['sha256']==u[role+'_sha256'])
 fs=d['fresh_modules'];yes(len(fs)==1 and fs[0]['module']==u['module']);f=fs[0]
 yes(all(f[k]==d['source_pass_object'][k]for k in ('module','path','sha256','source_sha256')))
 actual=d['fresh_first_provider_before_audit'];ap=actual.get('actual_first',actual.get('path'))
 yes(sha(f['path'])==sha(ap)==f['sha256']==actual['sha256']and Path(ap).resolve()==Path(f['path']).resolve())
 pr=d['preparation'];yes(sha(pr['path'])==pr['sha256']);prep=json.loads(Path(pr['path']).read_text())
 yes(prep['status']=='PREPARED_NOT_BUILT'and prep['prepare_only']and prep['commands']==[]and prep['fresh_modules']==[]and prep['before']==prep['after']==d['before'])
 reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
 yes([n for n,a in reports]==['SetTheory.BusyBeaver.ZFC.SitesRouting245.'+x for x in u['probe_names']])
 yes([dict(name=n,axioms=[x.strip()for x in a.split(',')if x.strip()])for n,a in reports]==d['actual_axiom_sets'])
 for ci in u['cuts']:yes(ci not in reused);reused[ci]=u['module']
 raw_records.append(desc(p))
yes(set(reused)==set(range(1,42)))
for i in (0,70,174):reused[i]=next(x['full_module']for x in plan['reused_units']if x['index']==i)
new=sorted(set(range(236))-set(reused));yes(len(new)==192 and new[:2]==[42,43]);yes(new==inventory['new_cut_indices'])
modules={i:reused.get(i,'BusyBeaver.ZFC.SitesRouting245Cut'+str(i).zfill(3))for i in range(236)}
for q in plan['join_plan']:
 for kind,i in [q['left'],q['right']]:
  if kind=='join':yes(i<q['index'])
  else:yes(i in modules)
yes(192+15+1==inventory['prospective_new_units']==208)
yes(192+235+3==inventory['prospective_new_probes']==inventory['prospective_new_callers']==430)
yes(41+3==inventory['reused_probes']==44 and 41+6==inventory['reused_callers']==47)
yes(430+44==474 and 430+47==477)
yes(23+16+207==inventory['prospective_final_project_closure']==246)
# Source histories including exact timeout remain unchanged and usable.
for p in (V/'history-v1/sources').iterdir():yes(p.read_bytes()==(B/'sources'/p.name).read_bytes())
for n,original in [('check-production.py',B/'check-production.py'),('generate_sites_routing245.py',B/'generate_sites_routing245.py'),('batch.json',B/'all-run1/batch.json')]:yes((V/'history-v1'/n).read_bytes()==original.read_bytes())
for p in (V/'history-v1/unit013').rglob('*'):
 if p.is_file():yes(p.read_bytes()==(B/'all-run1/unit013'/p.relative_to(V/'history-v1/unit013')).read_bytes())
failed=Path(batch['failed_record']['path']);yes(sha(failed)==batch['failed_record']['sha256']);f=json.loads(failed.read_text());yes(f['status']=='FAIL'and f['fresh_modules']==[]and len(f['commands'])==1 and f['commands'][0]['timed_out'])
out=V/'independent-successor-source-review.json';yes(not out.exists())
r=dict(status='SOURCE_ONLY_SUCCESSOR_REVIEW_CLEAN',reviewer=desc(Path(__file__)),programs={n:desc(V/n)for n in names},inventory=desc(V/'static-plan-inventory.json'),checks=checks,reused_actual_records=raw_records,deduplicated_current_inputs=len(unique),original_timeout=desc(failed),findings=[],source_findings=['Exact cap64 frontier and both-child joins are unchanged; one new module per remaining cut.','All13 actual old batches cover cuts1..41, while3 pilots cover0,70,174. Reused theorem names/namespaces stay exact.','Old batch records require nonpilot preparation checks and original SitesRouting245 probe prefixes; pilots use their original namespaces and checked probe.','192 new cuts+15join modules+final=208 new units;430new+44reused probes=474,430new+47reused callers=477.','Execution body is AST-identical to reviewed v1 after one base-boundary path relocation, including shared120s/defaultlimits/source-before-audit/process-group termination.','Manifest freezer allows only exact prospectivecensus/current416files, inserts one manifest digest and explicit path, and never runs a proof.'],future_obligations=['Root must emit exact successor sources, inspect first cuts42/43 and freeze manifest before any proof run. This receipt does not claim generated-source or compiled success.','Final prospective Sites closure is246; final Binary guard closure must be recomputed instead of reusing earlier330 estimate.'],no_emitter_execution=True,no_freezer_execution=True,no_guard_execution=True,no_compiler_or_version_execution=True,no_simulation=True)
out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(review=desc(out),checks=checks,current_inputs=len(unique)),indent=2))
