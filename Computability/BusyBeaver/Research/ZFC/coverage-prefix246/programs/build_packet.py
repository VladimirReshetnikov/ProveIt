#!/usr/bin/env python3
"""Package an already complete exact246 coverage proof; never execute supplied code.
All102 selected source/audit PASSES and a complete existing-evidence review are
required. Historical interruptions/failures remain raw and separately classified.
The builder only reads, hashes and copies files into a new external directory.
"""
from pathlib import Path
import argparse,hashlib,json,re,shutil
PLAN_SHA='9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09'
GENERATION_SHA='174870fefd527465036748bd5649f9acde8dcfad3a46e8ee33884c888507e223'
TEMPLATE_SHA='ce1fdfcbc0304d261364a302a3e913ca0d6f971e27266a46c217b474a300a34d'
RECOVERY_SHA='489a13fa02e83342c824fa9dee64f133b8d65e188d2edadd8d25577e13588a5d'
REUSE050_SHA='9a80157f47d7526eab3cf8abbe34944a55f2240f10af034e265e14e4482fdb55'
Z=Path('Computability/BusyBeaver/Research/ZFC');L=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC');DEST=Z/'coverage-prefix246'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for name in ['repo','coverage-root','terminal-pipeline','complete-review','output']:ap.add_argument('--'+name,type=Path,required=True)
 ap.add_argument('--complete-review-sha',required=True);ap.add_argument('--template',type=Path,default=Path('/tmp/zfc-prefix250-lean/coverage/check.py'))
 a=ap.parse_args();need(__debug__,'Assertions must remain enabled.');R=a.repo.resolve();B=a.coverage_root.resolve();O=a.output.resolve();H=Path(__file__).resolve().parent
 need(not O.exists()and not O.is_relative_to(R)and not O.is_relative_to(B),'Use a new external output outside repo and coverage history.')
 mf=B/'guards-four/pipeline-manifest.json';gf=B/'plan-four/generation.json';need(sha(mf)==PLAN_SHA and sha(gf)==GENERATION_SHA,'Frozen plan changed.')
 plan=json.loads(mf.read_text());generation=json.loads(gf.read_text());units=plan['units'];by={u['module']:u for u in units}
 need(len(units)==len(by)==102 and plan['full_plan'],'Incomplete selected plan.')
 need(sum(u['probes']for u in units)==sum(u['callers']for u in units)==468,'Audit census changed.')
 need(sha(a.template)==TEMPLATE_SHA,'Original guard-generator template changed.')
 canonical=R/Z/'candidate-prefix246/zfc_prefix246.tm';need(sha(canonical)=='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc','Canonical246 table changed.')
 recovery=B/'recovery-after-session79413/recovery-review.json';reuse=B/'grouped-four-reuse-050.json'
 need(sha(recovery)==RECOVERY_SHA and sha(reuse)==REUSE050_SHA,'Provisional50/recovery history changed.')
 tp=a.terminal_pipeline.resolve();need(tp.is_relative_to(B),'Terminal summary must belong to coverage history.');terminal=json.loads(tp.read_text())
 need(terminal['status']=='PASS_COMPLETE_PLAN'and terminal['full_plan']and terminal['endpoint_established']and terminal['pending']==[],'Complete terminal runner PASS required.')
 need(terminal['manifest']['sha256']==PLAN_SHA and terminal['plan_sha256']==GENERATION_SHA,'Terminal plan differs.')
 available=terminal['available_records'];need(set(available)==set(by),'Terminal records do not cover exactly102 modules.')
 current={};selected={};scanned={};actual_guard={}
 def bind_current(path,h):
  path=str(Path(path).resolve())
  if path in current:need(current[path]==h,'Conflicting current input identity: '+path)
  else:need(sha(path)==h,'Current input changed: '+path);current[path]=h
 def current_record(p,u):
  d=json.loads(p.read_text());need(d['status']=='PASS'and d['only_standard_axioms']and d['all_input_provider_postchecks']and d['all_fresh_objects_unchanged_after_audit'],'Incomplete PASS: '+str(p))
  need(d['before']==d['after']and d['source_object_recorded_before_audit'],'Missing input/fresh pre-audit check.')
  need([c['label']for c in d['commands']]==['source','audit']and all(c['exit_code']==0 and not c.get('timed_out',False)for c in d['commands']),'Missing successful source/audit.')
  need(len(d['fresh_modules'])==1,'Unexpected fresh module count.');f=d['fresh_modules'][0]
  need(f['module']==u['module']and f['source_sha256']==u['source_sha256']and d['source_pass_object']==f,'Fresh object identity differs.')
  need((d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']),'Audit census differs.')
  for k in ['source','audit']:
   need(d[k]['sha256']==u[k+'_sha256'],'Selected proof bytes differ.');bind_current(d[k]['path'],d[k]['sha256']);bind_current(d[k]['snapshot'],d[k]['sha256'])
  for p0,h in d['before'].items():bind_current(p0,h)
  bind_current(f['path'],f['sha256'])
  for q in d['actual_first_providers']:
   need(Path(q['actual_first']).resolve()==Path(q['resolved']).resolve(),'First provider path differs.');bind_current(q['actual_first'],q['sha256'])
  need(d['compiler']['sha256']==terminal['compiler']['sha256']and d['compiler']['version']==terminal['compiler']['version'],'Compiler identity differs.')
  for c in d['commands']:need((p.parent/(c['label']+'.log')).read_text()==c['output'],'Raw log differs.')
  reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",d['commands'][1]['output'],re.S)
  need([n for n,_ in reports]==['SetTheory.BusyBeaver.ZFC.SitesPrefix246.'+n for n in u['probe_names']],'Probe order differs.')
  need(all({v.strip()for v in ax.split(',')if v.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Nonstandard axiom.')
  guards=[(Path(p0),h)for p0,h in d['before'].items()if p0.endswith('.py')]
  need(len(guards)==1,'Expected one actual executed coverage guard.');actual_guard[u['module']]=guards[0]
  return d
 for u in units:
  for pk,hk in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:bind_current(u[pk],u[hk])
  ref=available[u['module']];p=Path(ref['path']).resolve();need(p.is_relative_to(B)and sha(p)==ref['sha256'],'Selected raw record identity/root differs.')
  d=current_record(p,u);need(d['fresh_modules'][0]==ref['fresh'],'Terminal fresh reference differs.');selected[u['module']]=(p,d)
 final_module='BusyBeaver.ZFC.SitesPrefix246';fp,fd=selected[final_module]
 need(fd['project_module_count']==125 and len(fd['reused_modules'])==125,'Final closure count differs.')
 providers={q['module']:q for q in fd['reused_modules']};need(len(providers)==125,'Duplicate final providers.')
 closure=[];visiting=set()
 def visit(m):
  if m in closure:return
  need(m in providers and m not in visiting,'Incomplete/cyclic final import closure: '+m);visiting.add(m);q=providers[m]
  bind_current(q['source'],q['source_sha256']);bind_current(q['object'],q['object_sha256'])
  for n in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(q['source']).read_text(),re.M):
   if n!='Init'and not n.startswith(('Lean.','Std.')):visit(n)
  visiting.remove(m);closure.append(m)
 for m in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',Path(fd['source']['path']).read_text(),re.M):visit(m)
 need(set(closure)==set(providers)and len(closure)==125,'Exact final import DFS differs.')
 generated={q['module']:q for q in fd['reused_modules']if q['module']in by}
 need(set(generated)==set(by)-{final_module},'Final closure omits generated ancestors.')
 for m,q in generated.items():
  f=selected[m][1]['fresh_modules'][0];need((q['source_sha256'],q['object_sha256'])==(f['source_sha256'],f['sha256']),'Final provider differs from selected record: '+m)
 # Require a scoped complete-review receipt bound to all selected record bytes.
 review=a.complete_review.resolve();need(sha(review)==a.complete_review_sha,'Complete review hash changed.');rd=json.loads(review.read_text())
 expected_records={m:sha(p)for m,(p,d)in selected.items()}
 need(rd['status']=='PASS_COMPLETE_COVERAGE_EXISTING_EVIDENCE_REVIEW','A source-only/provisional review is insufficient.')
 need(rd['coverage_final_verification_sha256']==sha(fp)and rd['selected_record_sha256_by_module']==expected_records,'Complete review does not bind these102 records.')
 # Enumerate all actual proof records, including unsuccessful/interrupted predecessors.
 for p in sorted(B.rglob('verification.json')):
  if 'publication-design'in p.relative_to(B).parts:continue
  d=json.loads(p.read_text());need(d['status']not in ['RUNNING','PREPARING'],'Unresolved proof record: '+str(p));scanned[str(p.resolve())]=d
 need(all(str(p)in scanned for p,d in selected.values()),'Selected records omitted from history scan.')
 pipelines=[]
 for p in sorted(B.rglob('pipeline.json')):
  if 'publication-design'in p.relative_to(B).parts:continue
  d=json.loads(p.read_text());stale=d['status']=='RUNNING'
  if stale:
   need(p.resolve()==Path(json.loads(recovery.read_text())['pipeline']['path']).resolve()and sha(p)==json.loads(recovery.read_text())['pipeline']['sha256'],'Unclassified interrupted runner.')
  # Apply the attempt-completeness gate to every pipeline, not just stale ones.
  # No absent record is inferred to mean precompiler failure: that would need a
  # separately reviewed evidence-based classification, which this version rejects.
  for x in d['attempts']:
   out=Path(x['output']).resolve();v=out/'verification.json'
   need(out.is_relative_to(B)and str(v)in scanned,'Attempt lacks an archived verification record; explicit no-record classification required: '+str(out))
   need(x['status']!='RUNNING'or stale,'Unclassified RUNNING attempt in terminal pipeline: '+str(out))
   if 'record'in x:
    need(Path(x['record']['path']).resolve()==v and sha(v)==x['record']['sha256'],'Pipeline attempt record binding differs: '+str(out))
   if 'log'in x:
    log=Path(x['log']).resolve();need(log.is_relative_to(B)and sha(log)==x['log_sha256'],'Pipeline driver-log binding differs: '+str(log))
  pipelines.append((p,d,stale))
 # Read everything first, then copy. No original run/source is ever changed.
 O.mkdir();registry={};filemap=[]
 def add(src,target,aliases=(),force=False):
  src=Path(src);data=src.read_bytes();h=hashlib.sha256(data).hexdigest();target=Path(target);need(not target.is_absolute()and '..'not in target.parts,'Unsafe publication target.')
  if h in registry and not force:
   need(registry[h]['bytes']==data,'Hash collision.');registry[h]['original_aliases'].update([str(src),*map(str,aliases)]);return dict(path=registry[h]['published_paths'][0],sha256=h)
  dest=O/target;dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists():need(dest.read_bytes()==data,'Conflicting target.')
  else:dest.write_bytes(data);filemap.append(dict(source=str(dest),target=str(R/target),sha256=h))
  if h not in registry:registry[h]=dict(bytes=data,published_paths=[],original_aliases=set())
  need(registry[h]['bytes']==data,'Hash collision.');registry[h]['published_paths'].append(str(target));registry[h]['original_aliases'].update([str(src),*map(str,aliases)])
  return dict(path=str(target),sha256=h)
 entries=[]
 for u in units:
  m=u['module'];short=m.split('.')[-1];p,d=selected[m];guard,h=actual_guard[m]
  art=dict(source=add(u['source_path'],L/(short+'.lean'),[d['source']['path'],d['source']['snapshot']]),audit=add(u['audit_path'],DEST/'audits'/(short+'.audit.lean'),[d['audit']['path'],d['audit']['snapshot']]),planned_guard=add(u['guard'],DEST/'guards/planned'/(short+'.check.py')),executed_guard=add(guard,DEST/'guards/executed'/(short+'.check.py')),verification=add(p,DEST/'attempts'/p.relative_to(B)))
  entries.append(dict(module=m,kind=u['kind'],probes=u['probes'],callers=u['callers'],probe_names=u['probe_names'],artifacts=art,planned_source_path=u['source_path'],planned_audit_path=u['audit_path'],planned_guard_was_executed=sha(guard)==u['guard_sha256'],generated_direct_dependencies=u['generated_direct_dependencies'],generated_transitive_dependencies=u['generated_transitive_dependencies'],expected_provider_count=u['expected_provider_count'],selected_record_sha256=sha(p),fresh_module=d['fresh_modules'][0],warnings=d['warnings']))
 # Attempt-local files include exact logs and distinct failure/source snapshots.
 attempts=[];text_suffixes={'.json','.lean','.log','.py','.md','.diff','.txt'}
 hash_lookup=None
 def historical(path,h):
  nonlocal hash_lookup
  p=Path(path)
  if p.exists()and sha(p)==h:return p
  if hash_lookup is None:
   hash_lookup={}
   for q in B.rglob('*'):
    if q.is_file()and not q.is_symlink()and q.suffix in text_suffixes and 'cache'not in q.parts and 'publication-design'not in q.relative_to(B).parts:hash_lookup.setdefault(sha(q),q)
  need(h in hash_lookup,'Missing exact historical input bytes: '+path);return hash_lookup[h]
 for pstr,d in scanned.items():
  p=Path(pstr);files=[]
  for q in sorted(p.parent.rglob('*')):
   if q.is_file()and not q.is_symlink()and 'cache'not in q.relative_to(p.parent).parts and q.suffix in text_suffixes:files.append(add(q,DEST/'attempts'/q.relative_to(B)))
  guard_bindings=[]
  for old,h in d.get('before',{}).items():
   if old.endswith('.py'):
    q=historical(old,h);guard_bindings.append(add(q,DEST/'attempts'/p.parent.relative_to(B)/('executed-'+h[:16]+'.py'),[old]))
  proof_bindings={}
  for kind in ['source','audit']:
   if kind not in d:continue
   q=d[kind];h=q['sha256'];need(re.fullmatch('[0-9a-f]{64}',h)is not None,'Malformed historical proof hash.')
   aliases=[q['path']]+([q['snapshot']]if q.get('snapshot')else[])
   for old in aliases:
    if old in d.get('before',{}):need(d['before'][old]==h,'Conflicting historical proof identities: '+old)
   exact=next((Path(old)for old in reversed(aliases)if Path(old).is_file()and sha(old)==h),None)
   if exact is None:exact=historical(q['path'],h)
   need(sha(exact)==h,'Historical proof-byte resolution differs.')
   proof_bindings[kind]=add(exact,DEST/'attempts'/p.parent.relative_to(B)/('recorded-'+kind+'-'+h[:16]+'.lean'),aliases)
  attempts.append(dict(original_record=pstr,status=d['status'],selected=any(p==s for s,x in selected.values()),record=add(p,DEST/'attempts'/p.relative_to(B)),files=files,executed_guard_bindings=guard_bindings,recorded_proof_bindings=proof_bindings,source=d.get('source'),audit=d.get('audit'),fresh_modules=d.get('fresh_modules',[])))
 pipeline_entries=[]
 for p,d,stale in pipelines:
  files=[add(p,DEST/'pipelines'/p.relative_to(B))]
  for q in sorted(p.parent.glob('*')):
   if q.is_file()and(q.name.endswith('.driver.log')or q.name.endswith('.dependencies.json')):files.append(add(q,DEST/'pipelines'/q.relative_to(B)))
  bound_attempts=[]
  for x in d['attempts']:
   v=Path(x['output']).resolve()/'verification.json'
   binding=dict(module=x['module'],raw_attempt_status=x['status'],verification_status=scanned[str(v)]['status'],verification=add(v,DEST/'attempts'/v.relative_to(B)))
   if 'log'in x:
    log=Path(x['log']).resolve();binding['driver_log']=add(log,DEST/'pipelines'/log.relative_to(B))
   bound_attempts.append(binding)
  pipeline_entries.append(dict(record=files[0],raw_status=d['status'],stale_interrupted_history=stale,attempt_bindings=bound_attempts,files=files))
 support=[]
 for q in sorted(B.iterdir()):
  if q.is_file()and q.suffix in text_suffixes:support.append(add(q,DEST/'development'/q.name))
 for dirname in ['recovery-after-session79413','representatives']:
  for q in sorted((B/dirname).rglob('*')):
   if q.is_file()and not q.is_symlink()and q.suffix in text_suffixes:support.append(add(q,DEST/'development'/q.relative_to(B)))
 for dirname,filename in [('plan-single','generation.json'),('guards-single-pending','pipeline-manifest.json'),('guards-single-ready','pipeline-manifest.json')]:
  q=B/dirname/filename
  if q.exists():support.append(add(q,DEST/'plans'/dirname/filename))
 planned=dict(generation=add(gf,DEST/'plans/grouped/generation.json'),pipeline=add(mf,DEST/'plans/grouped/pipeline-manifest.json'))
 programs={name:add(B/name,DEST/'programs'/name,force=True)for name in ['generate_sites_prefix246.py','prepare_plan_guards.py','run_pipeline.py']}
 programs['coverage-guard-template.py']=add(a.template,DEST/'programs/coverage-guard-template.py')
 portable=O/'portable-guard-generator.py';old=(B/'prepare_plan_guards.py').read_text();needle="Path('/tmp/zfc-prefix250-lean/coverage/check.py')";need(old.count(needle)==1,'Template lookup changed.')
 portable.write_text(old.replace(needle,"Path(__file__).with_name('coverage-guard-template.py')"));programs['portable_guard_generator']=add(portable,DEST/'programs/prepare_plan_guards_portable.py')
 import difflib
 delta=O/'portable-guard-generator.diff';delta.write_text(''.join(difflib.unified_diff(old.splitlines(True),portable.read_text().splitlines(True),fromfile='prepare_plan_guards.py',tofile='prepare_plan_guards_portable.py')));programs['portable_guard_generator_diff']=add(delta,DEST/'programs/prepare_plan_guards_portable.diff')
 programs['coordinator_source']=add(H/'portable_coverage.py',DEST/'programs/portable_coverage.py')
 programs['coordinator']=add(H/'portable_coverage.py',Z/'check_prefix246_sites.py',force=True);programs['packet_builder']=add(Path(__file__).resolve(),DEST/'programs/build_packet.py')
 review_binding=add(review,DEST/'reviews/complete-existing-evidence-review.json')
 review_support={}
 for key,name in [('full_binding_review','complete-binding-review.json'),('reviewer_source','complete-reviewer-source.py')]:
  descriptor=rd[key];path=Path(descriptor['path']).resolve()
  need(sha(path)==descriptor['sha256'],'Complete-review supporting artifact changed: '+key)
  review_support[key]=add(path,DEST/'reviews'/name)
 scope_doc=add(H/'prefix246_coverage.md',Z/'prefix246_coverage.md')
 programs['scope_doc_source']=add(H/'prefix246_coverage.md',DEST/'programs/prefix246_coverage.md',force=True)
 for name in ['plan.md','publication-plan.json','endpoint-freeze.json','independent-plan-review.json','PACKER-REVIEW.md']:
  q=H/name
  if q.exists():support.append(add(q,DEST/'development/publication'/name))
 for q in sorted((H/'history').rglob('*')):
  if q.is_file()and q.suffix in text_suffixes:support.append(add(q,DEST/'development/publication'/q.relative_to(H)))
 final_binding=add(fp,Z/'results/prefix246-sites-verification.json',force=True)
 # The selected actual records bind fixed Site and MP parents; preserve exact evidence aliases.
 site=Path(plan['site_evidence']);need(sha(site)==plan['site_evidence_sha256'],'Site parent changed.')
 site_binding=add(site,DEST/'parents/site-verification.json')
 for p,h in current.items():need(sha(p)==h,'Input changed during packaging: '+p)
 content={h:dict(published_paths=v['published_paths'],original_aliases=sorted(v['original_aliases']))for h,v in sorted(registry.items())}
 result=dict(status='EXACT_COMPLETED_COVERAGE_EVIDENCE_PACKET',target='machinePrefix246',canonical_table_sha256='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc',module_count=102,named_axiom_probes=468,typed_callers=468,mathematical_counts={k:generation[k]for k in ['nodes','leaves','guard_cases','decoder_depth','chunks','joins']},final_theorem='SetTheory.BusyBeaver.ZFC.SitesPrefix246.all_sites',scope='Closed coverage for every actual decoder path; final Binary calibration and PA internalization are separate.',units=entries,plans=planned,site_parent=site_binding,final_verification=final_binding,complete_review=review_binding,scope_doc=scope_doc,programs=programs,attempt_history=attempts,pipeline_history=pipeline_entries,supporting_history=support,terminal_pipeline=dict(original_path=str(tp),sha256=sha(tp)),content_registry=content,all_selected_current_inputs_rechecked=True,current_input_paths=len(current),objects_not_published=True,compiler_invoked=False,guard_invoked=False,version_queried=False,provisional_history_note='The immutable50-PASS recovery receipt and later progress/reuse receipts are retained as historical progress; none is the publication gate.',cache_boundary='Exact existing MP/Site project objects and toolchain caches remain prerequisites. Raw historical JSON is never rewritten into a fresh evidence claim.')
 result['complete_review_support']=review_support
 mp=O/'manifest.json';dump(mp,result);filemap.append(dict(source=str(mp),target=str(R/DEST/'manifest.json'),sha256=sha(mp)));dump(O/'file-map.json',filemap)
 print(json.dumps(dict(files=len(filemap),manifest_sha256=sha(mp),file_map_sha256=sha(O/'file-map.json'),complete_modules=102),indent=2))
if __name__=='__main__':main()
