"""Static generated-plan review, independent of proof compilation."""
from pathlib import Path
import ast,hashlib,importlib.util,json,re,sys
B=Path('/tmp/zfc-prefix246-lean/coverage');R=Path('/home/codex/.codex/worktrees/ec20/Proofs');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
gen=B/'generate_sites_prefix246.py';spec=importlib.util.spec_from_file_location('coverage246_generator',gen);mod=importlib.util.module_from_spec(spec);sys.modules[spec.name]=mod;spec.loader.exec_module(mod)
single=json.loads((B/'plan-single/generation.json').read_text());old=json.loads(Path('/tmp/zfc-prefix250-lean/coverage/generated/generation.json').read_text());reps=json.loads((B/'representatives/generation.json').read_text())
keys=['index','path','nodes','leaves','guards','depth','theorem']
assert [{k:q[k]for k in keys}for q in single['cut_frontier']]==[{k:q[k]for k in keys}for q in old['cut_frontier']]
assert single['chunks']==233 and single['joins']==232 and single['selected_units']==249
for c in single['cut_frontier']:
 assert c['guards']<=64
 for d in single['cut_frontier']:
  if c is not d:assert c['path']!=d['path'][:len(c['path'])]
assert sum(c['leaves']for c in single['cut_frontier'])==6460 and sum(c['guards']for c in single['cut_frontier'])==8391
for u in reps['units']:
 full=next(v for v in single['units']if v['module']==u['module']);assert u['source_sha256']==full['source_sha256'] and u['audit_sha256']==full['audit_sha256']
for u in single['units']:
 s=B/'plan-single'/u['source'];a=B/'plan-single'/u['audit'];assert sha(s)==u['source_sha256'] and sha(a)==u['audit_sha256']
 assert not re.search(r'\b(native_decide|sorry|admit)\b|set_option\s+max(?:Heartbeats|RecDepth)',s.read_text()+a.read_text())
 assert re.findall(r'^#print axioms (\S+)',a.read_text(),re.M)==['SetTheory.BusyBeaver.ZFC.SitesPrefix246.'+n for n in u['probe_names']]
 assert len(re.findall(r'^example\b',a.read_text(),re.M))==u['callers']
final=single['units'][-1];assert final['probes']==final['callers']==3 and final['probe_names']==['all_sites','actual_walk_checked','actual_walk_exists']
manifest=json.loads((B/'guards-single-pending/pipeline-manifest.json').read_text());known=set()
for u in manifest['units']:
 assert sha(u['guard'])==u['guard_sha256'];t=Path(u['guard']).read_text();ast.parse(t)
 assert set(u['generated_direct_dependencies'])<=known and u['expected_provider_count']==24+len(u['generated_transitive_dependencies']);known.add(u['module'])
 assert repr(u['source_path']) in t and repr(u['audit_path'])in t and repr(u['source_sha256'])in t and repr(u['audit_sha256'])in t
 assert f"CALLERS={u['callers']}" in t and f"PROBES={u['probe_names']!r}"in t
 assert 'PENDING_EXACT_SITE246_PASS'in t
# Adaptive grouping keeps exact cuts/propositions and isolated representative proof bytes.
groupings=[]
for n,budget in [(4,128),(8,256),(16,512)]:
 files,p=mod.build_plan(R,64,16,n,budget,False)
 assert [{k:q[k]for k in keys}for q in p['cut_frontier']]==[{k:q[k]for k in keys}for q in single['cut_frontier']]
 allcuts=[i for u in p['units']if u['kind']=='closed_cuts'for i in u['cuts']];assert allcuts==list(range(233))
 for u in p['units']:
  if u['kind']=='closed_cuts':assert len(u['cuts'])<=n and u['guards']<=budget
 for u in reps['units']:assert hashlib.sha256(files[u['source']]).hexdigest()==u['source_sha256'] and hashlib.sha256(files[u['audit']]).hexdigest()==u['audit_sha256']
 groupings.append(dict(max_cuts=n,max_guards=budget,cut_modules=sum(u['kind']=='closed_cuts'for u in p['units']),all_modules=len(p['units'])))
# Both child edges occur in every structural join; exact named root consumes all cuts.
uses={('cut',i): 0 for i in range(233)}|{('join',i): 0 for i in range(232)}
for j in single['join_plan']:
 for side,bit in [('left',False),('right',True)]:
  tag,i=j[side];child=(single['cut_frontier']if tag=='cut'else single['join_plan'])[i];assert child['path']==j['path']+[bit];uses[tag,i]+=1
assert uses['join',231]==0 and all(v==1 for k,v in uses.items()if k!=('join',231)) and single['join_plan'][-1]['path']==[]
r=dict(status='STATIC_SOURCE_REVIEW_ONLY_NO_EXECUTION',generator_sha256=sha(gen),pipeline_sha256=sha(B/'run_pipeline.py'),guard_generator_sha256=sha(B/'prepare_plan_guards.py'),fixed_frontier=dict(cuts=233,joins=232,leaves=6460,guards=8391,exact250_frontier_identity=True),representative_indices=[0,42,210],representative_bytes_equal_full_plan=True,final_audit_probes=3,final_typed_callers=3,ungrouped_units=249,grouping_options=groupings,all_source_audit_hashes_checked=True,all_guard_syntax_and_metadata_checked=True,both_children_required_at_every_join=True,all_nonroot_proofs_used_once=True,compiler_invoked=False,version_queried=False,guard_invoked=False,pending='Actual Site246 PASS pin, root review and representative timing measurements before choosing grouping; no generated coverage theorem has been executed by this script.')
(B/'static-pipeline-review.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
