from pathlib import Path
from functools import lru_cache
import json,hashlib,re,subprocess,difflib,copy
ROOT=Path('/home/codex/.codex/worktrees/9c9b/Proofs');BASE=Path('/tmp/gowers-next598-prospective-composition-v2');OUT=Path('/tmp/gowers-next829-prospective-composition');TOOLS=Path('/tmp/gowers-next829-native-tools');PRIOR=Path('/tmp/gowers-next598-native-tools-v2');BERN=Path('/tmp/gowers-bernoulli-powerset-product-reuse-draft');ADD=Path('/tmp/gowers-additive-tuple-three-copy-reuse-research')
assert not OUT.exists() and not TOOLS.exists()
sha=lambda b:hashlib.sha256(b).hexdigest();load=lambda p:json.loads(Path(p).read_text())
br=load(BASE/'report.json');bf=load(BASE/'freeze.json');bs=load(BERN/'summary.json');arows=load(ADD/'source-rows.json');ai=load(ADD/'interfaces.json')
assert sha((BASE/'report.json').read_bytes())=='0b796087b516e64d6392a10c287fe5599816487b73003f07a99b23b6bb83476a'
assert sha((BASE/'freeze.json').read_bytes())=='f20f1e36dddb71742ddbc84e90d988caa3126b14ec5d92e2c5f05ec30b73b8d9'
for p,h in bf['assets'].items():assert sha((BASE/p).read_bytes())==h,p
pins={str(BASE/'report.json'):sha((BASE/'report.json').read_bytes()),str(BASE/'freeze.json'):sha((BASE/'freeze.json').read_bytes())}
assert sha((BERN/'summary.json').read_bytes())=='699a6ead818966083cdac178922711faeb452ae8e9ac41e8ea17c2bb48f364d1'
for p in (BERN/'summary.json',BERN/'changes.patch',Path(bs['draft']),ADD/'source-rows.json',ADD/'interfaces.json',ADD/'changes.patch',ADD/'scope.json'):pins[str(p)]=sha(p.read_bytes())
assert pins[str(ADD/'changes.patch')]=='451158a501fbdc30f81eb090fdb9268f806c0ad6169c3e59d779c94e7ba9a555'
bern_review=Path('/tmp/gowers-bernoulli-powerset-product-reuse-root-review.json')
assert sha(bern_review.read_bytes())=='5a7cb5082aacb5e49d6a3c361d27331181c7ad77e68a2282e230e1e75cb81fe1';pins[str(bern_review)]=sha(bern_review.read_bytes())
parser=Path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py');assert sha(parser.read_bytes())=='8efad41a0a5f1ec5946154a0643920ce1f4bf47f25d1fd85de167cabe2448d1f'
ns={};exec(compile(parser.read_text(),str(parser),'exec'),ns);mask=ns['mask_comments'];pins[str(parser)]=sha(parser.read_bytes())
header_fix='LeanProofs.GowersSzemeredi.theorem10_13_zeta_bound'
def decl(text):
 ds=ns['declarations'](text)
 if header_fix in ds:
  d=ds[header_fix];end=':=\n  theorem10_13_zeta_le_parameterRadius alpha halpha';assert d['block'].endswith(end);d['header']=d['block'][:-len(end)].rstrip()
 return ds
proof=lambda d:len(re.sub(r'^\s*:=\s*by(?:\r?\n|[ \t]+)','',d['block'][len(d['header']):],count=1).strip('\n').splitlines()) if d['kind'] in ('theorem','lemma') and re.match(r'\s*:=\s*by\b',mask(d['block'][len(d['header']):])) else 0
paths={};texts={}
for p in subprocess.check_output(['rg','--files','Combinatorics/Ramsey/Lean','lib/openai-math/lean','-g','*.lean'],cwd=ROOT,text=True).splitlines():
 prefix='Combinatorics/Ramsey/Lean/' if p.startswith('Combinatorics/Ramsey/Lean/') else 'lib/openai-math/lean/'
 m=p[len(prefix):-5].replace('/','.');assert m not in texts;paths[m]=p;texts[m]=(ROOT/p).read_text()
assert len(texts)==6021
baseoverlay={r['module']:Path(r['draft_path']).read_text() for r in br['owners']};overlay=dict(baseoverlay);origins={m:['NEXT598'] for m in baseoverlay};last_sources={r['module']:r['draft_path'] for r in br['owners']}
for r in br['owners']:assert sha(texts[r['module']].encode())==r['baseline_sha256'] and sha(baseoverlay[r['module']].encode())==r['draft_sha256']
bm='GowersSzemeredi.Proofs12BernoulliSelection';assert sha(baseoverlay[bm].encode())==bs['baseline_sha256'];overlay[bm]=Path(bs['draft']).read_text();assert sha(overlay[bm].encode())==bs['draft_sha256'];origins[bm].append('Bernoulli products');last_sources[bm]=bs['draft']
for r in arows:
 m=r['module'];baseline=baseoverlay.get(m,texts[m]);assert sha(baseline.encode())==r['baseline_sha256'] and Path(r['baseline_path']).read_text()==baseline
 overlay[m]=Path(r['draft_path']).read_text();assert sha(overlay[m].encode())==r['draft_sha256'];origins.setdefault(m,[]).append('Additive block reuse');last_sources[m]=r['draft_path'];pins[r['draft_path']]=r['draft_sha256']
assert len(overlay)==13
imports=lambda t:re.findall(r'^import\s+(\S+)',mask(t),re.M)
graph={m:imports(t) for m,t in texts.items()};ng=dict(graph);bg=dict(graph)
for m,t in baseoverlay.items():bg[m]=imports(t)
for m,t in overlay.items():ng[m]=imports(t)
assert ng==bg,'New proposals must preserve the NEXT598 import graph exactly'
def closure_fn(g):
 active=set()
 @lru_cache(None)
 def c(m):
  assert m not in active,('cycle',m);active.add(m)
  v=frozenset({m}).union(*(c(d) for d in g[m] if d in g));active.remove(m);return v
 return c
cb=closure_fn(graph);ca=closure_fn(ng)
for m in texts:cb(m);ca(m)
oldlen={m:len(t.splitlines()) for m,t in texts.items()};newlen={m:len(overlay.get(m,t).splitlines()) for m,t in texts.items()};baselen={m:len(baseoverlay.get(m,t).splitlines()) for m,t in texts.items()}
bds={m:decl(texts[m]) for m in overlay};ads={m:decl(t) for m,t in overlay.items()}
moved_short=['lemma134Left','lemma134Right','lemma134_zero_mem_left','lemma134_zero_notMem_right','lemma134_additive_ext'];moved_names={'LeanProofs.GowersSzemeredi.'+n for n in moved_short};src='GowersSzemeredi.Proofs13InitialProgression';dst='GowersSzemeredi.Proofs00Basics'
moveledger=[]
for name in sorted(moved_names):
 d=bds[src][name];a=ads[dst][name];assert name not in ads[src] and name not in bds[dst]
 assert all(d[k]==a[k] for k in ('kind','header','context','block')),(name,'moved syntax')
 moveledger.append({'name':name,'kind':d['kind'],'old_owner':src,'new_owner':dst,'header':d['header'],'context':d['context'],'header_sha256':sha(d['header'].encode()),'old_block_sha256':sha(d['block'].encode()),'new_block_sha256':sha(a['block'].encode()),'old_line':d['line'],'new_line':a['line'],'proof_lines':proof(d),'exact_block':True})
start=texts[src].index('private def lemma134Left');end=texts[src].index(bds[src]['LeanProofs.GowersSzemeredi.lemma134_additive_ext']['block'])+len(bds[src]['LeanProofs.GowersSzemeredi.lemma134_additive_ext']['block'])
block=texts[src][start:end];assert block in overlay[dst]
# Preserve the author's full53-line moved region, including its separators.
assert sum(1 for _ in block.splitlines())==52
prior_changed={(x['owner'],x['name']) for x in load(BASE/'interfaces.json') if not x['exact_block']}
allowed_changes=prior_changed|{(bm,'LeanProofs.GowersSzemeredi.'+x) for x in ('restrictionWeight_sum','restrictionWeight_event')}
allowed_changes|={(r['module'],name) for r in arows for name in r['changed_callers']}
allowed_removed={(r['owner'],r['name']) for r in load(BASE/'removed-private-declarations.json')}
allowed_removed|={(bm,'LeanProofs.GowersSzemeredi.'+x) for x in ('restrictionWeight_insert','restrictionWeight_not_insert')}
for item in ai.get('removed',ai.get('removed_private',[])):
 owner=item.get('old_owner',item.get('owner'));m=owner if owner.startswith('GowersSzemeredi.') else 'GowersSzemeredi.'+owner
 allowed_removed.add((m,item['name']))
# The exact author deletion list is independently determined if its schema uses another label.
for r in arows:
 m=r['module'];d0=decl(baseoverlay.get(m,texts[m]));d1=ads[m]
 for name,d in d0.items():
  if name not in d1 and name not in moved_names:
   assert d['header'].startswith('private ');allowed_removed.add((m,name))
interfaces=[];removed=[];owners=[]
for m in sorted(overlay):
 bd=bds[m];ad=ads[m]
 assert set(ad)-set(bd)==(moved_names if m==dst else set())
 for name,d in bd.items():
  if name not in ad:
   if m==src and name in moved_names:continue
   assert (m,name) in allowed_removed and d['header'].startswith('private '),(m,name)
   removed.append({'owner':m,'name':name,'kind':d['kind'],'header':d['header'],'context':d['context'],'block_sha256':sha(d['block'].encode()),'proof_lines':proof(d)});continue
  a=ad[name];assert all(d[k]==a[k] for k in ('kind','header','context')),(m,name)
  exact=d['block']==a['block']
  if not exact:assert (m,name) in allowed_changes,(m,name)
  if d['kind'] not in ('theorem','lemma'):assert exact
  interfaces.append({'owner':m,'name':name,'kind':d['kind'],'header':d['header'],'context':d['context'],'header_sha256':sha(d['header'].encode()),'old_block_sha256':sha(d['block'].encode()),'new_block_sha256':sha(a['block'].encode()),'old_line':d['line'],'new_line':a['line'],'proof_lines_before':proof(d),'proof_lines_after':proof(a),'exact_block':exact,'header_boundary_override':name==header_fix})
 owners.append({'module':m,'file':paths[m],'components':origins[m],'component_final_draft':last_sources[m],'baseline_sha256':sha(texts[m].encode()),'NEXT598_overlay_sha256':sha(baseoverlay.get(m,texts[m]).encode()),'draft_sha256':sha(overlay[m].encode()),'draft_path':str(OUT/'draft'/Path(paths[m]).name),'source_lines_before':oldlen[m],'source_lines_after':newlen[m],'source_delta':newlen[m]-oldlen[m],'additional_source_delta_vs598':newlen[m]-baselen[m],'theorem_tactic_delta':sum(map(proof,ad.values()))-sum(map(proof,bd.values())),'term_proof_delta':sum(map(ns['term_lines'],ad.values()))-sum(map(ns['term_lines'],bd.values())),'old_declarations':len(bd),'new_declarations':len(ad),'imports_before':graph[m],'imports_after':ng[m]})
assert sum(r['source_delta'] for r in owners)==-829
assert sum(r['additional_source_delta_vs598'] for r in owners)==-231
assert sum(r['theorem_tactic_delta'] for r in owners)==-691
assert sum(r['term_proof_delta'] for r in owners)==0
assert len(interfaces)==738 and len(moveledger)==5 and len(removed)==26
assert sum(not x['exact_block'] for x in interfaces)==13
assert sum(x['kind'] not in ('theorem','lemma') for x in interfaces)+sum(x['kind'] not in ('theorem','lemma') for x in moveledger)==236
snap_path=Path('/tmp/gowers-next297-repaired6a75-source-snapshot.json');snap=load(snap_path);pins[str(snap_path)]=sha(snap_path.read_bytes())
for p,h in snap['source_hashes'].items():assert sha((ROOT/p).read_bytes())==h,p
plan=load(PRIOR/'plan.json');oldplan=copy.deepcopy(plan);roots=plan['shared']['roots']+plan['supplemental']['roots'];union=lambda rr,f:set().union(*(f(m) for m in rr));fresh=union(roots,ca)
assert [len(v['roots']) for v in plan.values()]==[1,65,18] and len(fresh)==1964
assert fresh==union(roots,closure_fn(bg))
@lru_cache(None)
def oldproof(m):return sum(map(proof,decl(texts[m]).values()))
def newproof(m):return sum(map(proof,ads[m].values())) if m in ads else oldproof(m)
def measure(rr):
 b=union(rr,cb);a=union(rr,ca)
 pd=sum(newproof(m)-oldproof(m) for m in set(overlay)&a&b)+sum(newproof(m) for m in a-b)-sum(oldproof(m) for m in b-a)
 return {'roots':rr,'module_count':len(a),'input_count':len(a)+3,'source_lines':sum(newlen[m] for m in a),'source_lines_NEXT598':sum(baselen[m] for m in a),'additional_source_delta_vs598':sum(newlen[m]-baselen[m] for m in a),'baseline_module_count':len(b),'baseline_source_lines':sum(oldlen[m] for m in b),'source_delta_same_roots':sum(newlen[m] for m in a)-sum(oldlen[m] for m in b),'theorem_tactic_delta_same_roots':pd,'added_modules':sorted(a-b),'removed_modules':sorted(b-a)}
routes={k:measure(v['roots']) for k,v in plan.items()};routes.update(original_final=measure(['GowersSzemeredi.Final']),stronger_final=measure(['GowersSzemeredi.Proofs18CoverFejerAllDegrees']),union=measure(roots))
for k in plan:
 for field in ('module_count','input_count','source_lines'):plan[k][field]=routes[k][field]
assert all(plan[k]['roots']==oldplan[k]['roots'] for k in plan)
assert all(plan[k][f]==oldplan[k][f] for k in plan for f in ('module_count','input_count'))
consumers=[]
for m in sorted(texts):
 a=ca(m);b=cb(m)
 if set(overlay)&(a|b):consumers.append({'module':m,'baseline_modules':len(b),'prospective_modules':len(a),'source_delta':sum(newlen[x] for x in a)-sum(oldlen[x] for x in b),'additional_source_delta_vs598':sum(newlen[x]-baselen[x] for x in a),'covered_by_fresh_union':m in fresh})
outside=[x['module'] for x in consumers if not x['covered_by_fresh_union']];assert outside==['GowersSzemeredi','GowersSzemeredi.Audit','GowersSzemeredi.PortImportAudit']
# Reproject complete inventory from current repository, never stacking shifts.
invpath=ROOT/'Combinatorics/Ramsey/gowers-proof-status.json';inv=load(invpath);proj=copy.deepcopy(inv);changes=[];byfile={paths[m]:m for m in overlay}
def walk(v,path=[]):
 if isinstance(v,dict):
  if v.get('file') in byfile and 'line' in v:
   m=byfile[v['file']];short=v.get('name',v.get('statement'));names=[n for n in bds[m] if n.rsplit('.',1)[-1]==short];assert len(names)==1,(path,short)
   name=names[0];assert v['line']==bds[m][name]['line'];target=dst if m==src and name in moved_names else m;assert name in ads[target]
   for field,new in [('file',paths[target]),('line',ads[target][name]['line'])]:
    if v[field]!=new:changes.append({'path':path+[field],'name':short,'before':v[field],'after':new});v[field]=new
  for k,w in v.items():walk(w,path+[k])
 elif isinstance(v,list):
  for i,w in enumerate(v):walk(w,path+[i])
walk(proj)
def diff(a,b,path=[]):
 assert type(a)is type(b)
 if isinstance(a,dict):assert list(a)==list(b);return sum((diff(a[k],b[k],path+[k]) for k in a),[])
 if isinstance(a,list):assert len(a)==len(b);return sum((diff(x,y,path+[i]) for i,(x,y) in enumerate(zip(a,b))),[])
 return [] if a==b else [{'path':path,'before':a,'after':b}]
assert diff(inv,proj)==[{k:r[k] for k in ('path','before','after')} for r in changes]
assert len(inv['statements'])==120
occ=lambda x:sum(len(r.get('exact_companions',[]))+len(r.get('related_theorems',[])) for r in x['statements']);assert occ(inv)==occ(proj)==544
coverage=load(BASE/'fresh-coverage.json');retpath=Path(coverage['historical_review_path']);ret=load(retpath);allinputs={};futureinputs={};histmods=set();scopes=[]
for s in ret['retained_scope_candidates']:
 rr=s['root'];own=ca(rr);assert own==cb(rr) and own<=fresh;histmods.update(own)
 expected={paths[m] for m in own}|{'Combinatorics/Ramsey/scripts/check_gowers.py','lean-toolchain','lake-manifest.json'};assert expected==set(s['own_input_map'])
 changed=[]
 for p,h in s['own_input_map'].items():
  assert sha((ROOT/p).read_bytes())==h;assert p not in allinputs or allinputs[p]==h;allinputs[p]=h
  m=byfile.get(p);new=sha(overlay[m].encode()) if m else h;futureinputs[p]=new
  if new!=h:changed.append({'file':p,'historical_sha256':h,'prospective_sha256':new})
 scopes.append({'root':rr,'module_count':len(own),'input_count':len(expected),'prospective_source_lines':sum(newlen[m] for m in own),'changed_source_inputs':changed,'all_modules_in_fresh_union':True,'future_attribution':'prospective shared65 invocation, not historical retention'})
assert len(allinputs)==128 and len(histmods)==125 and histmods<=fresh
coverage.update(status='PROSPECTIVE_NEXT829_ALL_SEVEN_SCOPES_FRESH_NATIVE_UNTESTED',scope_rows=scopes,historical_union_source_map=allinputs,prospective_union_source_map=futureinputs)
# Bind the finalized additive report and accepted independent static review.
add_notes={}
for p in [ADD/'report.json',ADD/'freeze.json',Path('/tmp/gowers-additive-tuple-three-copy-reuse-independent-review/report.json'),Path('/tmp/gowers-additive-tuple-three-copy-reuse-independent-review.json')]:
 if p.exists():pins[str(p)]=sha(p.read_bytes());add_notes[str(p)]=sha(p.read_bytes())
assert add_notes[str(ADD/'report.json')]=='cb75dda15d4b7f3f22c4d640f8af6ebe202f402d565380770e1074e9dcf1207a'
assert add_notes['/tmp/gowers-additive-tuple-three-copy-reuse-independent-review/report.json']=='50c7b9a4f9749d1992f76c399a124a20638103b4fc2d52a432160a15841f5aa1'
for p,h in pins.items():assert sha(Path(p).read_bytes())==h,('input changed',p)
OUT.mkdir();(OUT/'draft').mkdir()
for m,t in overlay.items():(OUT/'draft'/Path(paths[m]).name).write_text(t)
def write(p,v):Path(p).write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n')
patch=''.join(''.join(difflib.unified_diff(texts[m].splitlines(True),overlay[m].splitlines(True),fromfile='a/'+paths[m],tofile='b/'+paths[m])) for m in sorted(overlay));(OUT/'changes.patch').write_text(patch)
for name,v in [('interfaces.json',interfaces),('moved-declarations.json',moveledger),('removed-private-declarations.json',removed),('consumer-costs.json',consumers),('routes.json',routes),('inventory-projected.json',proj),('inventory-changes.json',changes),('fresh-coverage.json',coverage)]:write(OUT/name,v)
report={'status':'FROZEN_PROSPECTIVE_SOURCE_COMPOSITION_COMPONENTS_STATICALLY_ACCEPTED_NATIVE_UNTESTED','baseline_source_commit':snap['source_commit'],'actual_future_source_commit':None,'base_package':{'report':str(BASE/'report.json'),'sha256':pins[str(BASE/'report.json')],'freeze_sha256':pins[str(BASE/'freeze.json')]},'Bernoulli':{'summary':str(BERN/'summary.json'),'summary_sha256':pins[str(BERN/'summary.json')],'root_review':str(bern_review),'root_review_sha256':pins[str(bern_review)]},'additive':{'directory':str(ADD),'source_rows_sha256':pins[str(ADD/'source-rows.json')],'interfaces_sha256':pins[str(ADD/'interfaces.json')],'patch_sha256':pins[str(ADD/'changes.patch')],'captured_notes':add_notes,'acceptance':'Root accepted the source-only additive proposal after its independently passing review; combined source remains unapplied and native untested.'},'owners':owners,'source_ledger':{'production_owners':13,'source_lines_delta':-829,'theorem_tactic_lines_delta':-691,'term_proof_delta':0,'additional_source_delta_vs598':-231,'additional_theorem_tactic_delta_vs598':-195,'old_declarations':sum(len(d) for d in bds.values()),'retained_complete_same_owner_headers':len(interfaces),'moved_complete_headers':5,'total_retained_complete_headers':len(interfaces)+5,'retained_non_theorem_blocks_including_moves':236,'removed_private_declarations':26,'changed_retained_proof_blocks':13,'moved_existing_declarations':5,'new_declarations':0},'composition_identity':{'all13_final_owner_bytes_match_the_selected_component_drafts':True,'overlap_baselines_checked_against_NEXT598_not_current_sources':True,'all_other_NEXT598_drafts_preserved':True,'new_import_changes_beyond_NEXT598':0,'complete_let_header_correction_preserved':br['header_reporting_correction']},'moves':{'from':src,'to':dst,'names':sorted(moved_names),'all_headers_contexts_full_blocks_exact':True,'public_name_retained':True,'note':'Four supporting private declarations move with the existing public lemma; this is not a new helper block.'},'routes':routes,'scope':{'full_source_graph_modules':6021,'gowers_oai_modules':5983,'acyclic_before_and_after':True,'module_graph_identical_to_NEXT598':True,'affected_consumers':len(consumers),'covered':len(consumers)-len(outside),'outside':outside,'source_growing_consumers':sum(x['source_delta']>0 for x in consumers),'maximum_source_growth':max(x['source_delta'] for x in consumers),'additional_source_growing_vs598':sum(x['additional_source_delta_vs598']>0 for x in consumers),'maximum_additional_source_growth_vs598':max(x['additional_source_delta_vs598'] for x in consumers),'mode_root_counts':[1,65,18],'ordered_roots_identical_to_NEXT598':True,'fresh_union_modules':1964,'fresh_union_inputs':1967,'all125_historical_modules_in_fresh_union':True,'all128_current_historical_source_pins_match':True,'future_historical_retention_used':False},'inventory':{'baseline_sha256':sha(invpath.read_bytes()),'rows':120,'companion_occurrences':544,'changed_leaves':len(changes),'file_changes':sum(x['path'][-1]=='file' for x in changes),'line_changes':sum(x['path'][-1]=='line' for x in changes),'projection':'inventory-projected.json','changes':'inventory-changes.json','all_other_objects_values_keys_order_duplicates_preserved':True,'generator_not_run':True},'authorship':'Source composition and metric author also authored earlier import components and reviewed JT3; this package is not an independent mathematical review of the additional additive candidate.','limitations':['Root authorized prospective preparation only; component static acceptance is complete, while combined review and actual source application remain pending.','No future source commit, native outcome, inventory regeneration or publication evidence is supplied.','No runtime/capture/preflight/native/compiler invocation, live-artifact access or repo/Git/source/cache mutation.','Only new /tmp composition/tool assets are written; all prior components and NEXT598 remain immutable.']}
write(OUT/'report.json',report)
(OUT/'README.txt').write_text('Prospective NEXT829 over exact NEXT598 v2: Bernoulli finite-product identities plus exact relocation/reuse of five additive-tuple declarations. Thirteen owner drafts;829 source and691 theorem tactic lines removed. All84 ordered root entries (1/65/18) preserved;1964 modules are planned for fresh validation.\n\nComponent static reviews are bound; no source application or native outcome is claimed. Exact source moves, full headers, early-consumer growth and ordered inventory locations are recorded. Prior packages remain unchanged.\n')
write(OUT/'freeze.json',{'status':'FROZEN_PROSPECTIVE_COMPONENTS_STATICALLY_ACCEPTED','assets':{str(p.relative_to(OUT)):sha(p.read_bytes()) for p in sorted(OUT.rglob('*')) if p.is_file()},'external_pins':pins,'builder':str(Path(__file__)),'builder_sha256':sha(Path(__file__).read_bytes())})
TOOLS.mkdir();codehashes={}
for name,want in {'common.py':'4c71aedd3ec630046fd5dd5d205e250893c93bb0b1f1d2b0faf69bfe89e07328','capture.py':'8463cc8e288255e12fd9ad777f8a2fe7f0a75aa6cbf888f423129a112f6cecd2','run.py':'bf1aa169ed14fc098fd20c57a93a8c9904718bfc2b2648997384a3effd61e83a'}.items():
 b=(PRIOR/name).read_bytes();assert sha(b)==want;(TOOLS/name).write_bytes(b);codehashes[name]=want
write(TOOLS/'plan.json',plan)
(TOOLS/'plan.diff').write_text(''.join(difflib.unified_diff((PRIOR/'plan.json').read_text().splitlines(True),(TOOLS/'plan.json').read_text().splitlines(True),fromfile=str(PRIOR/'plan.json'),tofile=str(TOOLS/'plan.json'))))
planchanges=[{'mode':m,'field':k,'before':oldplan[m][k],'after':plan[m][k]} for m in plan for k in plan[m] if oldplan[m][k]!=plan[m][k]]
assert all(x['field']=='source_lines' for x in planchanges)
write(TOOLS/'measurement.json',{'status':'PROSPECTIVE_DATA_ONLY_COMPONENTS_STATICALLY_ACCEPTED_NO_EXECUTION','composition_report':str(OUT/'report.json'),'composition_sha256':sha((OUT/'report.json').read_bytes()),'composition_freeze_sha256':sha((OUT/'freeze.json').read_bytes()),'actual_future_source_commit':None,'runtime_source_directory':str(PRIOR),'runtime_files_byte_identical':codehashes,'prior_plan_sha256':sha((PRIOR/'plan.json').read_bytes()),'exact_plan_changes':planchanges,'root_counts':[1,65,18],'root_entries':84,'all_ordered_roots_and_module_input_counts_unchanged':True,'mode_metrics':{k:{f:routes[k][f] for f in ('module_count','input_count','source_lines')} for k in plan},'union':{f:routes['union'][f] for f in ('module_count','input_count','source_lines')},'source_owner_hashes':{o['file']:o['draft_sha256'] for o in owners},'future_historical_retention_used':False,'required_before_use':['Independently review the exact combined source and prospective plan.','Apply/commit source, recheck actual configuration/inventory, and capture a fresh snapshot.','Run actual sequential core/shared65/supplemental18 in fresh attempt directories.'],'no_runtime_native_or_live_artifact_actions':True})
(TOOLS/'README.txt').write_text('Prospective NEXT829 data-only plan. Runtime code byte-identical to NEXT598/NEXT297. All1/65/18 ordered roots and module/input counts preserved; only measured source-line totals change.\nNo future sourcecommit or snapshot is bound. Combined independent/root review, source application and actual native checks remain required. No historical retention is used for the future1964-module scope.\n')
write(TOOLS/'freeze.json',{'status':'FROZEN_PROSPECTIVE_PLAN_COMPONENTS_STATICALLY_ACCEPTED','files':{p.name:sha(p.read_bytes()) for p in sorted(TOOLS.iterdir()) if p.is_file()}})
for directory in (OUT,TOOLS):
 for p in directory.rglob('*'):
  if p.is_file():p.chmod(0o444)
print(json.dumps({'composition':str(OUT),'report_sha256':sha((OUT/'report.json').read_bytes()),'freeze_sha256':sha((OUT/'freeze.json').read_bytes()),'patch_sha256':sha((OUT/'changes.patch').read_bytes()),'tools':str(TOOLS),'plan_sha256':sha((TOOLS/'plan.json').read_bytes()),'measurement_sha256':sha((TOOLS/'measurement.json').read_bytes()),'tools_freeze_sha256':sha((TOOLS/'freeze.json').read_bytes()),'metrics':{k:{f:v[f] for f in ('module_count','input_count','source_lines','additional_source_delta_vs598','source_delta_same_roots','theorem_tactic_delta_same_roots')} for k,v in routes.items()},'source_ledger':report['source_ledger'],'scope':report['scope'],'inventory':report['inventory'],'additive_notes':add_notes},indent=2))
