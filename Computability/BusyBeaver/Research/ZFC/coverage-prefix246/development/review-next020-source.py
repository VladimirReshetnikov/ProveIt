"""Static source and existing-evidence review; never runs generated proof guards."""
from pathlib import Path
import ast,hashlib,json,re
B=Path('/tmp/zfc-prefix246-lean/coverage');M=B/'guards-four/pipeline-manifest.json';P=B/'plan-four/generation.json';U=B/'grouped-four-reuse-014.json';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=json.loads(M.read_text());p=json.loads(P.read_text());assert sha(P)==m['plan_sha256'];assert sha(m['site_evidence'])==m['site_evidence_sha256'];assert m['status']=='GUARDS_FROZEN_READY' and m['full_plan'];units={x['module']:x for x in m['units']};planunits={x['module']:x for x in p['units']};known={};refs=0;bindings={}
for name in json.loads(U.read_text()):
 r=json.loads(Path(name).read_text());assert r['status']=='PASS' and r['only_standard_axioms'] and r['all_input_provider_postchecks'] and r['all_fresh_objects_unchanged_after_audit'] and r['source_object_recorded_before_audit'];assert r['before']==r['after'];f=r['fresh_modules'][0];assert len(r['fresh_modules'])==1 and r['source_pass_object']==f;unit=units[f['module']];assert r['source']['sha256']==unit['source_sha256'] and r['audit']['sha256']==unit['audit_sha256'];assert r['named_axiom_probes']==unit['probes'] and r['callers']==unit['callers'];assert [x['label'] for x in r['commands']]==['source','audit'] and all(x['exit_code']==0 for x in r['commands']);assert all(v==0 for v in r['warnings'].values())
 for path,h in r['before'].items():assert sha(path)==h;refs+=1;bindings[path]=h
 for kind in ['source','audit']:assert sha(r[kind]['path'])==sha(r[kind]['snapshot'])==r[kind]['sha256']
 for x in r['actual_first_providers']:assert Path(x['actual_first']).resolve()==Path(x['resolved']).resolve() and sha(x['actual_first'])==x['sha256']
 assert sha(f['path'])==f['sha256'] and f['source_sha256']==unit['source_sha256'];assert f['module'] not in known;known[f['module']]={'path':name,'sha256':sha(name),'fresh_object_sha256':f['sha256']}
assert len(known)==14
nexts=[x for x in m['units'] if x['module'] not in known][:20];assert len(nexts)==20
ns='SetTheory.BusyBeaver.ZFC.SitesPrefix246.'
def bits(path):return '['+', '.join('true' if x else 'false' for x in path)+']'
def goal(path):return 'allSites SitePrefix246.checkSite '+bits(path[::-1])+'\n      (descend ActualTree254.tree '+bits(path)+') = true'
def normalized_guard(text,u):
 tree=ast.parse(text)
 for node in tree.body:
  if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name):
   key=node.targets[0].id
   if key in ['MODULE','SOURCE_SHA','AUDIT_SHA','PROBES','CALLERS']:
    expected={'MODULE':u['module'],'SOURCE_SHA':u['source_sha256'],'AUDIT_SHA':u['audit_sha256'],'PROBES':u['probe_names'],'CALLERS':u['callers']}[key];assert ast.literal_eval(node.value)==expected;node.value=ast.Constant(value='UNIT_METADATA')
   elif key in ['S','A']:
    var='source' if key=='S' else 'audit';path=u[var+'_path'];expected=ast.parse(key+'=a.'+var+'.resolve() if a.'+var+' else Path('+repr(path)+')').body[0];assert ast.dump(node)==ast.dump(expected);node.value=ast.Constant(value='UNIT_PATH')
 if isinstance(tree.body[0],ast.Expr) and isinstance(tree.body[0].value,ast.Constant):tree.body[0].value=ast.Constant(value='UNIT_DOCSTRING')
 return ast.dump(tree,include_attributes=False)
base=units['BusyBeaver.ZFC.SitesPrefix246Batch011'];baseline=normalized_guard(Path(base['guard']).read_text(),base)
source_template=Path(base['source_path']).read_text();header=source_template[:source_template.index('/-- Cut')];tail='\nend SetTheory.BusyBeaver.ZFC.SitesPrefix246\n'
selection=[];cutids=[]
for u in nexts:
 for k,v in planunits[u['module']].items():assert u[k]==v
 for pathkey,hashkey in [('source_path','source_sha256'),('audit_path','audit_sha256'),('guard','guard_sha256')]:assert sha(u[pathkey])==u[hashkey]
 assert u['kind']=='closed_cuts' and not u['generated_direct_dependencies'] and not u['generated_transitive_dependencies'] and u['expected_provider_count']==24
 assert len(u['cuts'])<=4 and u['probes']==u['callers']==len(u['cuts']);assert u['guards']==sum(p['cut_frontier'][i]['guards'] for i in u['cuts'])<=128;assert u['leaves']==sum(p['cut_frontier'][i]['leaves'] for i in u['cuts'])
 src=Path(u['source_path']).read_text();aud=Path(u['audit_path']).read_text();guard=Path(u['guard']).read_text();assert normalized_guard(guard,u)==baseline
 expected=header
 for i in u['cuts']:
  c=p['cut_frontier'][i];expected+=f"/-- Cut {i}: {c['leaves']} leaves, {c['guards']} guards. -/\ntheorem block_{i} :\n    {goal(c['path'])} := by decide +kernel\n\n";cutids.append(i)
 expected+=tail;assert src==expected,'source pattern '+u['module']
 expected_a='import '+u['module']+'\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesPrefix246\n\n'+'\n'.join('#print axioms '+ns+n for n in u['probe_names'])+'\n\n'+'\n\n'.join('example : '+goal(p['cut_frontier'][i]['path'])+f' := block_{i}' for i in u['cuts'])+'\n';assert aud==expected_a,'audit pattern '+u['module']
 assert u['probe_names']==['block_'+str(i) for i in u['cuts']]
 selection.append({k:u[k] for k in ['module','source_path','source_sha256','audit_path','audit_sha256','guard','guard_sha256','cuts','guards','leaves','probes','callers','expected_provider_count']})
assert cutids==[i for i in range(39,98) if i!=42]
record={'status':'SOURCE_ONLY_NEXT20_REVIEW_PASS_NOT_EXECUTED','manifest':{'path':str(M),'sha256':sha(M)},'generation':{'path':str(P),'sha256':sha(P)},'reuse_list':{'path':str(U),'sha256':sha(U)},'runner':{'path':str(B/'run_pipeline.py'),'sha256':sha(B/'run_pipeline.py')},'existing_PASS_records':known,'existing_input_references_rechecked':refs,'distinct_existing_input_paths':len(bindings),'selected_units':selection,'totals':{'new_units':20,'cut_theorems':len(cutids),'guard_cases':sum(x['guards'] for x in nexts),'leaves':sum(x['leaves'] for x in nexts),'max_guards_per_new_unit':max(x['guards'] for x in nexts)},'source_pattern':'Every complete source reconstructed byte-for-byte from the frozen actual-tree path and its reversal; only closed allSites equations proved by decide +kernel. Every complete audit reconstructed, with exact corresponding typed caller.','guard_pattern':'All20 guards have identical Python AST to checked Batch011 except explicitly checked docstring/module/hash/probe/caller/default-source-path metadata. All provider, limit, proof and postcheck logic identical.','limits':{'shared_source_audit_seconds_per_unit':120,'threads':1,'memory_mebibytes':4096,'proof_limits':'Lean defaults'},'execution_here':{'proof_guard':False,'runner':False,'compiler':False,'version_query':False},'scope':'Readiness for20 independent closed-cut checks; no new coverage proofs or full all-sites endpoint are claimed.'}
review=B/'grouped-four-next020-source-review.json';review.write_text(json.dumps(record,indent=2)+'\n');sel=B/'grouped-four-next020-selection.json';sel.write_text(json.dumps({'manifest_sha256':sha(M),'reuse_list_sha256':sha(U),'review_sha256':sha(review),'modules':[x['module'] for x in selection],'units':selection},indent=2)+'\n');print(json.dumps({'review':str(review),'review_sha256':sha(review),'selection':str(sel),'selection_sha256':sha(sel),'totals':record['totals'],'reused_records':len(known),'existing_input_references':refs,'runner_sha256':sha(B/'run_pipeline.py'),'manifest_sha256':sha(M),'reuse_list_sha256':sha(U)},indent=2))
