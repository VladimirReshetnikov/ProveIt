"""Own read-only evidence reviewer, writing only this scratch review directory."""
from pathlib import Path
import hashlib,io,json,zipfile
E=Path('/tmp/zfc-intake187/opening-execution');R=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
desc=lambda p:dict(path=str(p),sha256=sha(p),bytes=Path(p).stat().st_size)
record=json.loads((E/'result.json').read_text());plan=json.loads((E/'plan.json').read_text());C=Path(plan['packet']);O=E/'output'
assert record['status']=='FRESH_DIRECT_LEAVES_PASS' and len(record['jobs'])==14
assert record['input_pins_after_unchanged'] and record['runtime_records_equal_except_elapsed_seconds']
assert record['plan_sha256']==sha(E/'plan.json')
for p,h in plan['inputs'].items():assert sha(p)==h
for j in record['jobs']:
 assert j['returncode']==0 and not j['timed_out'] and j['seconds']<j['timeout_seconds']
 assert sha(j['stdout'])==j['stdout_sha256'] and sha(j['stderr'])==j['stderr_sha256']
 assert Path(j['stderr']).read_bytes()==b''
# Bind the selected cached copies to their actual members in this new archive's ancestry.
p=E/'recovered/K219_Construction_2026-10-20/portable/vendor/K220_Construction_2026-10-20.zip'
with zipfile.ZipFile(p)as z:
 names=[n for n in z.namelist()if n.endswith('/K221_Construction_2026-10-20.zip')];assert len(names)==1
 raw=z.read(names[0])
with zipfile.ZipFile(io.BytesIO(raw))as z:
 for tail,target in [('portable/runtime/vendor/symbolic_runtime.py',E/'runtime-vendor/symbolic_runtime.py'),('portable/runtime/vendor/independent_runtime.py',E/'runtime-vendor/independent_runtime.py'),('portable/runtime/reference_results/legacy_mapping.json',E/'legacy_mapping.json')]:
  names=[n for n in z.namelist()if n.endswith('/'+tail)];assert len(names)==1 and z.read(names[0])==target.read_bytes()
summary={};bindings=[]
for name,cases,steps in [('zero_terminal',6175,313845),('retagged',6167,312707),('composed',6175,314043)]:
 d=O/'certificates'/name;s=json.loads((O/'machine'/name/'sites.json').read_text());a=json.loads((d/'runtime.json').read_text());b=json.loads((d/'startup.json').read_text());c=json.loads((d/'integrity.json').read_text());xs=json.loads((d/'cases.json').read_text())
 assert a['status']=='ALL_GENERIC_PRIMITIVE_INTERFACES_PROVED' and a['failures']==[] and a['generic_cases_excluded']==0
 expected=[(i,v)for i,(_,op,_)in enumerate(s)for v in ((False,True)if op=='CD'else(False,))]
 assert [(x['index'],x['positive'])for x in xs]==expected and len(xs)==cases==a['cases']==a['expected_cases']
 assert sum(x['symbolic_steps']for x in xs)==a['symbolic_steps']
 assert all(len(x['duration'])==13 and x['duration'][0]>0 and all(type(t)is int and t>=0 for t in x['duration'])for x in xs)
 assert len(a['directly_used_rows'])==438 and len(set(map(tuple,a['directly_used_rows'])))==438
 assert c['status']=='INDEPENDENT_EXACT_TABLE_UNBOUNDED_STARTUP_AUDIT_PASS' and c['generic_cases']==cases and c['directly_used_rows']==438
 for f,h in c['hashes'].items():assert sha(d/f)==h
 assert b['status']=='INDEPENDENT_EXACT_TABLE_STARTUP_CENSUS_PASS' and b['states']==219 and b['rows']==438
 boot=b['startup'];assert boot['steps']==steps and boot['state']==84 and boot['head']==-5 and len(boot['ones'])==277 and boot['all_other_cells']==0
 assert boot['logical_registers']==[3,0,0,0,3,0,0,0,0] and boot['spares']==[1]*130 and boot['sparse_and_dense_agree']
 assert a['table_sha256']==sha(O/'machine'/name/'k219.native.tm') and a['source_sha256']==sha(O/'machine'/name/'sites.json')
 for f in ('source.json','startup.json','cases.json','canonical.tm'):assert (d/f).read_bytes()==(C/'certificates'/name/f).read_bytes()
 summary[name]={'states':219,'rows':438,'leaf_occurrences':len(s),'generic_cases':cases,'symbolic_steps':a['symbolic_steps'],'startup_steps':steps,'startup_one_cells':277,'seconds':next(j['seconds']for j in record['jobs']if j['name']=='06_runtime_'+name),'generic_cases_excluded':0,'table':desc(O/'machine'/name/'k219.native.tm'),'source':desc(O/'machine'/name/'sites.json')}
 bindings += [desc(d/f)for f in ('source.json','runtime.json','startup.json','cases.json','integrity.json')]
ind=json.loads((O/'independent-runtime.json').read_text());assert ind['status']=='INDEPENDENT_RUNTIME_RECEIPTS_AND_FOUR_BLOCKS_PASS'
neg=json.loads((O/'negative-controls.json').read_text());assert neg['status']=='ALL_NEGATIVE_CONTROLS_REJECTED' and neg['count']==10 and all(x['status']=='REJECTED'for x in neg['controls'])
src=json.loads((O/'independent-source/source_transport.json').read_text());assert src['status']=='INDEPENDENT_ALL_NATURAL_RETAGGED_COMPOSED_SOURCE_AND_LITERAL_TABLE_TRANSPORT_PASS'
assert src['composition']['full_tree_rewrites_commute_exactly'] and src['tables']['composition_uses_different_retagged_physical_seed']
for v in src['sources'].values():assert v['leaf_occurrences']==4744 and v['unique_dag_nodes']==206 and v['unique_interior_dag_nodes']==183
receipt={'status':'FRESH_SOURCE141_DIRECT_LEAF_REPLAY_REVIEW_PASS','reviewer':'opening_encoder','role':'Independently read supplied leaf/import closure and source/engine contracts; authored and executed scratch copy/extraction/14-job adapter and this evidence reader. No supplied proof or algorithm authorship claimed.','findings':[],'execution':desc(E/'result.json'),'plan':desc(E/'plan.json'),'source_notes':desc(R/'notes.md'),'runtime_input_lineage':desc(R/'runtime-input-lineage.json'),'portable_adapter_review':desc(R/'portable-review.json'),'variants':summary,'jobs':14,'total_generic_cases':sum(x['generic_cases']for x in summary.values()),'negative_controls_rejected':10,'bindings':bindings+[desc(O/'independent-runtime.json'),desc(O/'negative-controls.json'),desc(O/'independent-source/source_transport.json')],'scope':plan['scope'],'limitations':['Three219-state alternatives, no <=218 result.','No Lean/Rocq compilation or exact-table kernel endpoint.','No delivered wrapper, manifest/checksum suite, inherited calibration or ancestor runtime suite invoked.','Source equivalence is all-natural from source entry; the physical checker independently covers every generic guard without applying that reachability invariant.','Independent runtime audit checks stored fresh complete evidence and block identities, not an independent regeneration of every symbolic derivation.'],'own_helpers':[desc(R/f)for f in ('prepare.py','run.py','finalize_review.py')]}
(R/'review.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':receipt['status'],'review':desc(R/'review.json'),'variants':summary},indent=2))
