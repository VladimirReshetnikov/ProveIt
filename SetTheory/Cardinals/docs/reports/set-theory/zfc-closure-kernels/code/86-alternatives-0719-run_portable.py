#!/usr/bin/env python3
"""Run selected native components/audits in a fresh scratch copy of the package."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,shutil,subprocess,sys,time,shlex
if not __debug__:raise SystemExit('Assertions must be enabled; do not use -O')
ROOT=Path(__file__).resolve().parent
GROUPS={
 'copy':['native_copier/marked_unary_copy.py','native_copier/biased_reference_copy.py','native_copier/biased_reference_copy19.py','native_copier/check_variable_anchor.py','verification/audit_marked_unary_copy.py','verification/audit_biased_reference_copy.py','verification/audit_biased_reference_copy19.py'],
 'writer':['native_copier/anchor_mode_writer.py','verification/audit_anchor_mode_writer.py'],
 'comparators':['arithmetic_core/compare_biased_counter.py','arithmetic_core/compare_biased_counter27.py','arithmetic_core/biased_reference_copy18.py','arithmetic_core/fold_comparator_entries.py','verification/audit_comparators_and_copy18.py'],
 'oracle':['verification/audit_pattern_oracle.py','architectures/oracle_search.py'],
 'paths':['architectures/reverse_path_copy.py','architectures/retained_template_query.py','verification/audit_reverse_path_copy.py','verification/audit_retained_template_query.py'],
 'edges':['verification/audit_locator_pipeline.py','verification/audit_tag_native_edge.py','verification/audit_encoded_native_edge.py'],
 'logic':['logical_routes/fixed_binder_semantics.py','logical_routes/double_b6_modal_check.py','logical_routes/canonical_arena.py','logical_routes/square_pair_conjugacy.py','logical_routes/forward_saturation.py','verification/audit_saturation_and_canonical.py'],
 'packing':['verification/audit_packed_libraries.py','machine_encoding/component_packing/rebuild_certificate.py research_sub246/machine_encoding/component_packing/final_with_compare','machine_encoding/component_packing/rebuild_certificate.py research_sub246/machine_encoding/component_packing/final_without_compare','machine_encoding/component_packing/test_library.py research_sub246/machine_encoding/component_packing/final_with_compare','machine_encoding/component_packing/test_library.py research_sub246/machine_encoding/component_packing/final_without_compare','machine_encoding/component_packing/emit_native_quotient.py']}
p=argparse.ArgumentParser();p.add_argument('--only',default=','.join(GROUPS));p.add_argument('--list',action='store_true');a=p.parse_args()
if a.list:
 print(json.dumps(GROUPS,indent=2));raise SystemExit(0)
selected=a.only.split(',');unknown=set(selected)-set(GROUPS)
if unknown:raise SystemExit('Unknown groups: '+','.join(unknown))
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ');work=ROOT/'portable-runs'/stamp;tree=work/'research_sub246';work.mkdir(parents=True)
shutil.copytree(ROOT/'research_sub246',tree,ignore=shutil.ignore_patterns('__pycache__'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tables={str(p.relative_to(tree)):sha(p) for p in tree.rglob('*.tm')}
records=[];env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
for group in selected:
 for rel in GROUPS[group]:
  parts=shlex.split(rel);path=tree/parts[0]
  if not path.is_file():raise SystemExit('Missing selected script '+rel)
  cmd=[sys.executable,'-B',str(path),*parts[1:]];started=time.monotonic();proc=subprocess.run(cmd,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log=work/(str(len(records)+1).zfill(2)+'-'+Path(parts[0]).stem+'.log');log.write_text(proc.stdout)
  item={'group':group,'script':rel,'command':[sys.executable,'-B','research_sub246/'+parts[0],*parts[1:]],'returncode':proc.returncode,'seconds':round(time.monotonic()-started,6),'log':log.name};records.append(item)
  print(group,rel,proc.returncode,item['seconds'],flush=True)
  (work/'run-results.json').write_text(json.dumps({'status':'RUNNING' if proc.returncode==0 else 'FAILED','commands':records},indent=2)+'\n')
  if proc.returncode:print(proc.stdout[-5000:]);raise SystemExit(proc.returncode)
changed=[rel for rel,h in tables.items() if not(tree/rel).exists() or sha(tree/rel)!=h]
result={'status':'PASS' if not changed else 'TABLE_BYTES_CHANGED','scope':'Portable component/regression replay only; no full-machine or proof-assistant claim','python':sys.version,'groups':selected,'commands':records,'preexisting_tables_checked':len(tables),'changed_tables':changed}
(work/'run-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='commands'},indent=2));print('Results:',work)
raise SystemExit(bool(changed))
