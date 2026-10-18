from pathlib import Path
import json,hashlib,sys
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=Path(sys.argv[1]);d=json.loads(p.read_text());assert d['status']=='PASS_SELECTED_UNITS' and not d['prepare_only'] and d['failed_unit'] is None
seen={};checks=0;probes=callers=0;times=[];records=[]
for row in d['completed_units']:
 ref=row['record'];assert H(ref['path'])==ref['sha256'];v=json.loads(Path(ref['path']).read_text());assert v['status']=='PASS' and not v['prepare_only']
 assert v['before']==v['after'] and v['all_input_provider_postchecks'] and v['source_object_recorded_before_audit'] and v['all_fresh_objects_unchanged_after_audit']
 for f,h in v['before'].items():
  if f not in seen:seen[f]=H(f)
  assert seen[f]==h,f
  checks+=1
 for k in ['source','audit']:
  assert H(v[k]['path'])==H(v[k]['snapshot'])==v[k]['sha256']
 assert len(v['commands'])==2
 for c in v['commands']:
  assert c['exit_code']==0 and not c['timed_out'] and not c['interrupted']
  assert Path(c['log']).read_text()==c['output']
  assert '-j1' in c['command'] and '-M4096' in c['command']
  assert not any(x in c['output'] for x in ['sorryAx',"declaration uses 'sorry'",'warning:'])
 assert sum(c['seconds'] for c in v['commands'])<=120
 fresh=v['fresh_modules'][0];first=v['fresh_first_provider_before_audit'];capture=v['source_pass_object']
 assert H(fresh['path'])==fresh['sha256']==first['sha256']==capture['sha256']
 assert first['actual_first']==fresh['path']==capture['path'] and capture['source_command_index']==0
 for x in v['actual_first_providers']:
  assert Path(x['actual_first']).resolve()==Path(x['resolved']).resolve() and H(x['actual_first'])==x['sha256']
 assert v['warnings']=={'source':0,'audit':0} and v['only_standard_axioms']
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in v['actual_axiom_sets'])
 assert v['named_axiom_probes']==v['expected_named_axiom_probes']==len(v['actual_axiom_sets']) and v['callers']==v['expected_callers']
 probes+=v['named_axiom_probes'];callers+=v['callers'];times.append(sum(c['seconds'] for c in v['commands']));records.append(ref)
out={'status':'CLEAN_SELECTED_ROUTING245_BATCH_ROOT_REVIEW','batch':{'path':str(p),'sha256':H(p)},'unit_indices':[x['unit_index'] for x in d['completed_units']],'records':records,'input_hash_references_checked':checks,'unique_input_paths_checked':len(seen),'named_axiom_probes':probes,'callers':callers,'max_shared_seconds':max(times),'total_shared_seconds':sum(times),'findings':[],'scope':'Exact selected actual units only. Complete routing coverage remains unclaimed.'}
q=p.parent/'root-review.json';q.write_text(json.dumps(out,indent=2)+'\n');print(q,H(q),len(records),'units',probes,'probes',callers,'callers')
