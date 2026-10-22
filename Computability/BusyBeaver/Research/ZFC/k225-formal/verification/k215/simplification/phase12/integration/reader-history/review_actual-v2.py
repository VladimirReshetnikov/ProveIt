from pathlib import Path
import hashlib,json,re
BASE=Path('/tmp/k215-phase12-import-check'); OUT=Path('/tmp/k215-phase12-import-proposal')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
allowed={'propext','Classical.choice','Quot.sound'}
results=[];union=set()
for label,count,fresh,prior,secondary in [('primary',184,15,169,0),('compatibility',69,5,12,52)]:
 p=BASE/(label+'-run1');r=read(p/'result.json');inv=read(p/'inventory.json');done=read(p/'completed.json');before=read(p/'before.json')
 assert r['status']=='PASS' and sha(p/'inventory.json')==r['inventory_sha256'] and sha(p/'completed.json')==r['completed_sha256']
 assert set(done)=={x['module'] for x in inv['modules']} and len(done)==count
 assert len(r['fresh_modules'])==fresh and len(r['phase11_reused_modules'])==prior and len(r['secondary_reused_modules'])==secondary
 assert sha(BASE/'build.py')==r['runner_sha256']=='4242f1dab9adcf9a5f1b89ef87d5a65568e1ef302627fb89183e2a94dd99dcb5'
 for name,pin in before['inputs'].items():assert sha(name)==pin,name
 for name in before['absent_inputs']:assert not Path(name).exists() and not Path(name).is_symlink()
 fresh_warnings=0;inherited_warnings=0;reports=0
 for row in inv['modules']:
  m=row['module'];rec=done[m];assert rec['source_sha256']==row['source_sha256']==sha(row['source'])
  assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
  assert rec['dependencies']=={d:done[d]['object_sha256'] for d in row['imports'] if d!='Init'}
  assert sha(p/'objects'/(m.replace('.','/')+'.olean'))==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
  log=Path(rec['log']).read_text();assert not re.search(r'sorryAx|declaration uses .sorry.|error:|PANIC',log)
  parsed=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log)
  if 'reports' in rec:assert [list(x) for x in parsed]==[list(x) for x in rec['reports']]
  else:assert rec['origin']!='candidate_fresh'
  assert all({x.strip() for x in axioms.split(',') if x.strip()}<=allowed for _,axioms in parsed)
  if rec['origin']=='candidate_fresh':
   assert sha(rec['source'])==row['source_sha256'];fresh_warnings+=log.count('warning:')
  else:inherited_warnings+=log.count('warning:')
  reports+=len(parsed)
  if m not in {'WFModelCompat12','ZFNativeCompat12'}:union.add(m)
 for a in r['audits']:
  n=a['module'];assert a['status']=='PASS' and a['exit_code']==0 and not a['timed_out']
  assert a['dependencies']=={m:rec['object_sha256'] for m,rec in done.items()}
  assert sha(a['source'])==a['source_sha256'] and sha(a['log'])==a['log_sha256']
  assert sha(p/('audit-'+n)/(n+'.lean'))==a['source_sha256'] and sha(p/('audit-'+n)/(n+'.olean'))==a['object_sha256']
  log=Path(a['log']).read_text();assert not re.search('sorryAx|warning:|error:|PANIC',log)
  parsed=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",log)
  assert [list(x) for x in parsed]==[list(x) for x in a['named_reports']]
  assert all({x.strip() for x in axioms.split(',') if x.strip()}==allowed for _,axioms in parsed)
 assert len(r['audits'])==(2 if label=='primary' else 0)
 results.append({'scope':label,'modules':count,'fresh':fresh,'phase11':prior,'primary':secondary,'fresh_warning_occurrences':fresh_warnings,'reused_warning_occurrences':inherited_warnings,'module_reports':reports,'endpoint_clients':len(r['audits']),'before_inputs_rehashed':len(before['inputs']),'result_sha256':sha(p/'result.json')})
assert len(union)==199
record={'status':'PASS_INDEPENDENT_ROOT_PHASE12_ACTUALS','runs':results,'distinct_project_modules':len(union),'all_sources_objects_logs_dependencies_and_inputs_rehashed':True,'compiler_invocations':0,'scope':'Independent raw-record and live-object read only, before canonical adoption; no compiler or producer run.'}
(OUT/'root-actual-review.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
