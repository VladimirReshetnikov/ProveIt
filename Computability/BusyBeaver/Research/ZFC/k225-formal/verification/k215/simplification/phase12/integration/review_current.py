from pathlib import Path
import json,hashlib
R=Path.cwd();P=Path('/tmp/k215-phase12-import-proposal');B=Path('/tmp/k215-phase12-import-check')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
a=read(P/'adoption.json');by_source={r['source']:r for r in a['files']};historical={str(R/r['target']):r for r in a['files'] if r['target'].endswith('.py')};assert len(historical)==1
for row in a['files']:assert sha(R/row['target'])==row['sha256']==sha(row['source'])
all_sources={};runs=[]
for label,expected in [('primary',184),('compatibility',69)]:
 p=B/(label+'-run1');inv=read(p/'inventory.json');done=read(p/'completed.json');before=read(p/'before.json');assert len(done)==expected;history=[]
 for path,pin in before['inputs'].items():
  if path in historical:
   old=historical[path];assert old['before_sha256']==pin==sha(old['archived_before']);history.append({'canonical':path,'before_sha256':pin,'archived_before':old['archived_before'],'current_sha256':old['sha256']})
  else:assert sha(path)==pin,path
 assert len(history)==1
 for path in before['absent_inputs']:assert not Path(path).exists() and not Path(path).is_symlink()
 for row in inv['modules']:
  m=row['module'];s=by_source.get(row['source']);current=R/s['target'] if s else Path(row['source']);assert sha(current)==row['source_sha256'];rec=done[m]
  assert sha(p/'objects'/(m.replace('.','/')+'.olean'))==rec['object_sha256'];assert sha(rec['log'])==rec['log_sha256']
  assert rec['dependencies']=={d:done[d]['object_sha256'] for d in row['imports'] if d!='Init'}
  if m not in {'WFModelCompat12','ZFNativeCompat12'}:
   value={'current':str(current),'sha256':row['source_sha256']};assert m not in all_sources or all_sources[m]==value;all_sources[m]=value
 runs.append({'scope':label,'rows':expected,'intentionally_historical_canonical_inputs':history,'other_before_inputs_current_exact':True})
assert len(all_sources)==199
(P/'current-review.json').write_text(json.dumps({'status':'PASS_CURRENT_PHASE12_ADOPTION','adoption_sha256':sha(P/'adoption.json'),'canonical_writes':8,'project_sources':199,'runs':runs,'sources':all_sources,'scope':'Current canonical source binding plus live source/object/log/input rehash; one canonical producer before-input retained as exact historical bytes. No compiler or producer run.'},indent=2)+'\n');print('PASS current8writes/199projectsourcebindings;one explicit historical producer per run')
