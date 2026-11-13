#!/usr/bin/env python3
"""Audit successful sign17 staged degree bound without rerunning Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-degree-staged-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-degree-staged-retry-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==58319 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(p/'run.py')=='553d568f8c178f109b30146c746f255db52b051c5d636bbb1f6951360dad2312';names=[f'Sign17SharedDegree{i:02}' for i in range(1,7)]+['Sign17RowDegrees00','Sign17RowDegrees01','Sign17DegreeStructural','Sign17DegreeResiduals','Sign17DegreeCompose'];assert [r['module'] for r in s['rows']]==names;entries=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(entries)==11
pins={'Sign17SyntaxDegree':'92eec74fdf59018c09c412203a4c35ff412ed8d327e6c758c24deef87b872a19','Sign17SharedDegree00':'b7259469f06aa29666e3312140bac75f2f047b315f63227564b1d9d6a665e911'};guards=0
for row,e,name in zip(s['rows'],entries,names):
 src=p/'src/DiophantineConsistency'/(name+'.lean');assert row['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(name+'.lean'));obj=out/'lib/DiophantineConsistency'/(name+'.olean');assert row['object_sha256']==sha(obj);pins[name]=row['object_sha256']
 for phase in ('deps','compile'):
  x=row[phase];log=name+'-'+phase+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/log)==sha(out/log)==x['log_sha256']
 for path,v in row['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  dep=row['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
 log=(a/(name+'-compile.txt')).read_text();assert not any(t in log for t in ('error:','warning:','sorryAx'))
log=' '.join((a/'Sign17DegreeCompose-compile.txt').read_text().split())
for th in ('seed_degree_le','expression_degree_le','expression_polynomial_degree_le','current_polynomial_degree_le'):assert 'Sign17SyntaxDegree.'+th+"' depends on axioms:" in log
assert log.count('[propext, Classical.choice, Quot.sound]')==2
c=(p/'src/DiophantineConsistency/Sign17DegreeCompose.lean').read_text();assert '(Sign17AbstractExpression.expression p).toPolynomial.totalDegree ≤ 96' in c and 'Sign17CurrentExpression.expression.toPolynomial.totalDegree ≤ 96' in c
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
for check in (root/'reviews/nine-sharing-sign17-degree-shared-probe-retry02-terminal-independent/check.py',p/'framework-survey.py'):
 subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':58319,'outer_exit':0,'stages':11,'guard_entries':guards,'overlay_links':len(s['overlay_links']),'scope':'arbitrary-port abstract and current symbolic Fin17 totalDegree ≤ 96; no lower/exact degree or external binding'},indent=2,sort_keys=True))
