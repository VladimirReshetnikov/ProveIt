#!/usr/bin/env python3
"""Audit sign21 exact-degree client and two observed audited providers, no Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign21-exact-degree-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign21-exact-degree-20261109');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['outer_session']==3492 and o['outer_exit_code']==0
sp=attempt/'state.json';assert sha(sp)==sha(out/'state.json');s=json.loads(sp.read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(packet/'run.py')=='8db1078a667801eaf29867d4c957cc0611d9a44866b416d6c3291526e6107a36'
r,=s['rows'];name='Sign21ExactDegree';e,=json.loads((packet/'source-manifest.json').read_text())['rows'];src=packet/'src/DiophantineConsistency'/(name+'.lean')
assert r['module']==name and r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
assert '(Sign21AbstractExpression.expression p).toPolynomial.totalDegree = 14' in src.read_text() and 'Sign21CurrentExpression.expression.toPolynomial.totalDegree = 14' in src.read_text()
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='23ca9ee5f73e8db28f3ba03f078582ab0bf76b48f2a79df318261c9b4b6476e5'
for phase in ('deps','compile'):
 stage=r[phase];assert stage['exit']==0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids'];assert stage['rss_limit_bytes']==4*1024**3 and stage['host_floor_bytes']==10*1024**3 and stage['timeout_seconds']==120
 log=name+'-'+phase+'.txt';assert sha(attempt/log)==sha(out/log)==stage['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'Sign21DegreeCompose':'43a215883b539af6c6f8f5569b04b0dfa118cac59e1d91ff0696daf6f55088ef','Sign21DegreeLower':'21ac7528a9a48fdad4d9f9d5362907f51b7fbad6530e0bb1c027f0f0b663fedb'}
for mod in e['imports']:
 dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
log=' '.join((attempt/(name+'-compile.txt')).read_text().split());assert all(x not in log for x in ('warning:','error:','sorryAx'))
for t in ('abstract_exact','current_exact'):assert "'DiophantineConsistency.Sign21ExactDegree."+t+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
for review in ('nine-sharing-sign21-degree-upper-terminal-independent','nine-sharing-sign21-full-coeff-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'upper-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(u.stdout)['overlay_overlap']==1440
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':3492,'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'state_sha256':sha(sp),'scope':'abstract/current sign21 Lean expression polynomial totalDegree=14; no external binding'},sort_keys=True,indent=2))
