#!/usr/bin/env python3
"""Audit sign22 exact-degree client and two observed audited providers, no Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign22-exact-degree-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign22-exact-degree-20261109');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['outer_session']==29568 and o['outer_exit_code']==0
sp=attempt/'state.json';assert sha(sp)==sha(out/'state.json');s=json.loads(sp.read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(packet/'run.py')=='9d0c5fd25629b9ba2869dd0f4edd6e72c06118ddf7ff702b0e4a5d6c51fd03e2'
r,=s['rows'];name='Sign22ExactDegree';e,=json.loads((packet/'source-manifest.json').read_text())['rows'];src=packet/'src/DiophantineConsistency'/(name+'.lean')
assert r['module']==name and r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
assert '(Sign22AbstractExpression.expression p).toPolynomial.totalDegree = 12' in src.read_text() and 'Sign22CurrentExpression.expression.toPolynomial.totalDegree = 12' in src.read_text()
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='7cae933aed6489fe495d06e7d8b2c2c1141527ae54a8559fd8e09b97b5335aff'
for phase in ('deps','compile'):
 stage=r[phase];assert stage['exit']==0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids'];assert stage['rss_limit_bytes']==4*1024**3 and stage['host_floor_bytes']==10*1024**3 and stage['timeout_seconds']==120
 log=name+'-'+phase+'.txt';assert sha(attempt/log)==sha(out/log)==stage['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'Sign22DegreeCompose':'319b716cc1b9b5cfd00e8399b818d13ccea2445b9e934aab5d64a3e7f17c0d8b','Sign22DegreeLower':'4ecdb9007664f9c3f07662c214bf487a47074640c12f94f280dff89faf8fbc4b'}
for mod in e['imports']:
 dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
log=' '.join((attempt/(name+'-compile.txt')).read_text().split());assert all(x not in log for x in ('warning:','error:','sorryAx'))
for t in ('abstract_exact','current_exact'):assert "'DiophantineConsistency.Sign22ExactDegree."+t+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
for review in ('nine-sharing-sign22-degree-upper-terminal-independent','nine-sharing-sign22-full-coeff-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'upper-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(u.stdout)['overlay_overlap']==1426
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':29568,'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'state_sha256':sha(sp),'scope':'abstract/current sign22 Lean expression polynomial totalDegree=12; no external binding'},sort_keys=True,indent=2))
