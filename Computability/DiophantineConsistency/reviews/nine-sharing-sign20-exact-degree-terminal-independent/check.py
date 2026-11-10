#!/usr/bin/env python3
"""Audit sign21 exact-degree client and two observed audited providers, no Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign20-exact-degree-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign20-exact-degree-20261109');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['outer_session']==65100 and o['outer_exit_code']==0
sp=attempt/'state.json';assert sha(sp)==sha(out/'state.json');s=json.loads(sp.read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(packet/'run.py')=='0d8762a85fe80ae47f9410903a68095b605f67b1790707f3ebefa3cb721b5ce1'
r,=s['rows'];name='Sign20ExactDegree';e,=json.loads((packet/'source-manifest.json').read_text())['rows'];src=packet/'src/DiophantineConsistency'/(name+'.lean')
assert r['module']==name and r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
assert '(Sign20AbstractExpression.expression p).toPolynomial.totalDegree = 20' in src.read_text() and 'Sign20CurrentExpression.expression.toPolynomial.totalDegree = 20' in src.read_text()
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='196fcc6fbece852281904080c7b9e1f6ff77514532cf8421bd6b9c3c54c3bbf8'
for phase in ('deps','compile'):
 stage=r[phase];assert stage['exit']==0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids'];assert stage['rss_limit_bytes']==4*1024**3 and stage['host_floor_bytes']==10*1024**3 and stage['timeout_seconds']==120
 log=name+'-'+phase+'.txt';assert sha(attempt/log)==sha(out/log)==stage['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'Sign20CurrentBeta':'e4c29037e8e76ee4bae08c7d9b85286af83cde7862174d84b4bce0297477ac36','Sign20DegreeCompose':'392c5123a36030f5f44a7b013463bd33cdbc185dd6140a9e40fec6d212f5c615','Sign20DegreeLower':'cd2691f4980c164d1816e0459d8ab9ff61cc8bbbf1ff1ad3d476848dc5ff1e0d'}
for mod in e['imports']:
 dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
log=' '.join((attempt/(name+'-compile.txt')).read_text().split());assert all(x not in log for x in ('warning:','error:','sorryAx'))
for t in ('abstract_exact','current_exact'):assert "'DiophantineConsistency.Sign20ExactDegree."+t+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
for review in ('nine-sharing-sign20-degree-upper-terminal-independent','nine-sharing-sign20-count-lower-terminal-independent','nine-sharing-sign20-current-beta-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'upper-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(u.stdout)['overlay_overlap']==1455
b=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'beta-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(b.stdout)['overlay_overlap']==1455
assert '(hp : p 0 ≠ 0)' in src.read_text() and 'Sign20CurrentBeta.nonzero' in src.read_text()
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':65100,'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'state_sha256':sha(sp),'scope':'conditional abstract/current sign20 Lean expression polynomial totalDegree=20; no external binding'},sort_keys=True,indent=2))
