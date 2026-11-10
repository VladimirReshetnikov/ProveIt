#!/usr/bin/env python3
"""Audit sign24 exact-degree client and two observed audited providers, no Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign24-exact-degree-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign24-exact-degree-20261109');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['outer_session_id']==88484 and o['outer_exit_code']==0
sp=attempt/'state.json';assert sha(sp)==sha(out/'state.json');s=json.loads(sp.read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(packet/'run.py')=='4fb61ec5a61a1285c74b4e540c1d05cd4fa7625bfd60103be6939227b44113a3'
r,=s['rows'];name='Sign24ExactDegree';e,=json.loads((packet/'source-manifest.json').read_text())['rows'];src=packet/'src/DiophantineConsistency'/(name+'.lean')
assert r['module']==name and r['source_sha256']==e['source_sha256']==sha(src)==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
assert '(Sign24AbstractExpression.expression p).toPolynomial.totalDegree = 8' in src.read_text() and 'Sign24CurrentExpression.expression.toPolynomial.totalDegree = 8' in src.read_text()
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='80bc1b511aad339b19685c9e7faf906094d376a3ddeff8a4bc481b8b72ca658b'
for phase in ('deps','compile'):
 stage=r[phase];assert stage['exit']==0 and stage['stop_reason'] is None and not stage['monitor_errors'] and not stage['observed_descendant_pids'];assert stage['rss_limit_bytes']==4*1024**3 and stage['host_floor_bytes']==10*1024**3 and stage['timeout_seconds']==120
 log=name+'-'+phase+'.txt';assert sha(attempt/log)==sha(out/log)==stage['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'Sign24DegreeCompose':'8281e8be9dfe19dd6efa4faa05b4603b132feabbca3f33180325c8034e75f533','Sign24DegreeLower':'b6a39e3ccd7d089ee59b3b59c182235486a9cac86f502cdc5d07b6055672cc66'}
for mod in e['imports']:
 dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
log=' '.join((attempt/(name+'-compile.txt')).read_text().split());assert all(x not in log for x in ('warning:','error:','sorryAx'))
for t in ('abstract_exact','current_exact'):assert "'DiophantineConsistency.Sign24ExactDegree."+t+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for p,v in s['overlay_links'].items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
for review in ('nine-sharing-sign24-degree-structured-retry02-terminal-independent','nine-sharing-sign24-full-coeff-retry02-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'upper-survey.py')],check=True,capture_output=True,text=True,timeout=120);assert json.loads(u.stdout)['overlay_overlap']==1398
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','author_session':88484,'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'state_sha256':sha(sp),'scope':'abstract/current sign24 Lean expression polynomial totalDegree=8; no external binding'},sort_keys=True,indent=2))
