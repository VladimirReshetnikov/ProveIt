#!/usr/bin/env python3
"""Audit failure of sign22 leading-row first stage, without Lean replay."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign22-leading-rows-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign22-leading-rows-20261109')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['outer_session']==57783 and o['outer_exit_code']==1
statepath=attempt/'state.json';assert sha(statepath)==sha(out/'state.json');s=json.loads(statepath.read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign22LeadingRows')" and len(s['rows'])==1
assert s['runner_sha256']==sha(packet/'run.py')=='6fdebc810bfb7ac50aa577f8f29c064885c5e4f8086bf2aca187393e91ebff98'
r,=s['rows'];name='Sign22LeadingRows';e=json.loads((packet/'source-manifest.json').read_text())['rows'][0]
assert r['module']==name and r['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',1)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=name+'-'+phase+'.txt';assert sha(attempt/log)==sha(out/log)==x['log_sha256']
dep=r['dependencies']['DiophantineConsistency.Sign22CurrentExpressionDef'];assert dep['sha256']=='e6af82e204a6e942979ad67fd20fcdf27138f5b17143eeb3b65553d20bb2cb14' and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
log=' '.join((attempt/(name+'-compile.txt')).read_text().split());assert 'error: unsolved goals' in log and "Sign22LeadingRows.n0_row' depends on axioms: [propext]" in log and "Sign22LeadingRows.n0_axis' depends on axioms: [propext, sorryAx, Quot.sound]" in log
assert not (out/'lib/DiophantineConsistency/Sign22LeadingRows.olean').exists() and not (out/'lib/DiophantineConsistency/Sign22DiagonalDegree.olean').exists()
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign22-concrete-polynomial-bridge-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':57783,'outer_exit':1,'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'state_sha256':sha(statepath),'scope':'failed first module, no object or diagonal stage; n0 row report and incorrect axis source'},sort_keys=True,indent=2))
