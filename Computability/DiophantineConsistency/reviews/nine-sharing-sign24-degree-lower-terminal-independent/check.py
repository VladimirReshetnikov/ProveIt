#!/usr/bin/env python3
"""Audit failure of sign24 lower-bound first stage, without Lean replay."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign24-degree-lower-check';attempt=packet/'attempt01';out=Path('/tmp/nine-sharing-sign24-degree-lower-20261109')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
o=json.loads((attempt/'outer-result.json').read_text());assert o['outer_session_id']==59504 and o['outer_exit_code']==1
statepath=attempt/'state.json';assert sha(statepath)==sha(out/'state.json');s=json.loads(statepath.read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign24LeadingN0')" and len(s['rows'])==1
assert s['runner_sha256']==sha(packet/'run.py')=='3a40eb95f5bf51876af855ac6a1529284eb16234e27d98566ce099ae980de476'
r,=s['rows'];name='Sign24LeadingN0';e=json.loads((packet/'source-manifest.json').read_text())['rows'][0]
assert r['module']==name and r['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',1)]:
 x=r[phase];assert x['exit']==code and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=name+'-'+phase+'.txt';assert sha(attempt/log)==sha(out/log)==x['log_sha256']
dep=r['dependencies']['DiophantineConsistency.Sign24CurrentExpressionDef'];assert dep['sha256']=='c4461171b21c8317ec96470f066049d5d1457fcd934e71facadd2dd099e73f9f' and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
log=' '.join((attempt/(name+'-compile.txt')).read_text().split());assert 'error: unsolved goals' in log and "Sign24LeadingN0.n0_row' depends on axioms: [propext]" in log and "Sign24LeadingN0.n0_axis' depends on axioms: [propext, sorryAx]" in log
assert not (out/'lib/DiophantineConsistency/Sign24LeadingN0.olean').exists() and not (out/'lib/DiophantineConsistency/Sign24DiagonalDegree.olean').exists()
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
subprocess.run([sys.executable,'-I','-S','-B',str(packet/'expression-survey.py')],check=True,capture_output=True,timeout=120)
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign24-concrete-bridge-memory-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':59504,'outer_exit':1,'guards':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'state_sha256':sha(statepath),'scope':'failed first module, no object or diagonal stage; n0 row report alone'},sort_keys=True,indent=2))
