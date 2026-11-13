#!/usr/bin/env python3
"""Inspect current-beta retry receipt and direct provider without Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-root-lift-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-root-lift-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==14000 and o['outer_exit_code']==0
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='655e36cde261635502429ad7b86b937ef52e675bf5a7732003791c459cd5777b'
r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17RootLift';assert r['module']==n and r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(n+'.olean'))=='a9e50bc6101443cfadb386692232bab6b19e69d573feefc873285e20aa4727b3'
for phase in ('deps','compile'):
 x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
d=r['dependencies']['DiophantineConsistency.Sign17OrderedGap'];assert d['sha256']=='157ba8307d5bcf118e642cd3ca592d706bfe36ff5cb818696c4dcaf939f95a09' and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert not any(x in log for x in ('warning:','error:','sorryAx'))
for th in ('root_positive','scale_positive','exists_signed_lift'):assert "'DiophantineConsistency.Sign17RootLift."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-signed-lift-lemmas-retry-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':14000,'outer_exit':0,'guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'root/scale positive and gap representative under beta>0 and retained norm; B,C arbitrary, no concrete bridge'},indent=2,sort_keys=True))
