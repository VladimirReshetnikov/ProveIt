#!/usr/bin/env python3
"""Inspect current-beta retry receipt and direct provider without Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign20-count-proof-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign20-count-proof-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==15193 and o['outer_exit_code']==0
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='2e0cd195ae7b491141a7cefa906dbbfce419a7075e439a27193bd6084fca74dd'
r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign20CountProof';assert r['module']==n and r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(n+'.olean'))=='28f3f2bdd30585230d8939f46e3059f7d65a61e56519de0a331760c569628ff6'
for phase in ('deps','compile'):
 x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
d=r['dependencies']['DiophantineConsistency.Sign20CountShapes'];assert d['sha256']=='be34a38cbdb446b765c125ef96934301d54f4f81f1cc0ac9a6dee4a3f720a6df' and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert log.count('warning:')==4 and not any(x in log for x in ('error:','sorryAx'))
for th in ('n0_count','dc2_count'):assert "'DiophantineConsistency.Sign20CountProof."+th+"' depends on axioms: [propext]" in log
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign20-count-shapes-terminal-independent/check.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':15193,'outer_exit':0,'guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'two symbolic finite counts = 1; passed shape provider has failed-grandparent ancestry, no full lower theorem'},indent=2,sort_keys=True))
