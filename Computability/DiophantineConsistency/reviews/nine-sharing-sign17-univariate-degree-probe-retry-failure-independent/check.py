#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign17-univariate-degree-probe-retry-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign17-univariate-degree-probe-retry-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==61290 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign17UnivariateDegreeProbe')" and s['runner_sha256']==sha(packet/'run.py')=='988c1ab436b1ae25dad18c724022e3d7edc7a7c2b22ff5590bc1ee33f3184387';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign17UnivariateDegreeProbe';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',1)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/(phase+'.txt'))==sha(out/log)==r['log_sha256']
log=(a/'compile.txt').read_text();assert log.count('error:')==1 and 'sorryAx' in log and log.count('warning:')==0 and '⊢ 0 = 0' in log and 'mapped_degree_le' in log and 'product_degree' in log and 'dominant_add' in log and not (out/'lib/DiophantineConsistency'/(name+'.olean')).exists() and 'object_sha256' not in row
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
dep=row['dependencies']['DiophantineConsistency.Sign17DegreeCompose'];assert dep['sha256']=='4af0d401fc347ac92ce4d038699b9b5b0db6dd020c879a5821040aef9dca7d82' and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
dep2=row['dependencies']['Mathlib.Algebra.MvPolynomial.Equiv'];assert dep2['sha256']=='fbc9536ad69c177c0029f0bec09046ca307c22d71432d354e9a578eb4530147f' and row['direct_guard'][dep2['path']]=={'sha256':dep2['sha256'],'realpath':dep2['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':61290,'outer_exit':1,'compile_exit':1,'errors':1,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'Equiv import succeeded; mapped-degree rewrite side goal remains and sorryAx; no module object or postflight'},indent=2,sort_keys=True))
