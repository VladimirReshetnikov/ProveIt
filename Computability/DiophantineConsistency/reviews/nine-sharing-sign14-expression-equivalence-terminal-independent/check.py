#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign14-expression-equivalence-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign14-expression-equivalence-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==35001 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='a77edbf15ca63f1c555477a8247a229aa85bab7ceffb356bb46fa6b22c14053f';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign14ExpressionEquivalence';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:')==1 and 'zero_exists_iff' in log and 'exists_cons_iff' in log and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==2 and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='bbfc84952d5c2722a7c9ab69665c42b0e293d8df313961d32df44e76a8b9be21'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign14CurrentExpressionEval','c1c844a91a67788261eade557da23a87c2f5c8238c7d5d54306683f82551f21d'),('Sign15CurrentExpressionEval','36d2a7bf260e0f67356e11cffcc19159ac0dda031af8930ba556dffe3d807877'),('Sign14CurrentSeedIff','4a57b93cb248389511ac6740f7110c9a449a2faea0dcfd7276527978717d1ef7')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':35001,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'current symbolic Fin14/Fin15 model zero-existence iff; no concrete bridge or endpoint'},indent=2,sort_keys=True))
