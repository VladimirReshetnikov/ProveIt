#!/usr/bin/env python3
"""Audit failed generic sign16 absdiff attempt; do not invoke Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];packet=root/'research/nine-sharing-sign16-expression-equivalence-check';a=packet/'attempt01';out=Path('/tmp/nine-sharing-sign16-expression-equivalence-check-20261110');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==9305 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and 'failure' not in s and s['runner_sha256']==sha(packet/'run.py')=='db3ba88df710e0c60e7d9fb6d81a9dc09b55042667646380e18b264ad2a7bede';row,=s['rows'];e,=json.loads((packet/'source-manifest.json').read_text())['rows'];name='Sign16ExpressionEquivalence';assert row['module']==name and row['source_sha256']==e['source_sha256']==sha(packet/'src/DiophantineConsistency'/(name+'.lean'))==sha(out/'src/DiophantineConsistency'/(name+'.lean'))
for phase,code in [('deps',0),('compile',0)]:
 r=row[phase];log=name+'-'+phase+'.txt';assert r['exit']==code and r['stop_reason'] is None and not r['monitor_errors'] and not r['observed_descendant_pids'] and r['rss_limit_bytes']==4*1024**3 and r['host_floor_bytes']==10*1024**3 and r['timeout_seconds']==120 and sha(a/log)==sha(out/log)==r['log_sha256']==o['logs'][log]
log=(a/(name+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log and log.count('warning:')==1 and 'zero_exists_iff' in log and 'exists_cons_iff' in log and ' '.join(log.split()).count('[propext, Classical.choice, Quot.sound]')==2 and row['object_sha256']==sha(out/'lib/DiophantineConsistency'/(name+'.olean'))=='d02a419606be4cc2e47fdd1dbff9af070f6f6b7eaeba0d58ec7c87e14201e35f'
for path,v in row['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for mod,pin in [('Sign16CurrentExpressionEval', '92e05a57036ae2c319e54ee019a907abdfad4bab7db3af372596764b776439f1'), ('Sign17CurrentExpressionEval', '4ccb0e17b7f57d9516d4383dd53960f82a7c4d92c1d8f518484dfed8f9d13abc'), ('Sign16CurrentSeedIff', 'd82cc49e020fba4671781a0c6385513bfa5d37ff609136685ed74168526b6370')]:
 dep=row['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==pin and row['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':9305,'outer_exit':0,'compile_exit':0,'errors':0,'guard_entries':len(row['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'current symbolic Fin16/Fin17 model zero-existence iff; no concrete bridge or endpoint'},indent=2,sort_keys=True))
