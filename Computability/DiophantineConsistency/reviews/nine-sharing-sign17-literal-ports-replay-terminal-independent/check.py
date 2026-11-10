#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-literal-ports-replay-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-literal-ports-replay-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert json.loads((a/'outer-result.json').read_text())=={'outer_session':32017,'outer_exit_code':0}
assert sha(a/'state.json')==sha(out/'state.json')=='91937a98ca66bd60357bee5b54cc8d9d9ab6c41fc7217f377ff95c8e2215606f'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['manifest_sha256']==sha(p/'source-manifest.json')
e=json.loads((p/'source-manifest.json').read_text())['rows'][0];r=s['rows'][0];n='Sign17LiteralPorts';assert r['module']==n and e['module']=='DiophantineConsistency.'+n
assert sha(root.parents[1]/e['source'])==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all('Current14LiteralPortsMF.'+x in log for x in ('beta_eq','mu_eq','omega_eq','K_eq','all_ports')) and log.count('[propext, Classical.choice, Quot.sound]')==5 and all(x not in log for x in ('error:','warning:','sorryAx'))
prior=json.loads((root/'research/nine-sharing-sign17-lines-kernel-check/attempt01/state.json').read_text());assert prior['status']=='PASS';base=Path('/tmp/nine-sharing-sign17-lines-kernel-20261110/lib/DiophantineConsistency');pins={'MFCurrentKernel2011':'33d748748d1fbbc4ecbb3ce932536375d2bdcb45ada96602b5298e3dc89b948f','ArithmeticMaskData':'fce25c7165a78f7825542d699689135a3e65e539b01325b5dcfbe0d1fbcc639b','MFPaper1982Digits':'ad962dcb90cd33a206fb3ebe9780804e5170a5651659a1dcc7a96c4481bd83b5'}
for name,pin in pins.items():
 d=r['dependencies']['DiophantineConsistency.'+name];z=base/(name+'.olean');assert str(z) in prior['overlay_links'] and str(z.resolve())==prior['overlay_links'][str(z)]==d['realpath'] and sha(z)==d['sha256']==pin and r['direct_guard'][d['path']]=={'realpath':d['realpath'],'sha256':d['sha256']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':32017,'scope':'four structured port identities replayed in numeral-K context; no PDF/file or full ancestry theorem'},indent=2))
