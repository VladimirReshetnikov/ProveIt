#!/usr/bin/env python3
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/current14-carrier65-diagonal-p-check';a=p/'attempt01';out=Path('/tmp/current14-carrier65-diagonal-p-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==42593 and o['outer_exit_code']==0 and sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-value-congr-diagnostic-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Current14Carrier65DiagonalP';assert r['module']==n and e['module']=='DiophantineConsistency.'+n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']
assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256'] and 'Init' in r['dependencies']
for mod in e['imports']:
 d=r['dependencies'][mod];assert Path(d['path']).is_file() and str(Path(d['path']).resolve())==d['realpath'] and sha(Path(d['path']))==d['sha256']
 if mod.endswith('DiagonalRank'):
  prior=json.loads((root/'research/current14-carrier65-diagonal-rank-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][1]['object_sha256']
 if mod.endswith('DiagonalCoreBinding'):
  prior=json.loads((root/'research/current14-carrier65-diagonal-core-binding-retry-check/attempt01/state.json').read_text());assert d['sha256']==prior['rows'][1]['object_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert all(z in log for z in ('k_degree','ell_degree','tau_degree','P_degree')) and log.count('[propext, Classical.choice, Quot.sound]')==4 and log.count('warning:')==0 and not any(z in log for z in ('error:','sorryAx'))
a1=json.loads((root/'research/current14-carrier65-diagonal-rank-check/attempt01/state.json').read_text());b=json.loads((root/'research/current14-carrier65-diagonal-core-binding-retry-check/attempt01/state.json').read_text())
def relmap(st,base):return {str(Path(k).relative_to(base/'lib')):v for k,v in st['overlay_links'].items()}
aa=relmap(a1,Path('/tmp/current14-carrier65-diagonal-rank-20261110'));bb=relmap(b,Path('/tmp/current14-carrier65-diagonal-core-binding-retry-20261110'));ov=set(aa)&set(bb);diff=[x for x in ov if aa[x]!=bb[x]];assert len(ov)==s['provider_overlap_count']==1267 and diff==['DiophantineConsistency/Current14Carrier65QFields.olean'] and sha(Path(aa[diff[0]]))==sha(Path(bb[diff[0]]))=='ffc15e09467d94f0f1c8752c38fbb06579d16b30863fb8954ef0950b5a568f0b';key=str(out/'lib'/diff[0]);assert s['overlay_links'][key]==aa[diff[0]] and str(Path(key).resolve())==aa[diff[0]]
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':42593,'scope':'actual axis k/ell/tau/P exact degrees 1/11/7/22 under p0 nonzero; whole expression separate'},indent=2))
