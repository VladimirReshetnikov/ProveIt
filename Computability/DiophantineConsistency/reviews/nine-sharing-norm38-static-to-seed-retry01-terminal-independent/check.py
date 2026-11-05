#!/usr/bin/env python3
"""Read-only static-to-seed terminal and immediate producer audit."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-static-to-seed-retry01';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-static-to-seed-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='ae9f8310391bea63f5d591966b81284846bbf0f526c1da00c8a4225fb56c0b74';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['base_state_sha256']=='71326dc89477d47cca893654dca94000877096b87a28ffd1086649677aa52d71';r=s['rows'][0];assert r['module']=='Norm38StaticToSeed'
src=q/'src/DiophantineConsistency/Norm38StaticToSeed.lean';assert sha(src)==sha(out/'src/DiophantineConsistency/Norm38StaticToSeed.lean')==r['source_sha256']=='8bf928814dc96ba30c7ae8fc6c0edb0db967821c86d785cb51876406a10b7b25';obj=out/'lib/DiophantineConsistency/Norm38StaticToSeed.olean';assert sha(obj)==r['object_sha256']=='1e1cbb3ca4feb02070c15c0a70d65e2ae77ec6772cf170620cda45a8d8e00a84'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==86310 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
def guards(g):
 for path,v in g.items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
for typ in ('deps','compile'):
 z=r[typ];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];check(a/('Norm38StaticToSeed-'+typ+'.txt'),z['log_sha256']);check(out/('Norm38StaticToSeed-'+typ+'.txt'),z['log_sha256'])
assert (a/'Norm38StaticToSeed-compile.txt').read_text().count('warning:')==1
guards(r['direct_guard'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
ps=R/'nine-sharing-norm38-forward-prefix-check/attempt01/state.json';es=R/'nine-sharing-norm38-each-slot-retry01/attempt01/state.json';bs=R/'nine-sharing-norm38-slots-batched-retry01/attempt01/state.json'
assert sha(ps)=='71326dc89477d47cca893654dca94000877096b87a28ffd1086649677aa52d71' and sha(es)=='8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70' and sha(bs)=='5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc'
p=json.loads(ps.read_text());e=json.loads(es.read_text());b=json.loads(bs.read_text());assert p['status']==e['status']=='PASS' and b['status']=='FAILED' and b['rows'][-1]['module']=='Norm38SlotsAssembly' and b['rows'][-1]['compile']['stop_reason']=='timeout'
producers=[(p['rows'][0],Path('/tmp/nine-sharing-norm38-forward-prefix-check-20261105')),(e['rows'][0],Path('/tmp/nine-sharing-norm38-each-slot-retry01-20261105'))]+[(x,Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105')) for x in b['rows'] if x['module'] in {f'Norm38Slots{i:02d}' for i in range(10)}];assert len(producers)==12
for row,base in producers:
 n=row['module'];assert row['deps']['exit']==row['compile']['exit']==0 and row['deps']['stop_reason'] is row['compile']['stop_reason'] is None
 check(base/'src/DiophantineConsistency'/(n+'.lean'),row['source_sha256']);check(base/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256'])
 for typ in ('deps','compile'):check(base/(n+'-'+typ+'.txt'),row[typ]['log_sha256'])
 guards(row['direct_guard'])
 if n!='Norm38ForwardPrefix':
  dep=r['dependencies']['DiophantineConsistency.'+n];assert dep['sha256']==row['object_sha256'];check(dep['path'],dep['sha256'],dep['realpath']);assert Path(dep['path']).resolve()==(base/'lib/DiophantineConsistency'/(n+'.olean')).resolve()
prior=D/'reviews/nine-sharing-norm38-static-to-seed-retry01-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(prior/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(prior/'result.json').read_bytes()
print(json.dumps({'status':'PASS_STATIC_TO_SEED_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(obj),'author_recorded_outer_session':86310,'author_recorded_exit':0,'candidate_guard_slots':len(r['direct_guard']),'producer_rows':len(producers),'producer_guard_slots':sum(len(x[0]['direct_guard']) for x in producers),'overlay_links':len(s['overlay_links']),'scope':'Retained source/log/object and producer guard points; no Lean replay or independent historical outer exit.'},indent=2,sort_keys=True))
