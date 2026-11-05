#!/usr/bin/env python3
"""Audit successful five-norm client and its four direct producer rows."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
q=R/'nine-sharing-norm38-five-norms-check-v2';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-five-norms-check-v2-20261105')
assert sha(a/'state.json')==sha(out/'state.json')=='a16e6c80cd1f713b0ec2e863b800847a80265e86643f757ae146c1f1c9656140'
assert sha(q/'src/DiophantineConsistency/Norm38FiveNorms.lean')==sha(R/'nine-sharing-norm38-five-norms-draft/Norm38FiveNorms.lean')=='659df3272bc175cad9a3a461d01c52cc3d10a6375f16c351a0e6093a28f383d2'
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Norm38FiveNorms' and r['source_sha256']==sha(q/'src/DiophantineConsistency/Norm38FiveNorms.lean')==sha(out/'src/DiophantineConsistency/Norm38FiveNorms.lean')
assert r['object_sha256']=='ea31b12a3933596dc35448c05a91b17dcb3c915ff8ed13c603caf161d136051d'==sha(out/'lib/DiophantineConsistency/Norm38FiveNorms.olean')
for typ in ('deps','compile'):
 v=r[typ];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(a/('Norm38FiveNorms-'+typ+'.txt'))==sha(out/('Norm38FiveNorms-'+typ+'.txt'))==v['log_sha256']
assert (a/'Norm38FiveNorms-compile.txt').read_bytes()==b''
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==76122 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
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
guards(r['direct_guard'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
each=R/'nine-sharing-norm38-each-slot-retry01/attempt01/state.json';batch=R/'nine-sharing-norm38-slots-batched-retry01/attempt01/state.json'
assert sha(each)=='8bd674fad57bcb8dfe1d4d98dc8ba5716be15bc7d9c029f39198e53557bdfa70' and sha(batch)=='5e2b9bc0792962fe16bb2015ee035a06c4e806acfeb85eafc2d942029eef8edc'
es=json.loads(each.read_text());bs=json.loads(batch.read_text());assert es['status']=='PASS' and bs['status']=='FAILED' and bs['rows'][-1]['module']=='Norm38SlotsAssembly' and bs['rows'][-1]['compile']['stop_reason']=='timeout'
producers={'Norm38EachSlot':(es['rows'][0],Path('/tmp/nine-sharing-norm38-each-slot-retry01-20261105'))}
producers.update({x['module']:(x,Path('/tmp/nine-sharing-norm38-slots-batched-retry01-20261105')) for x in bs['rows'] if x['module'] in ('Norm38Slots03','Norm38Slots05','Norm38Slots09')});assert len(producers)==4
for n,(row,base) in producers.items():
 assert row['deps']['exit']==row['compile']['exit']==0 and row['deps']['stop_reason'] is row['compile']['stop_reason'] is None
 check(base/'src/DiophantineConsistency'/(n+'.lean'),row['source_sha256']);check(base/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256'])
 for typ in ('deps','compile'):check(base/(n+'-'+typ+'.txt'),row[typ]['log_sha256'])
 guards(row['direct_guard']);dep=r['dependencies']['DiophantineConsistency.'+n];assert dep['sha256']==row['object_sha256'];check(dep['path'],dep['sha256'],dep['realpath']);assert Path(dep['path']).is_symlink() and Path(dep['path']).resolve()==(base/'lib/DiophantineConsistency'/(n+'.olean')).resolve()
print(json.dumps({'status':'PASS_FIVE_NORM_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'outer_author_record_sha256':sha(a/'outer-terminal-author-record.json'),'author_recorded_outer_session':76122,'author_recorded_outer_exit':0,'candidate_guard_slots':len(r['direct_guard']),'producer_guard_slots':sum(len(x[0]['direct_guard']) for x in producers.values()),'overlay_links':len(s['overlay_links']),'direct_producers':{n:x[0]['object_sha256'] for n,x in producers.items()},'scope':'Retained state/logs and direct producer point checks; no Lean replay or independent historical outer-session observation.'},indent=2,sort_keys=True))
