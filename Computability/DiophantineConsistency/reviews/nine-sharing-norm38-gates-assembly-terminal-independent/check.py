#!/usr/bin/env python3
"""Read-only terminal and direct-producer review for the gate assembly."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-gates-assembly-retry';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-gates-assembly-retry-20261105');old=R/'nine-sharing-norm38-gates-batched-draft';base=Path('/tmp/nine-sharing-norm38-gates-batched-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='1ca0968a7e2acfbd398302581e30f3c02caebcf2a4c81081ba73e0b913ea8b72'
assert sha(a/'outer-terminal-author-record.json')=='e4ea0d8bf9f8b333ac77b2c83b777a18ed7a1b2009a898b61444cf5394f63a46';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==2051 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
src=q/'src/DiophantineConsistency/Norm38GatesAssembly.lean';prior=old/'src/DiophantineConsistency/Norm38GatesAssembly.lean';assert sha(src)==sha(out/'src/DiophantineConsistency/Norm38GatesAssembly.lean')=='c5dec04f7956dac3572fdcf45ef1c763c2c76c41e7e6705c9e2a56e3a948b639';before=prior.read_text();assert before.count('gate80 p ports w hp hz⟩')==1 and before.replace('gate80 p ports w hp hz⟩','gate80 p ports w hp hz, by simp⟩')==src.read_text()
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Norm38GatesAssembly' and r['source_sha256']==sha(src);obj=out/'lib/DiophantineConsistency/Norm38GatesAssembly.olean';assert r['object_sha256']=='70830fc749e108a9776b1ec8274427e47476d3dbb94916688b0a76a2fc476b09'==sha(obj)
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 key=str(p.resolve())
 if key not in cache:cache[key]=sha(p)
 assert cache[key]==h
def guards(g):
 for path,v in g.items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
for typ in ('deps','compile'):
 v=r[typ];assert v['exit']==0 and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(a/('Norm38GatesAssembly-'+typ+'.txt'))==sha(out/('Norm38GatesAssembly-'+typ+'.txt'))==v['log_sha256']
assert (a/'Norm38GatesAssembly-compile.txt').read_text().count('warning:')==2
guards(r['direct_guard'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
oldstate=old/'attempt01/state.json';assert sha(oldstate)=='fc4e64a0bb36abdff0d51a21e29bebd4d8771f688f9a0a8fc56d700731317e65';b=json.loads(oldstate.read_text());assert b['status']=='FAILED' and b['rows'][-1]['module']=='Norm38GatesAssembly' and b['rows'][-1]['compile']['exit']==1
producers=b['rows'][:12];assert [x['module'] for x in producers]==[f'Norm38Gates{i:02d}' for i in range(12)]
for row in producers:
 n=row['module'];assert row['deps']['exit']==row['compile']['exit']==0 and row['deps']['stop_reason'] is row['compile']['stop_reason'] is None
 check(base/'src/DiophantineConsistency'/(n+'.lean'),row['source_sha256']);check(base/'lib/DiophantineConsistency'/(n+'.olean'),row['object_sha256'])
 for typ in ('deps','compile'):check(base/(n+'-'+typ+'.txt'),row[typ]['log_sha256'])
 guards(row['direct_guard']);dep=r['dependencies']['DiophantineConsistency.'+n];assert dep['sha256']==row['object_sha256'];check(dep['path'],dep['sha256'],dep['realpath']);assert Path(dep['path']).is_symlink() and Path(dep['path']).resolve()==(base/'lib/DiophantineConsistency'/(n+'.olean')).resolve()
review=D/'reviews/nine-sharing-norm38-gates-batched-independent';z=subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],capture_output=True);assert z.returncode==0 and not z.stderr and z.stdout==(review/'result.json').read_bytes()
print(json.dumps({'status':'PASS_GATES_ASSEMBLY_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':sha(obj),'author_recorded_outer_session':2051,'author_recorded_exit':0,'candidate_guard_slots':len(r['direct_guard']),'producer_guard_slots':sum(len(x['direct_guard']) for x in producers),'overlay_links':len(s['overlay_links']),'direct_producers':{x['module']:x['object_sha256'] for x in producers},'scope':'Retained source/logs/object and producer guard point checks; no Lean replay or independent historical outer observation.'},indent=2,sort_keys=True))
