import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-ports-split-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-ports-split-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38CurrentPortCasts')" and s['base_state_sha256']=='ebc30ad19643e6e0fe5eb5f253163d660c8510165e902d53150e11d75a9be578'
assert sha(q/'run.py')==s['runner_sha256']=='67b968d31634547dd97c10d238b3a1a8abeb7bc605516581518d26cb8564da9f' and sha(q/'source-manifest.json')=='868481d10dc1dfd490aec4e34466cce1c90eedb98a1d2d1b196d1686558e9cc7'
assert sha(a/'outer-terminal-author-record.json')=='05eed1d33296cb26c3f7d12c6a1de55d76c95a9df228741170f9bac1a285305a';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==82964 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
rows=s['rows'];names=['Norm38CurrentPortBase']+[f'Norm38CurrentPort{i}' for i in range(4)]+['Norm38CurrentPortCasts'];assert [r['module'] for r in rows]==names
manifest=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(manifest)==7
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for i,r in enumerate(rows):
 n=r['module'];assert r['source_sha256']==manifest[i]['source_sha256'];check(q/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256'])
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==(1 if i==5 and phase=='compile' else 0) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():check(v['path'],v['sha256'],v['realpath'])
 if i<5:check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 else:assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
 if 1<=i<=4:
  log=(a/f'{n}-compile.txt').read_text();assert f".port{i-1}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log and 'warning:' not in log
bad=(a/'Norm38CurrentPortCasts-compile.txt').read_text();assert ':15:8: error: (kernel) excessive memory consumption detected' in bad and 'DiophantineConsistency.Norm38CurrentPorts.port_casts]' in bad
assert not (a/'Norm38CurrentPortSpecialization-compile.txt').exists()
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for i in range(1,5):assert rows[i]['dependencies']['DiophantineConsistency.Norm38CurrentPortBase']['sha256']==rows[0]['object_sha256']
for i in range(4):assert rows[5]['dependencies'][f'DiophantineConsistency.Norm38CurrentPort{i}']['sha256']==rows[i+1]['object_sha256']
p=D/'reviews/nine-sharing-norm38-current-ports-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_recorded_session':82964,'author_recorded_exit':1,'successful_modules':{r['module']:r['object_sha256'] for r in rows[:5]},'failed_module':rows[5]['module'],'failed_compile_exit':1,'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'scope':'No Lean replay; universal axiom report includes failed declaration; specialization unrun.'},indent=2,sort_keys=True))
