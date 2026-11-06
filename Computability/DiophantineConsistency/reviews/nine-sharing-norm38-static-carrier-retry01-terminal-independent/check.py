import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-static-carrier-retry01';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-static-carrier-retry01-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38StaticCarrierConditional'
assert sha(a/'state.json')==sha(out/'state.json')=='36522d2c3ecc5be94735b41e9a45be77569c71f1da80d10da87c78f13d919f27';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38StaticCarrierConditional')" and s['base_state_sha256']=='7bd683c7d990981e7b1172c16c73c294a4da4f88382949da0d88158c5c580fbc'
assert sha(q/'run.py')==s['runner_sha256']=='1ab0deed6ea76be5ac2265ab32266909cf530507d2c57a21a381eb976c09117b' and sha(q/'source-manifest.json')=='6dd77a2333268b3739856bbc405ca639dfc0ae2e5a8eeeac4ee3f04e99ce53d8'
assert sha(a/'outer-terminal-author-record.json')=='2f124d354b65d62ab2fde85473b4eea6ae15bea963acfdfede7902eaa6ebe6cf';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==89636 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='13c7a4433cf5deac75fe279e70c816f093de875f4c05af90f1c925d98bd4ed6c' and 'object_sha256' not in r
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);assert not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
prior=(R/'nine-sharing-norm38-reference-fields-combine-check/src/DiophantineConsistency'/f'{n}.lean').read_text();assert src.read_text()==prior.replace('  rw [ht0,ht1,hta,htt,hts,htd,hc0,hc1,hca,hct,hcs,hcd] at hn','  dsimp only at hn\n  rw [ht0,ht1,hta,htt,hts,htd,hc0,hc1,hca,hct,hcs,hcd] at hn')
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==(0 if phase=='deps' else 1) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert 'error: Ambiguous term' in log and 'sub_self' in log and 'error: unsolved goals' in log and 'sorryAx' in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
dep=r['dependencies']['DiophantineConsistency.Norm38ReferenceFieldsAll'];assert dep['sha256']=='3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd';check(dep['path'],dep['sha256'],dep['realpath'])
p=D/'reviews/nine-sharing-norm38-reference-fields-combine-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_FAILURE_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_recorded_session':89636,'author_recorded_exit':1,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'No Lean replay; ambiguous sub_self and unsolved goals, axiom report contains sorryAx.'},indent=2,sort_keys=True))
