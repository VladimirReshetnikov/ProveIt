import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-four-variable-ports-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-four-variable-ports-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38FourVariablePorts'
assert sha(a/'state.json')==sha(out/'state.json')=='c3bf8f529e151226e83d9b8db93a025f6eaf1e7d3795d2395e47ca6b731321b0';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='c7e1f7e465cf89c0d5ca5e3231cf0ddc96bcd35fa31399d219174a119df75c09'
assert sha(q/'run.py')==s['runner_sha256']=='39f9e980a646f279ccca90e5c1d8f8885cfa83b6dd71b63cc826ab4257122e56' and sha(q/'source-manifest.json')=='b0a4e6a276d070640a70987791d1a46761bbb474baa7cf1527b61f5f10b285e6'
assert sha(a/'outer-terminal-author-record.json')=='44328cc85367597372b46a6eb2ec68d24558ef55678ed5f6890bf686f6c8f53b';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==55176 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='24c2e6a9ccfa40c8766e53c9523cbc4562322308279b8e7f3afa51b9e08c7302' and r['object_sha256']=='507e42e05050f66b1ee65be5826cac20bab0da1484c95a9f7964e4844e0fd68e'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
for i,v in enumerate(('b','k','l','h')):assert t.count(f'(h{i} : ((p {i} : ℤ) : DiffRing V) = ι {v})')==2
assert 'InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w) ↔' in t and 'NormAssignment38.gatesHold ι (naturalPorts b k l h) w ∧' in t and 'NormAssignment38.fiveNorms ι (naturalPorts b k l h) w' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert log.count('depends on axioms: [propext,\n Classical.choice,\n Quot.sound]')==2 and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38FinFour':'6d5c93c760bc537fb5fcbbe4e7d12499c2fda37139c7df6a38a8409f2c614707','Norm38SeedStaticIff':'b66b343c8806e38f1c247fed3493622102fa2c0f6114cd1d60bb95e0a2fa8af0'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
for name in ('nine-sharing-norm38-current-ports-abstract-terminal-independent','nine-sharing-norm38-seed-static-iff-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':55176,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Port-parametric with four explicit cast assumptions, not a concrete instantiation or endpoint; no Lean replay.'},indent=2,sort_keys=True))
