import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-four-cast-instantiation-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-four-cast-instantiation-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentFourCastInstantiation'
assert sha(a/'state.json')==sha(out/'state.json')=='bad562eeca80d04d60ede99deb281686134612c3c091230a7326dd850b5deabf';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='c3bf8f529e151226e83d9b8db93a025f6eaf1e7d3795d2395e47ca6b731321b0'
assert sha(q/'run.py')==s['runner_sha256']=='be2be3f2c1708d38c7c6466a8036d8673f7ebd989ba4cdc1db001ff43e1892e8' and sha(q/'source-manifest.json')=='ceb6011af0cd26f06beb5f697daac9bcb08e3952763e5a621b3dcc441d77a30e'
assert sha(a/'outer-terminal-author-record.json')=='56e675b1ded0af84c880203842150d2c2de44d09813c41001892cdea3a686e1c';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==99640 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='8d9e2996454c0fd2ffbc05055db11cab7ab1ca22cef5b93ba8149cf535f0fa1e' and r['object_sha256']=='4f6ea58e06ea51ee24b830daba85da258de463e51587b37e89cfb1dbefffac95'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports) (Fin.cons (1 : V) w) ↔' in t and 'NormAssignment38.gatesHold ι (currentNaturalPorts (V := V)) w ∧' in t and 'NormAssignment38.fiveNorms ι (currentNaturalPorts (V := V)) w' in t
assert 'Norm38CurrentPorts.port0 Norm38CurrentPorts.port1 Norm38CurrentPorts.port2 Norm38CurrentPorts.port3' in t and t.count('CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ')==2
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "'DiophantineConsistency.Norm38CurrentFourCastInstantiation.current_seed_zero_iff_static' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
pstate=json.loads((R/'nine-sharing-norm38-current-ports-split-draft/attempt01/state.json').read_text());gstate=json.loads((R/'nine-sharing-norm38-four-variable-ports-check/attempt01/state.json').read_text())
for i in range(4):
 dep=r['dependencies'][f'DiophantineConsistency.Norm38CurrentPort{i}'];assert dep['sha256']==pstate['rows'][i+1]['object_sha256'];check(dep['path'],dep['sha256'],dep['realpath'])
dep=r['dependencies']['DiophantineConsistency.Norm38FourVariablePorts'];assert dep['sha256']==gstate['rows'][0]['object_sha256'];check(dep['path'],dep['sha256'],dep['realpath'])
for name in ('nine-sharing-norm38-current-ports-split-terminal-independent','nine-sharing-norm38-four-variable-ports-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':99640,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Current symbolic seed/static equivalence only; no source bridge, byte-file identity or endpoint; no Lean replay.'},indent=2,sort_keys=True))
