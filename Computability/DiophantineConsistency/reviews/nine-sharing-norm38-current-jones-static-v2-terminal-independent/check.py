import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-jones-static-check-v2';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-jones-static-check-v2-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentJonesStatic'
assert sha(a/'state.json')==sha(out/'state.json')=='c9af7e79ed82a7edb511c3169cca1b395915e32b320a5b3363e26c772bcc15fd';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='bad562eeca80d04d60ede99deb281686134612c3c091230a7326dd850b5deabf'
assert sha(q/'run.py')==s['runner_sha256']=='6409649ccd18fd4feab5c80a7ef189017f65476cc069694bcbf909038d7e4cff' and sha(q/'source-manifest.json')=='cf5a9b203599b2af0d249a55699c08ef76bf57874595a2d5b1969f2df7f6df6c'
assert sha(a/'outer-terminal-author-record.json')=='43796252fbde98d44f73db824724bff99a5bdd1d28192d3db809464c7ed6a990';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==19124 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='a70a6b65e73914d47cac0f71c4b0440f5ff53f125834c335164a3b689bfb5f10' and r['object_sha256']=='ca1ad9a9e82bab0a461574b5023a839db1669115c747b0c8bf83b62368a3c911'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '(∃ a : Fin 9 → V,' in t and '(ExecutableJones.expression (SharingSeed38.seed CurrentWindowCarry2011.ports) 0).evalRing' in t and '∃ w : Fin 38 → V,' in t and 'NormAssignment38.gatesHold ι' in t and 'NormAssignment38.fiveNorms ι' in t and 'SharingSeed38CurrentJones.current_nine_iff' in t and 'Norm38CurrentFourCastInstantiation.current_seed_zero_iff_static w' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "current_nine_zero_iff_static' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38CurrentFourCastInstantiation':'4f6ea58e06ea51ee24b830daba85da258de463e51587b37e89cfb1dbefffac95','SharingSeed38CurrentJones':'9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
for name in ('nine-sharing-norm38-current-four-cast-terminal-independent','nine-sharing-seed38-current-jones-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':19124,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Nine-coordinate Jones zero iff existence of 38-coordinate current static valuation in an IΣ₁ model; not a Carrier65 bridge or iPRA endpoint; no Lean replay.'},indent=2,sort_keys=True))
