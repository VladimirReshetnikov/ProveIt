import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-castfree-iff-draft';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-castfree-iff-check-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentCastFreeIff'
assert sha(a/'state.json')==sha(out/'state.json')=='668decb8f55d4566093bdfd08b448bfb4affeb7cec695f7df23f1b8f7a8183cd';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='dcbe82fca2f8c866e301d62281696fed13c33ca9240449b784e8439510674ba9'
assert sha(q/'run.py')==s['runner_sha256']=='234eb0dd0ae1ddb20cfb5320382fc14ffc1e58ce4e4222af63a1c995ac850427' and sha(q/'source-manifest.json')=='24ffd02320bf374ea9b1efa1e73cdddb3f3f1857f6a7548c6042ad705a316294' and sha(q/'provider_preflight.py')=='5ea423580ce4d58e528f3416aafba68b439b92f1aee99c32366f68e2ac464a5e'
assert sha(a/'outer-terminal-author-record.json')=='b851f3cfd5174143dc233e8e1ad644d3f9870da3fbbc02f921eabede31fc13e1';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==34596 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='f520c209256a1de37ba62be9d89a791888ce998c25f9999bed19f432a66297c7' and r['object_sha256']=='9a2021036f3598cccb7c9128f858544a33b985c5aa9f7463f39eefac430135f8'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '∀ j, ((CurrentWindowCarry2011.ports j : ℤ)' not in t and t.count('∃ u : Fin 14 → V')==2 and t.count('(fun j => u j + 1)')==2 and '∃ w : Fin 38 → V' in t and '∃ a : Fin 9 → V' in t and 'Norm38CurrentSourceFourCasts.source_zero_implies_seed_zero u hu' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert log.count('depends on axioms: [propext,\n Classical.choice,\n Quot.sound]')==2 and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38CurrentSeedSource':'176750b96fc712e1827066d61958dd164852427587d599d5846aeec4d1207d10','Norm38CurrentSourceFourCasts':'d0419dac500817ece12c1d6d4d4a90ab78afb45fe62447a2d2311a9b1d980a43','SharingSeed38CurrentJones':'9a4695880ffc229505e7cf46a77fb436cb1e7d41f132690cdeb6eb72f4836e2e'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True,text=True,timeout=120);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY',(x.stdout,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':34596,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Cast-free current symbolic seed/source and nine/source existential equivalences under IΣ₁, shifted source; no iPRA endpoint or Lean replay.'},indent=2,sort_keys=True))
