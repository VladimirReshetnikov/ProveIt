"""Replay direct-ordinate auxiliary norm with scoped inherited boundaries."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');P=Path('/tmp/adaptive-direct86-literal-qpkx_sbs');C=Path('/tmp/adaptive-direct-ordinate-context-tzc7q_t4');L=Path('/tmp/adaptive-first-root-factor87-literal-vi8qg8sd');F=Path('/tmp/adaptive13-factor-c9mdkg_f');U=Path('/tmp/adaptive13-units-ptx0g7i9');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';GEN=R/'Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/build_factors_lean.py';CAND=GEN.parent/'candidate.json';GRAPH=Path('/tmp/ha-expression-closure-exact.json')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
bs,ps,cs,ls,fs,us=map(lambda x:read(x/'state.json'),[B,P,C,L,F,U]);pr=read(B/'providers.json');lp=read(L/'providers.json');g=read(B/'guards.json');graph=read(GRAPH)
assert all(x['status']=='PASS' for x in [bs,ps,cs,ls,fs,us]);assert sha(B/'state.json')==ps['base_state_sha256']==cs['base_state_sha256'];assert sha(C/'state.json')==ps['context_state_sha256'] and sha(L/'state.json')==ps['literal87_state_sha256'];assert sha(B/'providers.json')==bs['providers_sha256'] and sha(B/'guards.json')==bs['guards_sha256'] and sha(L/'providers.json')==ls['providers_sha256']
Z=Path('/tmp/adaptive-direct86-factors-6q8xw_z_');zs=read(Z/'state.json');assert zs['status']=='PASS';zh=sha(Z/'state.json');names=['AdaptiveDirectOrdinate86AuxNorm'];snaps={n:sha(S/(n+'.lean')) for n in names};states={str(x):sha(x/'state.json') for x in [B,P,C,L,F,U]};gh=sha(GRAPH);genh=sha(GEN);candh=sha(CAND);sources=ps['reachable_guarded_sources'];replayed=ps['reachable_replayed_sources'];poph=sha(R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptivePopulation2011.lean');assert poph==ps['unrelated_population_current']
seen=set()
def visit(k):
 if k in seen:return
 seen.add(k)
 for v in graph['edges'].get(k,[]):visit(v)
for k in ['DiophantineConsistency.AdaptiveFirstRootFactor87Literal','DiophantineConsistency.AdaptiveFirstRootFactor87Syntax','DiophantineConsistency.ArithmeticSignedPairs','DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011','DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011']:visit(k)
assert not any(x in seen for x in ['DiophantineConsistency.ArithmeticAdaptivePopulation2011','DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011','DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011'])
extra=[('ArithmeticAdaptiveFactorMagnitude2011',F,fs),('ArithmeticAdaptiveFactorUnits2011',U,us)]
def auth():
 return (sha(Z/'state.json')==zh and all(sha(S/(r['name']+'.lean'))==r['source_sha256'] and sha(Z/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(Z/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in zs['records']) and all(sha(Path(p)/'state.json')==h for p,h in states.items()) and sha(GRAPH)==gh and sha(GEN)==genh and sha(CAND)==candh and all(sha(S/(n+'.lean'))==h for n,h in snaps.items()) and all(sha(p)==h for p,h in sources.items()) and all(sha(x['source'])==x['source_sha256'] and sha(x['object'])==x['object_sha256'] and sha(x['log'])==x['log_sha256'] for x in replayed.values()) and all(sha(Path(p)/'state.json')==h for p,h in ps['replayed_provider_states'].items()) and all(sha(x['path'])==x['sha256'] for x in pr.values()) and all(sha(x['path'])==x['sha256'] for x in lp) and all(sha(S/(n+'.lean'))==st['snapshots'][n] and sha(P/'lib/DiophantineConsistency'/(n+'.olean'))==next(r['object_sha256'] for r in st['records'] if r['name']==n) and sha(p/'logs'/(n+'.log'))==next(r['log_sha256'] for r in st['records'] if r['name']==n) for n,p,st in extra) and sha(S/'AdaptiveDirectOrdinate86Literal.lean')==ps['source_sha256'] and sha(P/'lib/DiophantineConsistency/AdaptiveDirectOrdinate86Literal.olean')==ps['object_sha256'] and sha(P/'build.log')==ps['log_sha256'] and sha(R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptivePopulation2011.lean')==poph)
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-direct86-auxnorm-'));shutil.copyfile(__file__,w/'driver.py');(w/'logs').mkdir();lib=w/'lib'
for n in names:shutil.copyfile(S/(n+'.lean'),w/'logs'/(n+'.lean'))
for f in (Z/'lib').rglob('*'):
 if f.is_file():
  dst=lib/f.relative_to(Z/'lib');dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
state={'status':'RUNNING','private':str(w),'input_states':states,'factor_state_sha256':zh,'graph_sha256':gh,'candidate_sha256':candh,'generator_sha256':genh,'source_graph':sorted(seen),'reachable_guarded_sources':sources,'snapshots':snaps,'records':[],'scope':'Actual 86 unshifted zero implies the additive auxiliary norm for the raw signed magnitude in arbitrary IΣ₁ models. Current reachable slice, historical object/provider boundaries retained; unrelated Population drift excluded. No binding of the signed magnitude to the 14-coordinate client, residue extraction, zero-set equivalence or HA claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
try:
 for n in names:
  src=S/(n+'.lean');o=lib/'DiophantineConsistency'/(n+'.olean');log=w/'logs'/(n+'.log');tim=w/'logs'/(n+'.time');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(src)];assert not o.exists() and sha(src)==snaps[n];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if o.exists():row['object_sha256']=sha(o)
  state['records'].append(row);save();print('DONE',n,code,flush=True)
  if code:raise RuntimeError(n)
 assert auth() and all(sha(w/'logs'/(r['name']+'.lean'))==r['source_sha256'] and sha(lib/'DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name']+'.log'))==r['log_sha256'] and sha(w/'logs'/(r['name']+'.time'))==r['time_sha256'] for r in state['records']);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
