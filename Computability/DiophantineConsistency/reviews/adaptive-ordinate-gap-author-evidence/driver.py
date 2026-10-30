"""Build conditional direct-ordinate recovery on the authenticated base."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptiveOrdinateGap2011.lean';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());bs=read(B/'state.json');g=read(B/'guards.json');pr=read(B/'providers.json');assert bs['status']=='PASS' and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'];bh=sha(B/'state.json');sh=sha(S);direct=['DiophantineConsistency/ArithmeticPellHalfIndex.olean','DiophantineConsistency/ArithmeticSignedPairs.olean'];assert all(sha(B/'lib'/k)==pr[k]['sha256'] for k in direct)
G=Path('/tmp/ha-expression-closure-exact.json');graph=read(G);gh=sha(G);seen=set()
def visit(k):
 if k in seen:return
 seen.add(k)
 for x in graph['edges'].get(k,[]):visit(x)
for k in ['DiophantineConsistency.ArithmeticPellHalfIndex','DiophantineConsistency.ArithmeticSignedPairs']:visit(k)
assert 'DiophantineConsistency.ArithmeticAdaptivePopulation2011' not in seen
sources={};boundary={}
for k in sorted(seen):
 path=R/graph['sources'][k]
 if not path.is_file():boundary[k]=graph['sources'][k];continue
 assert str(path) in g and sha(path)==g[str(path)]
 actual=sorted(x for line in path.read_text().splitlines() if line.startswith('import ') for x in line[7:].split());assert actual==sorted(graph['edges'].get(k,[]))
 sources[str(path)]=g[str(path)]
assert len(sources)==15 and len(boundary)==4
population=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptivePopulation2011.lean';population_hash=sha(population);assert str(population) in g and population_hash!=g[str(population)]
def auth():return sha(B/'state.json')==bh and sha(S)==sh and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and sha(G)==gh and sha(population)==population_hash and all(sha(p)==h for p,h in sources.items()) and all(sha(x['path'])==x['sha256'] for x in pr.values()) and all(sha(B/'lib'/k)==pr[k]['sha256'] for k in direct)
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-ordinate-gap-scoped-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean');lib=w/'lib'
for f in (B/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(B/'lib');dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
state={'status':'RUNNING','private':str(w),'base_state_sha256':bh,'guards_sha256':bs['guards_sha256'],'providers_sha256':bs['providers_sha256'],'source_sha256':sh,'direct_imports':{k:pr[k]['sha256'] for k in direct},'closure_graph_sha256':gh,'reachable_guarded_sources':sources,'inherited_boundaries':boundary,'unrelated_population_guard_expected':g[str(population)],'unrelated_population_current':population_hash,'scope':'Conditional all-model offset lemmas with a current 15-source direct-import slice, four inherited package/Foundation boundaries and a stale unrelated population guard; no complete provider-current, changed-equation or HA claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);o=lib/'DiophantineConsistency/ArithmeticAdaptiveOrdinateGap2011.olean';log=w/'build.log';tim=w/'build.time';cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
try:
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 assert auth() and sha(o)==state['object_sha256'] and sha(log)==state['log_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
