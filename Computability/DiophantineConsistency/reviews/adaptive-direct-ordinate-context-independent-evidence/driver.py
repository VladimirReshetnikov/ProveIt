"""Scoped signed-context bridge build with explicit stale unrelated guard."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');P=Path('/tmp/adaptive-first-root-factor87-syntax-cemx04n3');G=Path('/tmp/ha-expression-closure-exact.json');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/AdaptiveDirectOrdinate86Context.lean';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());bs=read(B/'state.json');ps=read(P/'state.json');g=read(B/'guards.json');pr=read(B/'providers.json');pp=read(P/'providers.json');graph=read(G);assert bs['status']==ps['status']=='PASS' and sha(B/'guards.json')==bs['guards_sha256']==ps['base_guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and sha(P/'providers.json')==ps['providers_sha256'] and sha(B/'state.json')==ps['base_state_sha256'];gen=(P/'lib/DiophantineConsistency/AdaptiveFirstRootFactor87.olean').resolve().parents[2];gs=read(gen/'state.json');assert gs['status']=='PASS' and sha(gen/'state.json')==ps['generic_state_sha256'];bh=sha(B/'state.json');ph=sha(P/'state.json');gh=sha(G);sh=sha(S);seen=set()
def visit(k):
 if k in seen:return
 seen.add(k)
 for x in graph['edges'].get(k,[]):visit(x)
for k in ['DiophantineConsistency.AdaptiveFirstRootFactor87Syntax','DiophantineConsistency.ArithmeticSignedPairs']:visit(k)
assert 'DiophantineConsistency.ArithmeticAdaptivePopulation2011' not in seen
sources={};boundary={};nonguard={}
for k in sorted(seen):
 path=R/graph['sources'][k]
 if not path.is_file():boundary[k]=graph['sources'][k];continue
 actual=sorted(x for line in path.read_text().splitlines() if line.startswith('import ') for x in line[7:].split());assert actual==sorted(graph['edges'].get(k,[]))
 if str(path) in g:assert sha(path)==g[str(path)];sources[str(path)]=g[str(path)]
 else:
  root=gen if k.endswith('AdaptiveFirstRootFactor87') else P
  row=next(x for x in read(root/'state.json')['records'] if 'DiophantineConsistency.'+x['name']==k)
  assert row['exit']==0 and sha(path)==row['source_sha256'] and sha(root/'lib/DiophantineConsistency'/(row['name']+'.olean'))==row['object_sha256'] and sha(root/'logs'/(row['name']+'.log'))==row['log_sha256'];nonguard[k]={'source':str(path),'source_sha256':row['source_sha256'],'object':str(root/'lib/DiophantineConsistency'/(row['name']+'.olean')),'object_sha256':row['object_sha256'],'log':str(root/'logs'/(row['name']+'.log')),'log_sha256':row['log_sha256']}
assert len(sources)==5 and len(nonguard)==2 and len(boundary)==9
population=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptivePopulation2011.lean';poph=sha(population);assert str(population) in g and poph!=g[str(population)]
def auth():
 return (sha(B/'state.json')==bh and sha(P/'state.json')==ph and sha(gen/'state.json')==ps['generic_state_sha256'] and sha(G)==gh and sha(S)==sh and sha(population)==poph and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and sha(P/'providers.json')==ps['providers_sha256'] and all(sha(p)==h for p,h in sources.items()) and all(sha(x['source'])==x['source_sha256'] and sha(x['object'])==x['object_sha256'] and sha(x['log'])==x['log_sha256'] for x in nonguard.values()) and all(sha(x['path'])==x['sha256'] for x in pr.values()) and all(sha(x['path'])==x['sha256'] for x in pp))
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-direct-ordinate-context-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean');lib=w/'lib'
for f in (P/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(P/'lib');dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
state={'status':'RUNNING','private':str(w),'base_state_sha256':bh,'syntax_state_sha256':ph,'generic_state_sha256':ps['generic_state_sha256'],'graph_sha256':gh,'source_sha256':sh,'reachable_guarded_sources':sources,'reachable_replayed_sources':nonguard,'inherited_boundaries':boundary,'unrelated_population_guard_expected':g[str(population)],'unrelated_population_current':poph,'scope':'Generic signed-context congruence with five current guarded sources, two replayed syntax sources and nine inherited boundaries; unrelated Population guard stale. No changed-equation zero-set equivalence or HA claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);o=lib/'DiophantineConsistency/AdaptiveDirectOrdinate86Context.olean';log=w/'build.log';tim=w/'build.time';cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
try:
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 assert auth() and sha(o)==state['object_sha256'] and sha(log)==state['log_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
