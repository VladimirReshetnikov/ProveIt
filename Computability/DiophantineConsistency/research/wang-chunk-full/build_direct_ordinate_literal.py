"""Scoped actual 86/87 literal binding, conditional on signed-square equivalence."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');P=Path('/tmp/adaptive-first-root-factor87-literal-vi8qg8sd');Q=Path('/tmp/adaptive-direct-ordinate-context-tzc7q_t4');G=Path('/tmp/ha-expression-closure-exact.json');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/AdaptiveDirectOrdinate86Literal.lean';T=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/AdaptiveDirectOrdinate86Context.lean';C=R/'Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/candidate.json';J=R/'Computability/DiophantineConsistency/research/adaptive-direct-ordinate86/build_literal_lean.py';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());bs=read(B/'state.json');ps=read(P/'state.json');qs=read(Q/'state.json');g=read(B/'guards.json');pr=read(B/'providers.json');pp=read(P/'providers.json');graph=read(G);assert bs['status']==ps['status']==qs['status']=='PASS' and sha(B/'guards.json')==bs['guards_sha256']==ps['canonical_guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and sha(P/'providers.json')==ps['providers_sha256'] and sha(B/'state.json')==ps['canonical_state_sha256']==qs['base_state_sha256'];bh=sha(B/'state.json');ph=sha(P/'state.json');qh=sha(Q/'state.json');gh=sha(G);sh=sha(S);th=sha(T);ch=sha(C);jh=sha(J);assert ch=='e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f' and sha(T)==qs['source_sha256'] and sha(Q/'lib/DiophantineConsistency/AdaptiveDirectOrdinate86Context.olean')==qs['object_sha256']
seen=set()
def visit(k):
 if k in seen:return
 seen.add(k)
 for x in graph['edges'].get(k,[]):visit(x)
for k in ['DiophantineConsistency.AdaptiveFirstRootFactor87Literal','DiophantineConsistency.AdaptiveFirstRootFactor87Syntax','DiophantineConsistency.ArithmeticSignedPairs']:visit(k)
assert 'DiophantineConsistency.ArithmeticAdaptivePopulation2011' not in seen
sources={};replayed={};boundary={};providerstates={}
for k in sorted(seen):
 path=R/graph['sources'][k]
 if not path.is_file():boundary[k]=graph['sources'][k];continue
 actual=sorted(x for line in path.read_text().splitlines() if line.startswith('import ') for x in line[7:].split());assert actual==sorted(graph['edges'].get(k,[]));key=k.replace('.','/')+'.olean';obj=P/'lib'/key;assert obj.exists()
 if str(path) in g:
  assert sha(path)==g[str(path)] and key in pr and sha(obj)==pr[key]['sha256'];sources[str(path)]=g[str(path)]
 else:
  root=obj.resolve().parents[2];st=read(root/'state.json');assert st['status']=='PASS';providerstates[str(root)]=sha(root/'state.json');row=next(x for x in st['records'] if 'DiophantineConsistency.'+x['name']==k);assert row['exit']==0 and sha(path)==row['source_sha256'] and sha(obj)==row['object_sha256'] and sha(root/'logs'/(row['name']+'.log'))==row['log_sha256'];replayed[k]={'source':str(path),'source_sha256':row['source_sha256'],'object':str(obj.resolve()),'object_sha256':row['object_sha256'],'log':str(root/'logs'/(row['name']+'.log')),'log_sha256':row['log_sha256']}
assert len(sources)==17 and len(replayed)==5 and len(boundary)==16
population=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticAdaptivePopulation2011.lean';poph=sha(population);assert str(population) in g and poph!=g[str(population)]
def auth():
 return (sha(B/'state.json')==bh and sha(P/'state.json')==ph and sha(Q/'state.json')==qh and sha(G)==gh and sha(S)==sh and sha(T)==th and sha(C)==ch and sha(J)==jh and sha(population)==poph and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and sha(P/'providers.json')==ps['providers_sha256'] and all(sha(p)==h for p,h in sources.items()) and all(sha(Path(p)/'state.json')==h for p,h in providerstates.items()) and all(sha(x['source'])==x['source_sha256'] and sha(x['object'])==x['object_sha256'] and sha(x['log'])==x['log_sha256'] for x in replayed.values()) and sha(Q/'lib/DiophantineConsistency/AdaptiveDirectOrdinate86Context.olean')==qs['object_sha256'] and sha(Q/'build.log')==qs['log_sha256'] and all(sha(x['path'])==x['sha256'] for x in pr.values()) and all(sha(x['path'])==x['sha256'] for x in pp))
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-direct86-literal-'));shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(S,w/'source-snapshot.lean');shutil.copyfile(C,w/'candidate.json');lib=w/'lib'
for f in (P/'lib').rglob('*'):
 if f.is_file():
  rel=f.relative_to(P/'lib');dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(f.resolve())
dst=lib/'DiophantineConsistency/AdaptiveDirectOrdinate86Context.olean';assert not dst.exists();dst.symlink_to((Q/'lib/DiophantineConsistency/AdaptiveDirectOrdinate86Context.olean').resolve())
state={'status':'RUNNING','private':str(w),'base_state_sha256':bh,'literal87_state_sha256':ph,'context_state_sha256':qh,'graph_sha256':gh,'source_sha256':sh,'candidate_sha256':ch,'generator_sha256':jh,'reachable_guarded_sources':sources,'reachable_replayed_sources':replayed,'replayed_provider_states':providerstates,'inherited_boundaries':boundary,'unrelated_population_guard_expected':g[str(population)],'unrelated_population_current':poph,'scope':'Actual 86/87 literal contexts and conditional zero-test equivalence under equivalent squared ordinates; source-current reachable slice with inherited boundaries, not natural witness directions or HA equivalence.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True);env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);o=lib/'DiophantineConsistency/AdaptiveDirectOrdinate86Literal.olean';log=w/'build.log';tim=w/'build.time';cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(o),str(S)];state['command']=cmd;save();print('START',flush=True);start=time.monotonic()
try:
 with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-start,log_sha256=sha(log),time_sha256=sha(tim));
 if o.exists():state['object_sha256']=sha(o)
 save();print('DONE',code,flush=True)
 if code:raise RuntimeError('Lean build failed')
 assert auth() and sha(o)==state['object_sha256'] and sha(log)==state['log_sha256'];state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
