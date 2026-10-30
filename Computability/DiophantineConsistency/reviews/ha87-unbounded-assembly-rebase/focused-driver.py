from pathlib import Path
import argparse, hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';ha=Path('/tmp/ha-expression-assembly-vgttkwsl');model=Path('/tmp/adaptive-unconditional-equivalence-ptaobui4');graph=Path('/tmp/ha-focused-unbounded-assembly-source-graph.json');plan=Path('/tmp/ha-preserved-model-rebuild-plan.json')
p=argparse.ArgumentParser();p.add_argument('--resume',type=Path);p.add_argument('--rebase',type=Path);args=p.parse_args();assert not (args.resume and args.rebase);sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
root=args.resume.resolve() if args.resume else Path(tempfile.mkdtemp(prefix='ha87-focused-validator-rebase-'));statepath=root/'state.json'
def save():
 tmp=root/'state.json.tmp';tmp.write_text(json.dumps(state,indent=2)+'\n');tmp.replace(statepath)
def require(path,h,why):
 if not path.is_file() or sha(path)!=h:raise RuntimeError(f'{why} changed or absent: {path}')
if args.resume:
 state=json.loads(statepath.read_text());state.update(status='RUNNING',phase='resume authentication',failure=None);save()
else:
 state={'status':'RUNNING','phase':'initialization','root':str(root),'records':[],'qualification':'Focused provisional integration preserving the complete historical HA object provider on every shared project object, rebuilding affected adaptive descendants that are absent from the HA boundary, and compiling the exact 87 endpoint. The historical HA source/object ancestry and unlisted dependencies, Foundation and Mathlib are inherited and not source-current authenticated. No claim of full-source provenance.'};save()
print('ROOT',root,flush=True)
try:
 g=json.loads(graph.read_text());pl=json.loads(plan.read_text());sources=dict(g['sources']);edges=dict(g['edges'])
 compat='DiophantineConsistency.ArithmeticHalfBinomialCompat'; compat_check=compat+'Checks'
 asm='DiophantineConsistency.ArithmeticConstructionUnboundedCompat';asm_check=asm+'Checks'
 sources[asm_check]='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticConstructionUnboundedCompatChecks.lean';edges[asm_check]=[asm]
 ord='DiophantineConsistency.ArithmeticPellOrdinateCompat'; ord_check=ord+'Checks'
 sources[ord_check]='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticPellOrdinateCompatChecks.lean';edges[ord_check]=[ord]
 sources[compat_check]='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticHalfBinomialCompatChecks.lean';edges[compat_check]=[compat]
 endpoint='DiophantineConsistency.HAAdaptiveFactor87';endpoint_check=endpoint+'Checks'
 sources[endpoint]='Computability/DiophantineConsistency/Lean/DiophantineConsistency/HAAdaptiveFactor87.lean';edges[endpoint]=['DiophantineConsistency.HAExpressionAssembly','DiophantineConsistency.ArithmeticAdaptiveEquivalenceUnconditional2011']
 sources[endpoint_check]='Computability/DiophantineConsistency/Lean/DiophantineConsistency/HAAdaptiveFactor87Checks.lean';edges[endpoint_check]=[endpoint]
 models={m for m in g['model'] if sources[m] not in ('MISSING','EXTERNAL')}|{compat_check,ord_check,asm_check}
 changed=(set(pl['rebuild'])-set(pl['records']))|{compat,compat_check,ord,ord_check,asm,asm_check};assert len(models)==273 and len(changed)==81
 states={'ha':sha(ha/'state.json'),'model':sha(model/'state.json'),'graph':sha(graph),'plan':sha(plan)}
 assert json.loads((ha/'state.json').read_text())['status']=='PASS' and json.loads((model/'state.json').read_text())['status']=='PASS'
 ha_sources={m:sha(R/sources[m]) for m in g['HA'] if sources[m] not in ('MISSING','EXTERNAL')}
 initial={m:sha(R/sources[m]) for m in models|{endpoint,endpoint_check}}
 if args.resume:
  if initial!=state['source_hashes'] or ha_sources!=state['current_ha_source_hashes'] or states!=state['anchor_hashes']:raise RuntimeError('source graph or provider anchors changed; build a new affected graph')
 else:
  state['source_hashes']=initial;state['current_ha_source_hashes']=ha_sources;state['anchor_hashes']=states
  ha_snap=root/'current-ha-source-snapshots';ha_snap.mkdir(exist_ok=True)
  for m,h in ha_sources.items():
   p=ha_snap/(m.replace('.','_')+'.lean');shutil.copyfile(R/sources[m],p);require(p,h,'current HA source snapshot (not historical-object provenance)')
  source_snap=root/'source-snapshots';source_snap.mkdir(exist_ok=True)
  for m,h in initial.items():
   f=R/sources[m]
   p=source_snap/(m.replace('.','_')+'.lean');shutil.copyfile(f,p);require(p,h,'initial source snapshot')
 state['phase']='historical boundary authentication';save();boundary={}
 # Traverse top-level project namespace symlink directories explicitly. Package
 # Foundation and Mathlib are separately inherited and intentionally excluded.
 for top in (ha/'lib').iterdir():
  if top.name in ('Foundation','Mathlib') or not top.is_dir():continue
  for dirpath,_,files in os.walk(top,followlinks=True):
   for fn in files:
    if fn.endswith('.olean'):
     f=Path(dirpath)/fn;rel=str(f.relative_to(ha/'lib'));boundary[rel]=sha(f)
 if args.resume:
  if boundary!=state['historical_boundary_objects']:raise RuntimeError('historical object boundary changed')
 else:state['historical_boundary_objects']=boundary
 prior={};prior_root=None
 if args.rebase:
  prior_root=args.rebase.resolve();prior_state=json.loads((prior_root/'state.json').read_text());prior_hash=sha(prior_root/'state.json')
  if prior_state['historical_boundary_objects']!=boundary:raise RuntimeError('prior historical boundary differs')
  if prior_state.get('package_audit_state_sha256')!=sha(Path('/tmp/ha87-full-source-jrvxi6bb/state.json')):raise RuntimeError('prior package anchor differs')
  prior={r['module']:r for r in prior_state['records'] if r.get('verified')}
  state['rebase_from']=str(prior_root);state['rebase_state_sha256']=prior_hash
  state['rebase_prior_count']=len(prior);save()
 # The scan plan follows symlink directories; compare all model/HA overlaps.
 for m,row in pl['records'].items():
  rel=Path(m.replace('.','/')+'.olean');require(ha/'lib'/rel,row['historical'],'historic shared object');require(model/'lib'/rel,row['adaptive'],'model shared object')
 model_inherited={}
 for m in models-changed:
  rel=m.replace('.','/')+'.olean'
  if rel not in boundary:model_inherited[m]=sha(model/'lib'/rel)
 if args.resume:
  if model_inherited!=state['model_only_inherited_objects']:raise RuntimeError('model-only inherited boundary changed')
 else:state['model_only_inherited_objects']=model_inherited
 state['phase']='prepare coherent overlay';save();lib=root/'lib';logs=root/'logs';lib.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
 for rel in boundary:
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists() and not dst.is_symlink():dst.symlink_to((ha/'lib'/rel).resolve())
 # Fill model-only project objects, never replace anything in the HA boundary.
 for dirpath,_,files in os.walk(model/'lib',followlinks=True):
  for fn in files:
   if not fn.endswith('.olean'):continue
   f=Path(dirpath)/fn;rel=f.relative_to(model/'lib')
   if rel.parts[0] in ('Foundation','Mathlib'):continue
   dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True)
   if not dst.exists() and not dst.is_symlink():dst.symlink_to(f.resolve())
 if not (lib/'Foundation').exists():(lib/'Foundation').symlink_to((ha/'lib'/'Foundation').resolve(),target_is_directory=True)
 # Remove only the affected adaptive descendants, not historical shared seeds.
 done={r['module'] for r in state['records'] if r.get('verified')}
 for m in changed:
  dst=lib/(m.replace('.','/')+'.olean')
  if m not in done and (dst.exists() or dst.is_symlink()):dst.unlink()
 # Current-source graph topological order; all preserved seed objects remain
 # explicit inherited historical boundary, not source-authenticated.
 seen=set();order=[]
 def visit(m):
  if m in seen:return
  seen.add(m)
  for d in edges.get(m,[]):
   if d in models:visit(d)
  if m in changed:order.append(m)
 visit('DiophantineConsistency.ArithmeticAdaptiveEquivalenceUnconditional2011')
 i=order.index(compat);order.insert(i+1,compat_check)
 i=order.index(ord);order.insert(i+1,ord_check)
 i=order.index(asm);order.insert(i+1,asm_check)
 if len(order)!=81:raise RuntimeError(f'expected 81 affected model/check modules, got {len(order)}')
 order+=['DiophantineConsistency.HAAdaptiveFactor87','DiophantineConsistency.HAAdaptiveFactor87Checks'];state['order']=order;save()
 pkg=Path('/tmp/ha87-full-source-jrvxi6bb/package-lib');pkg_state=Path('/tmp/ha87-full-source-jrvxi6bb/state.json')
 pkg_info=json.loads(pkg_state.read_text());assert pkg_info['status']=='AUDIT_PASS';pkg_anchor=sha(pkg_state)
 env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(pkg),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];state['package_audit_state_sha256']=pkg_anchor;save()
 for rec in state['records']:
  if rec.get('verified'):
   require(lib/(rec['module'].replace('.','/')+'.olean'),rec['object_sha256'],'completed output');require(logs/rec['log_file'],rec['log_sha256'],'completed log')
   for d,h in rec['dependency_hashes'].items():
    rel=d.replace('.','/')+'.olean';q=lib/rel if (lib/rel).is_file() else pkg/rel;require(q,h,'completed direct dependency')
   for p,h in rec['dependency_companions'].items():require(Path(p),h,'completed direct dependency companion')
 for m in order:
  if m in done:continue
  state['phase']='compile';state['module']=m;save();f=R/sources[m];require(f,initial[m],'source before compile')
  deps={};companions={}
  for d in edges[m]:
   rel=d.replace('.','/')+'.olean';q=lib/rel if (lib/rel).is_file() else pkg/rel
   if not q.is_file():raise RuntimeError(f'missing direct dependency {d} for {m}')
   deps[d]=sha(q)
   for z in (Path(str(q)+'.server'),Path(str(q)+'.private'),q.with_suffix('.ir')):
    if z.is_file():companions[str(z)]=sha(z)
  if m in prior:
   prev=prior[m]
   def normalize_companion_paths(items,source_root):
    out={}
    for q,h in items.items():
     p=Path(q)
     try:key='overlay/'+str(p.relative_to(source_root/'lib'))
     except ValueError:key='package/'+str(p.relative_to(pkg))
     out[key]=h
    return out
   if prev['source_sha256']==initial[m] and prev['dependency_hashes']==deps and normalize_companion_paths(prev.get('dependency_companions',{}),prior_root)==normalize_companion_paths(companions,root):
    oldobj=prior_root/'lib'/(m.replace('.','/')+'.olean');oldlog=prior_root/'logs'/prev['log_file'];oldsnap=prior_root/'logs'/prev['source_snapshot']
    require(oldobj,prev['object_sha256'],'rebase prefix object');require(oldlog,prev['log_sha256'],'rebase prefix log');require(oldsnap,prev['source_sha256'],'rebase prefix source')
    obj=lib/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    if obj.exists() or obj.is_symlink():obj.unlink()
    obj.symlink_to(oldobj.resolve());log=logs/(m.replace('.','_')+'-reused.log');snap=logs/(m.replace('.','_')+'-reused.lean');shutil.copyfile(oldlog,log);shutil.copyfile(oldsnap,snap)
    row={'module':m,'exit':0,'source_sha256':initial[m],'object_sha256':sha(obj),'log_sha256':sha(log),'log_file':log.name,'source_snapshot':snap.name,'dependency_hashes':deps,'dependency_companions':companions,'verified':True,'reused_from':str(prior_root)}
    state['records'].append(row);save();print(m,'REUSED',flush=True);continue
  attempt=1+sum(r['module']==m for r in state['records']);snap=logs/(m.replace('.','_')+f'-attempt-{attempt}.lean');shutil.copyfile(f,snap);obj=lib/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=logs/(m.replace('.','_')+f'-attempt-{attempt}.log');cmd=['lean','-M8000','-j1','-DElab.async=false',str(f),'-o',str(obj)];t=time.monotonic();r=subprocess.run(cmd,cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(r.stdout);row={'module':m,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.is_file() else None,'log_sha256':sha(log),'log_file':log.name,'source_snapshot':snap.name,'command':cmd,'dependency_hashes':deps,'dependency_companions':companions,'verified':False};state['records'].append(row);save()
  if r.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',r.stdout):raise RuntimeError(f'compile failed or forbidden diagnostic in {m}: {r.stdout}')
  require(snap,initial[m],'source snapshot');require(f,initial[m],'source after compile')
  for d,h in deps.items():
   rel=d.replace('.','/')+'.olean';q=lib/rel if (lib/rel).is_file() else pkg/rel;require(q,h,'direct dependency after compile')
  for p,h in companions.items():require(Path(p),h,'direct dependency companion after compile')
  row['verified']=True;save();print(m,'PASS',round(row['seconds'],1),flush=True)
 state['phase']='final authentication';save()
 for m,h in initial.items():
  f=R/sources[m];require(f,h,'final source')
 for m,h in ha_sources.items():
  require(R/sources[m],h,'final current HA source snapshot');require(root/'current-ha-source-snapshots'/(m.replace('.','_')+'.lean'),h,'saved HA source snapshot')
 for m,h in initial.items():require(root/'source-snapshots'/(m.replace('.','_')+'.lean'),h,'saved model source snapshot')
 for rel,h in boundary.items():
  require(ha/'lib'/rel,h,'final historical object');require(lib/rel,h,'final overlay historical object')
 for m,h in model_inherited.items():
  rel=m.replace('.','/')+'.olean';require(model/'lib'/rel,h,'final model-only parent object');require(lib/rel,h,'final overlay model-only object')
 for rec in state['records']:
  if rec.get('verified'):
   require(lib/(rec['module'].replace('.','/')+'.olean'),rec['object_sha256'],'final rebuilt output');require(logs/rec['log_file'],rec['log_sha256'],'final compiler log')
   for d,h in rec['dependency_hashes'].items():
    rel=d.replace('.','/')+'.olean';q=lib/rel if (lib/rel).is_file() else pkg/rel;require(q,h,'final direct dependency')
   for p,h in rec['dependency_companions'].items():require(Path(p),h,'final dependency companion')
 for m,row in pl['records'].items():require(model/'lib'/(m.replace('.','/')+'.olean'),row['adaptive'],'final model shared object')
 for k,f in [('ha',ha/'state.json'),('model',model/'state.json'),('graph',graph),('plan',plan)]:require(f,states[k],'final anchor')
 if state.get('rebase_from'):
  require(Path(state['rebase_from'])/'state.json',state['rebase_state_sha256'],'prior prefix state')
  for rec in state['records']:
   if rec.get('reused_from'):
    old=Path(rec['reused_from']);require(old/'lib'/(rec['module'].replace('.','/')+'.olean'),rec['object_sha256'],'final prior prefix object')
 require(pkg_state,pkg_anchor,'package audit state')
 for n,h in pkg_info['graph']['external_hashes'].items():require(pkg/(n.replace('.','/')+'.olean'),h,'direct package object')
 for rel,row in pkg_info['graph']['external_companions'].items():require(pkg/rel,row['sha256'],'direct package companion')
 state.update(status='PASS',phase='complete',module=None);save();print('PASS',root,flush=True)
except BaseException as exc:
 state.update(status='FAILED',failure={'type':type(exc).__name__,'message':str(exc),'phase':state.get('phase'),'module':state.get('module')});save();print('FAILED',root,state['failure'],flush=True);raise
