from pathlib import Path
import argparse,hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';parent=Path('/tmp/ha87-focused-post-zfc-merge-eumjnth_');ha=Path('/tmp/ha-expression-assembly-vgttkwsl');graph=Path(__file__).resolve().parent/'source-graph.json'
NAMES=['ArithmeticHalfBinomialCompat','ArithmeticHalfBinomialCompatChecks','ArithmeticAdaptivePopulation2011']
p=argparse.ArgumentParser();p.add_argument('--expected',type=Path);a=p.parse_args();sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest();out=Path(tempfile.mkdtemp(prefix='ha87-halfcompat-'));state={'status':'RUNNING','phase':'initialization','root':str(out),'parent':str(parent),'records':[],'qualification':'Focused additive compatibility repair on the failed author prefix. The 32-prefix outputs and 1136 historical project objects are hash-guarded; historical HA source/object provenance, package internals and the prior prefix independent replay are not established. This does not prove the 87 HA endpoint.'}
def save():
 q=out/'state.json.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(out/'state.json')
def require(f,h,msg):
 if not f.is_file() or sha(f)!=h:raise RuntimeError(f'{msg} changed or missing: {f}')
print('ROOT',out,flush=True);save()
try:
 ps=json.loads((parent/'state.json').read_text());assert ps['status']=='FAILED' and len(ps['records'])==33 and sum(x['exit']==0 for x in ps['records'])==32
 anchor=sha(parent/'state.json');g=json.loads(graph.read_text());gh=sha(graph);sources=g['sources'];ha_sources={m:sha(ROOT/sources[m]) for m in g['HA'] if sources[m] not in ('EXTERNAL','MISSING')};model_sources={m:sha(ROOT/sources[m]) for m in g['model'] if sources[m] not in ('EXTERNAL','MISSING')};initial={n:sha(SRC/(n+'.lean')) for n in NAMES};state.update(parent_state_sha256=anchor,graph_sha256=gh,current_ha_sources=ha_sources,current_model_sources=model_sources,input_sources=initial);save()
 expected=json.loads(a.expected.read_text()) if a.expected else None
 if expected and (initial!=expected['input_sources'] or ha_sources!=expected['current_ha_sources'] or model_sources!=expected['current_model_sources']):raise RuntimeError('current source snapshots differ from author')
 def auth():
  require(parent/'state.json',anchor,'failed-prefix state');require(graph,gh,'post-merge graph')
  for rel,h in ps['historical_boundary_objects'].items():require(ha/'lib'/rel,h,'historical object');require(parent/'lib'/rel,h,'prior overlay historical object')
  for m,h in ps['model_only_inherited_objects'].items():require(parent/'lib'/(m.replace('.','/')+'.olean'),h,'prior model-only object')
  for row in ps['records']:
   if row['exit']!=0:continue
   m=row['module'];require(ROOT/sources[m],row['source_sha256'],'current prior-prefix source');require(parent/'source-snapshots'/(m.replace('.','_')+'.lean'),row['source_sha256'],'prior prefix source snapshot');require(parent/'lib'/(m.replace('.','/')+'.olean'),row['object_sha256'],'prior prefix object');require(parent/'logs'/row['log_file'],row['log_sha256'],'prior prefix log')
  for m,h in ha_sources.items():require(ROOT/sources[m],h,'current HA source')
  for m,h in model_sources.items():require(ROOT/sources[m],h,'current adaptive source')
  for n,h in initial.items():require(SRC/(n+'.lean'),h,'repair source')
 state['phase']='authenticate inputs';save();auth()
 lib=out/'lib';logs=out/'logs';lib.mkdir();logs.mkdir()
 for top in (parent/'lib').iterdir():
  if top.name=='Foundation':(lib/'Foundation').symlink_to(top.resolve(),target_is_directory=True);continue
  if not top.is_dir():continue
  for dp,_,files in os.walk(top,followlinks=True):
   for fn in files:
    if not fn.endswith('.olean'):continue
    f=Path(dp)/fn;rel=f.relative_to(parent/'lib');dest=lib/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(f.resolve())
 for n in NAMES:
  q=lib/'DiophantineConsistency'/(n+'.olean')
  if q.exists() or q.is_symlink():q.unlink()
 path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip();env=dict(os.environ,LEAN_PATH=str(lib)+':'+path,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);state['LEAN_PATH']=env['LEAN_PATH'];save()
 for n in NAMES:
  state['phase']='compile';state['module']=n;save();src=SRC/(n+'.lean');snap=logs/(n+'.lean');shutil.copyfile(src,snap);obj=lib/'DiophantineConsistency'/(n+'.olean');log=logs/(n+'.log');cmd=['lean','-M8000','-j1','-DElab.async=false',str(src),'-o',str(obj)];t=time.monotonic();r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);log.write_text(r.stdout);row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'command':cmd};state['records'].append(row);save()
  if r.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',r.stdout):raise RuntimeError(f'{n} failed: {r.stdout}')
  require(snap,initial[n],'source snapshot');require(src,initial[n],'source after compilation')
  if expected:
   exp=next(x for x in expected['records'] if x['module']==n)
   for k in ['source_sha256','object_sha256','log_sha256']:
    if row[k]!=exp[k]:raise RuntimeError(f'{n} {k} differs from author')
  print(n,'PASS',flush=True)
 state['phase']='final authentication';save();auth();state.update(status='PASS',phase='complete',module=None);save();print('PASS',out,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure={'type':type(e).__name__,'message':str(e),'phase':state.get('phase'),'module':state.get('module')});save();print('FAILED',out,state['failure'],flush=True);raise
