"""Provisional exact 86 HA client over the focused 87 HA author provider.

The 87 provider and Foundation/Mathlib/ZF/package provenance remain explicitly
historical. Project objects, selected source guards and all new sources are
rechecked before and after; no full-source closure is asserted.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');SRC=R/'Computability/DiophantineConsistency/Lean';P=Path(os.environ.get('HA86_PARENT','/tmp/ha87-focused-validator-rebase-8o6bp_pm'));PACKAGE=Path('/tmp/ha87-full-source-jrvxi6bb');G=Path('/tmp/ha-focused-unbounded-current-source-graph.json');HA=Path('/tmp/ha-expression-assembly-vgttkwsl');MODEL=Path('/tmp/adaptive-unconditional-equivalence-ptaobui4');PLAN=Path('/tmp/ha-preserved-model-rebuild-plan.json');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());ps=read(P/'state.json');assert ps['status']=='PASS';ph=sha(P/'state.json');gh=sha(G);packageh=sha(PACKAGE/'state.json');assert packageh==ps['package_audit_state_sha256'];g=read(G);anchors={'ha':sha(HA/'state.json'),'model':sha(MODEL/'state.json'),'graph':gh,'plan':sha(PLAN)};assert anchors==ps['anchor_hashes'];gs=dict(g['sources']);sources={}
for n,h in {**ps['source_hashes'],**ps['current_ha_source_hashes']}.items():
 raw=gs.get(n)
 if not raw:raw='Computability/DiophantineConsistency/Lean/'+n.replace('.','/')+'.lean'
 p=R/raw;assert p.is_file() and sha(p)==h,n;sources[str(p)]=h
seen=set();build=[];boundary=[]
def visit(n):
 if n in seen:return
 seen.add(n);obj=P/'lib'/('/'.join(n.split('.'))+'.olean')
 if obj.is_file():boundary.append(n);return
 p=SRC/('/'.join(n.split('.'))+'.lean')
 if not p.is_file():boundary.append(n);return
 for line in p.read_text().splitlines():
  if line.startswith('import '):
   for x in line[7:].split():visit(x)
 build.append(n)
visit('DiophantineConsistency.HAAdaptiveDirectOrdinate86Checks');assert len(build)==27 and build[-1]=='DiophantineConsistency.HAAdaptiveDirectOrdinate86Checks';snap={n:sha(SRC/('/'.join(n.split('.'))+'.lean')) for n in build}
# Follow project namespace symlinks. Foundation and package trees remain a
# separately pinned inherited boundary, as in the focused 87 receipt.
providers={}
for top in (P/'lib').iterdir():
 if top.name in ('Foundation','Mathlib') or not top.is_dir():continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   if f.endswith('.olean'):
    p=Path(root)/f;providers[str(p.relative_to(P/'lib'))]={'path':str(p.resolve()),'sha256':sha(p)}
assert len(providers)>=1300
for n in boundary:
 key=n.replace('.','/')+'.olean'
 if n.startswith('DiophantineConsistency.'):assert key in providers,n
w=Path(tempfile.mkdtemp(prefix='ha86-focused-extension-'));(w/'logs').mkdir();lib=w/'lib';shutil.copyfile(__file__,w/'driver.py');(w/'providers.json').write_text(json.dumps(providers,indent=2,sort_keys=True)+'\n');prh=sha(w/'providers.json')
for n in build:shutil.copyfile(SRC/('/'.join(n.split('.'))+'.lean'),w/'logs'/(n.split('.')[-1]+'.lean'))
for rel,item in providers.items():
 dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(item['path'])
for name in ['Foundation','Mathlib']:
 p=P/'lib'/name
 if p.is_dir():(lib/name).symlink_to(p.resolve(),target_is_directory=True)
state={'status':'RUNNING','private':str(w),'ha87_author_state_sha256':ph,'graph_sha256':gh,'package_state_sha256':packageh,'anchor_hashes':anchors,'project_provider_inventory_sha256':prh,'project_provider_count':len(providers),'inherited_source_guard_count':len(sources),'build_order':build,'direct_boundaries':boundary,'source_sha256':snap,'records':[],'scope':'Provisional 27-module direct current-source 86 HA extension over focused 87 HA author provider; source/selected-object checks retained; 87 parent chosen by HA86_PARENT; acceptance depends on that parent’s independent replay and inherited historical HA/ZF/Foundation/Mathlib/package ancestry is not fully source-current authenticated.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
def auth():
 return (sha(P/'state.json')==ph and sha(G)==gh and sha(PACKAGE/'state.json')==packageh and sha(HA/'state.json')==anchors['ha'] and sha(MODEL/'state.json')==anchors['model'] and sha(PLAN)==anchors['plan'] and sha(w/'providers.json')==prh and all(sha(p)==h for p,h in sources.items()) and all(sha(SRC/('/'.join(n.split('.'))+'.lean'))==h for n,h in snap.items()) and all(sha(x['path'])==x['sha256'] for x in providers.values()) and all(sha(P/'lib'/(r['module'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(P/'logs'/r['log_file'])==r['log_sha256'] for r in ps['records'] if r.get('verified')))
save();print('PRIVATE',w,'MODULES',len(build),'PROVIDERS',len(providers),'SOURCE_GUARDS',len(sources),flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),str(PACKAGE/'package-lib')]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in build:
  short=n.split('.')[-1];src=SRC/('/'.join(n.split('.'))+'.lean');out=lib/('/'.join(n.split('.'))+'.olean');log=w/'logs'/(short+'.log');tim=w/'logs'/(short+'.time');assert not out.exists() and sha(src)==snap[n];cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M8000','-j1','-DElab.async=false','-o',str(out),str(src)];print('START',short,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tim),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  row={'name':n,'exit':code,'seconds':time.monotonic()-start,'source_sha256':sha(src),'log_sha256':sha(log),'time_sha256':sha(tim),'command':cmd}
  if out.exists():row['object_sha256']=sha(out)
  state['records'].append(row);save();print('DONE',short,code,flush=True)
  if code:raise RuntimeError(n)
 assert auth() and all(sha(w/'logs'/(r['name'].split('.')[-1]+'.lean'))==r['source_sha256'] and sha(lib/('/'.join(r['name'].split('.'))+'.olean'))==r['object_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] and sha(w/'logs'/(r['name'].split('.')[-1]+'.time'))==r['time_sha256'] for r in state['records']);state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
