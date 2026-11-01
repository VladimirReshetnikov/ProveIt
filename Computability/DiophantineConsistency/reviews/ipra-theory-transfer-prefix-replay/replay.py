#!/usr/bin/env python3
"""Check conditional iPRA transfer against a verified fixed-source prefix."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time,tomllib
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent;M=json.loads((PACKET/'manifest.json').read_text());P=Path(M['parent']);TREE=Path(M['source_tree']);pkg=P/'package-lib';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();work=Path(tempfile.mkdtemp(prefix='ipra-theory-transfer-prefix-'));src=work/'src';lib=work/'lib';logs=work/'logs';logs.mkdir();(src/'DiophantineConsistency').mkdir(parents=True);lib.mkdir()
state={'status':'RUNNING','phase':'initialization','root':str(work),'parent':str(P),'manifest_sha256':sha(PACKET/'manifest.json'),'records':[],'scope':M['scope']}
def save():
 q=work/'state.tmp';q.write_text(json.dumps(state,indent=2)+'\n');q.replace(work/'state.json')
def need(p,h,why):
 if not p.is_file() or sha(p)!=h:raise RuntimeError(why+': '+str(p))
save();print('ROOT',work,flush=True)
try:
 need(PACKET/'parent-prefix-state.json',M['prefix_state_sha256'],'prefix state');snap=json.loads((PACKET/'parent-prefix-state.json').read_text());assert all(M['project_records'][n] in snap['records'] for n in M['project_closure'])
 for n in M['suffix_order']:shutil.copyfile(PACKET/'frozen'/(n+'.lean'),src/'DiophantineConsistency'/(n+'.lean'))
 for n in M['project_closure']:
  a=P/'lib'/(n.replace('.','/')+'.olean');b=lib/(n.replace('.','/')+'.olean');b.parent.mkdir(parents=True,exist_ok=True);b.symlink_to(a.resolve())
 names={x['name'] for x in tomllib.loads((TREE/'lakefile.toml').read_text())['lean_lib']};leaked=[x for x in names if x!='Foundation' and (pkg/x).exists()]
 if leaked:raise RuntimeError('project namespace in package mirror: '+str(leaked))
 lean=Path(subprocess.check_output(['lake','env','which','lean'],cwd=ROOT,text=True).strip()).resolve();env=dict(os.environ,LEAN_PATH=str(lib)+':'+str(pkg),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 def audit():
  need(PACKET/'manifest.json',state['manifest_sha256'],'manifest');need(PACKET/'parent-prefix-state.json',M['prefix_state_sha256'],'prefix state');need(TREE/'lakefile.toml',M['lakefile_sha256'],'frozen lakefile');need(lean,M['compiler_sha256'],'Lean binary')
  for n in M['project_closure']:
   r=M['project_records'][n];source=M['project_sources'][n];need(TREE/source['path'],source['sha256'],'project source');need(P/'source-snapshots'/(n.replace('.','_')+'.lean'),source['sha256'],'parent source snapshot');need(P/'lib'/(n.replace('.','/')+'.olean'),r['object_sha256'],'parent output');need(lib/(n.replace('.','/')+'.olean'),r['object_sha256'],'linked parent output');need(P/'logs'/r['log_file'],r['log_sha256'],'parent log')
   if r.get('reused_from'):
    need(P/'transitive-manifests'/r['transitive_manifest'],r['transitive_manifest_sha256'],'reuse manifest');need(Path(r['original_compile_root'])/'state.json',r['original_compile_state_sha256'],'origin state')
   for dep,h in r['dependency_hashes'].items():
    q=(lib if dep in M['project_records'] else pkg)/(dep.replace('.','/')+'.olean');need(q,h,'parent declared dependency')
  for n,row in M['external_objects'].items():need(Path(row['path']),row['sha256'],'external object');need(pkg/(n.replace('.','/')+'.olean'),row['sha256'],'mirrored external object')
  for rel,row in M['external_companions'].items():need(Path(row['path']),row['sha256'],'external companion');need(pkg/rel,row['sha256'],'mirrored companion')
  for n,h in M['suffix_sources'].items():need(PACKET/'frozen'/(n+'.lean'),h,'frozen suffix source');need(src/'DiophantineConsistency'/(n+'.lean'),h,'build suffix source')
 state['phase']='parent authentication';save();audit();allowed=set(M['project_closure'])|{'DiophantineConsistency.'+n for n in M['suffix_order']}
 for n in M['suffix_order']:
  state.update(phase='compile',module=n);save();f=src/'DiophantineConsistency'/(n+'.lean');obj=lib/'DiophantineConsistency'/(n+'.olean');log=logs/(n+'.log');deps={}
  for line in f.read_text().splitlines():
   hit=re.match(r'^\s*(?:public\s+)?import\s+(.+)',line)
   if not hit:continue
   for dep in hit.group(1).split():
    if dep in allowed:q=lib/(dep.replace('.','/')+'.olean')
    elif dep in M['external_objects']:q=pkg/(dep.replace('.','/')+'.olean')
    else:raise RuntimeError('unaccounted import '+dep)
    if not q.is_file():raise RuntimeError('missing import '+dep)
    deps[dep]=sha(q)
  t=time.monotonic()
  with log.open('w') as out:r=subprocess.run([str(lean),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(obj)],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
  text=log.read_text();row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'dependency_hashes':deps};state['records'].append(row);save()
  if r.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',text):raise RuntimeError('compile failed or diagnostic in '+n+':\n'+text)
  for dep,h in deps.items():need((lib if dep in allowed else pkg)/(dep.replace('.','/')+'.olean'),h,'direct import after compile')
  if n.endswith('Checks'):
   groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
   if len(groups)!=2 or any({x.strip() for x in g.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for g in groups):raise RuntimeError('unexpected axiom checks')
  print('PASS',n,flush=True)
 state.update(phase='final authentication',module=None);save();audit()
 for row in state['records']:
  n=row['module'];need(lib/'DiophantineConsistency'/(n+'.olean'),row['object_sha256'],'suffix output');need(logs/(n+'.log'),row['log_sha256'],'suffix log')
 state.update(status='PASS',phase='complete');save();print('PASS',work,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure={'type':type(e).__name__,'message':str(e),'phase':state.get('phase'),'module':state.get('module')});save();print('FAILED',state['failure'],flush=True);raise
