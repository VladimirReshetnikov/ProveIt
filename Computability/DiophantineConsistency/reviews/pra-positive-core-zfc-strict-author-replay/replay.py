#!/usr/bin/env python3
"""Build positive ZFC sigma core from fixed sources over the strict peer."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parents[4];PACKET=Path(__file__).resolve().parent
M=json.loads((PACKET/'manifest.json').read_text());PARENT=Path(M['parent']);PL=PARENT/'lib'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
work=Path(tempfile.mkdtemp(prefix='pra-positive-core-zfc-strict-'));src=work/'src';lib=work/'lib';logs=work/'logs';logs.mkdir();(src/'DiophantineConsistency').mkdir(parents=True);(lib/'DiophantineConsistency').mkdir(parents=True);(lib/'ZFCinPA').mkdir()
for n in M['order']:shutil.copyfile(PACKET/'frozen'/(n+'.lean'),src/'DiophantineConsistency'/(n+'.lean'))
for rel in M['parent_objects']:
 dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to((PL/rel).resolve())
(lib/'Foundation').symlink_to((PL/'Foundation').resolve(),target_is_directory=True)
base=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=ROOT,text=True).strip().split(':');base=[x for x in base if not x.startswith(str(ROOT/'.lake/build/lib/lean'))]
env=dict(os.environ,LEAN_PATH=str(lib)+':'+':'.join(base),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state={'status':'RUNNING','root':str(work),'manifest_sha256':sha(PACKET/'manifest.json'),'parent':str(PARENT),'records':[],'scope':M['scope']}
def save():
 (work/'state.tmp').write_text(json.dumps(state,indent=2)+'\n');(work/'state.tmp').replace(work/'state.json')
def require(p,h,why):
 if not p.is_file() or sha(p)!=h:raise RuntimeError(why+': '+str(p))
def audit():
 require(PACKET/'manifest.json',state['manifest_sha256'],'manifest')
 for p,h in M['parent_states'].items():require(Path(p),h,'parent state')
 for n,h in M['source_sha256'].items():
  require(src/'DiophantineConsistency'/(n+'.lean'),h,'frozen source');require(PACKET/'frozen'/(n+'.lean'),h,'packet source');require(ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(n+'.lean'),h,'workspace suffix source')
 for rel,h in M['observed_parent_sources'].items():require(ROOT/rel,h,'workspace parent source')
 for rel,h in M['parent_objects'].items():require(lib/rel,h,'parent object')
 for rel,h in M['external_anchors'].items():require(lib/rel,h,'external anchor')
 require(Path(M['lean_path']),M['lean_sha256'],'lean compiler')
save();print('ROOT',work,'project and ZFC parent objects',len(M['parent_objects']),'suffix',len(M['order']),flush=True)
try:
 audit()
 for n in M['order']:
  state['module']=n;save();f=src/'DiophantineConsistency'/(n+'.lean');obj=lib/'DiophantineConsistency'/(n+'.olean');log=logs/(n+'.log');deps={}
  for line in f.read_text().splitlines():
   if line.startswith('import DiophantineConsistency.') or line.startswith('import ZFCinPA.'):
    for name in line.split()[1:]:
     p=lib/(name.replace('.','/')+'.olean')
     if not p.is_file():raise RuntimeError('missing declared project import '+name)
     deps[name]=sha(p)
  t=time.monotonic()
  with log.open('w') as out:r=subprocess.run([M['lean_path'],'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(obj)],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
  row={'module':n,'exit':r.returncode,'seconds':time.monotonic()-t,'source_sha256':sha(f),'object_sha256':sha(obj) if obj.exists() else None,'log_sha256':sha(log),'dependency_hashes':deps};state['records'].append(row);save()
  text=log.read_text()
  if r.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',text):raise RuntimeError('compile failed or diagnostic in '+n+':\n'+text)
  for name,h in deps.items():require(lib/(name.replace('.','/')+'.olean'),h,'dependency after compile')
  if n.endswith('Checks'):
   groups=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S)
   if len(groups)!=2 or any({x.strip() for x in g.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for g in groups):raise RuntimeError('unexpected axiom checks')
  print('PASS',n,flush=True)
 state['phase']='final authentication';save();audit()
 for row in state['records']:
  require(lib/'DiophantineConsistency'/(row['module']+'.olean'),row['object_sha256'],'output');require(logs/(row['module']+'.log'),row['log_sha256'],'log')
  for name,h in row['dependency_hashes'].items():require(lib/(name.replace('.','/')+'.olean'),h,'final dependency')
 state.update(status='PASS',phase='complete',module=None);save();print('PASS',work,flush=True)
except BaseException as e:
 state.update(status='FAILED',failure={'type':type(e).__name__,'message':str(e),'phase':state.get('phase'),'module':state.get('module')});save();print('FAILED',state['failure'],flush=True);raise
