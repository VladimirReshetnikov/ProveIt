#!/usr/bin/env python3
"""Replay the fixed-port client over two matched, guarded historical parents."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
SRC=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
base=Path('/tmp/gap85-seeded-two-step-replay-t53rzmpf')
other=Path('/tmp/gap85-current-indices-replay-2tuxudlt')
parents=[base,other]
states=[json.loads((p/'state.json').read_text()) for p in parents]
assert all(s['status']=='PASS' for s in states) and states[0]['boundary']==states[1]['boundary']
boundary=[Path(p) for p in states[0]['boundary']]
name='AdaptiveGap85CurrentSeededTwoStep'
checks=name+'Checks'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=SRC/(name+'.lean')
objects=[sorted(p for p in (parent/'lib/DiophantineConsistency').glob('*.olean*') if p.is_file()) for parent in parents]
byname=[{p.name:p for p in group} for group in objects]
common=sorted(byname[0].keys() & byname[1].keys())
assert common and all(sha(byname[0][n])==sha(byname[1][n]) for n in common)
parent_inputs=[]
for parent,state,mod in zip(parents,states,['AdaptiveGap85SeededTwoStep','AdaptiveGap85CurrentIndices']):
 obj=parent/'lib/DiophantineConsistency'/(mod+'.olean');src=parent/'src/DiophantineConsistency'/(mod+'.lean')
 row=next(r for r in state['records'] if r['module']==mod)
 assert sha(obj)==row['object_sha256'] and sha(src)==row['source_sha256']
 parent_inputs.extend([parent/'state.json',obj,src])
external=base/'lib/Foundation/FirstOrder/Arithmetic/HFS/PRF.olean'
files=[Path(__file__).resolve(),LEAN,source,external,*parent_inputs,*objects[0],*objects[1]]
anchors={str(p):sha(p) for p in files}
# Record both presence and absence for every project-module companion, and
# for every candidate direct import in the actual search roots.
stems=sorted({n.split('.olean')[0] for n in byname[0].keys() | byname[1].keys()})
watched=[]
for parent in parents:
 for stem in stems:
  for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
   watched.append(parent/'lib/DiophantineConsistency'/(stem+suffix))
for root in [*(p/'lib' for p in parents),*boundary]:
 for mod in ['Init','DiophantineConsistency/AdaptiveGap85SeededTwoStep','DiophantineConsistency/AdaptiveGap85CurrentIndices']:
  for suffix in ['.olean','.olean.private','.olean.server','.ilean']:
   watched.append(root/(mod+suffix))
def inventory():
 out={}
 for p in watched:
  exists=p.is_file()
  out[str(p)]={'exists':exists,'realpath':str(p.resolve()) if exists else None,'sha256':sha(p) if exists else None}
 return out
initial_inventory=inventory()
inventory_hash=hashlib.sha256(json.dumps(initial_inventory,sort_keys=True).encode()).hexdigest()
w=Path(tempfile.mkdtemp(prefix='gap85-current-seeded-two-step-replay-'));src=w/'src';lib=w/'lib';logs=w/'logs'
for p in [src/'DiophantineConsistency',lib/'DiophantineConsistency',logs]:p.mkdir(parents=True,exist_ok=True)
for p in (base/'lib').iterdir():
 if p.name!='DiophantineConsistency':(lib/p.name).symlink_to(p,target_is_directory=p.is_dir())
for parent in parents:
 for p in (parent/'lib/DiophantineConsistency').iterdir():
  dest=lib/'DiophantineConsistency'/p.name
  if not dest.exists() and not dest.is_symlink() and not p.name.startswith(name+'.'):
   dest.symlink_to(p,target_is_directory=p.is_dir())
def overlay_inventory():
 out={}
 for p in sorted((lib/'DiophantineConsistency').iterdir()):
  if p.name.startswith(name+'.') or p.name.startswith(checks+'.'):continue
  out[p.name]={'symlink':p.is_symlink(),'link':os.readlink(p) if p.is_symlink() else None,
               'realpath':str(p.resolve()),'file':p.is_file()}
 return out
initial_overlay=overlay_inventory()
overlay_hash=hashlib.sha256(json.dumps(initial_overlay,sort_keys=True).encode()).hexdigest()
shutil.copyfile(source,src/'DiophantineConsistency'/(name+'.lean'))
checkbytes=('import DiophantineConsistency.'+name+'\n#print axioms DiophantineConsistency.AdaptiveGap85CurrentSeededTwoStep.current_seeded_gap_zero_two_step\n#check DiophantineConsistency.AdaptiveGap85CurrentSeededTwoStep.current_seeded_gap_zero_two_step\n').encode()
(src/'DiophantineConsistency'/(checks+'.lean')).write_bytes(checkbytes)
checkhash=hashlib.sha256(checkbytes).hexdigest()
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
s={'status':'RUNNING','root':str(w),'provider':str(base)+' + '+str(other),'parent_project_object_count':sum(map(len,objects)),
   'common_project_objects':len(common),'anchors':anchors,'boundary':list(map(str,boundary)),
   'inventory_sha256':inventory_hash,'inventory_paths':len(watched),'overlay_sha256':overlay_hash,'overlay_entries':len(initial_overlay),'checks_sha256':checkhash,
   'records':[],'dependency_rows':[],
   'scope':'In every IΣ₁ model the actual fixed-port full zero and Pell-coordinate equation imply the R≥5 bound required by the conditional seeded two-step construction. The actual-to-seed scaling and two auxiliary seed equations remain explicit assumptions; no zero existence or unconditional reverse implication is asserted. Both parent object sets, overlap hashes and direct candidates are guarded; inherited project/package transitive source ancestry remains historical.'}
def save():(w/'state.json').write_text(json.dumps(s,indent=2)+'\n')
def audit():
 for p,h in anchors.items():
  if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('guard changed: '+p)
 if inventory()!=initial_inventory:raise RuntimeError('parent/direct-candidate inventory changed')
 if overlay_inventory()!=initial_overlay:raise RuntimeError('overlay inventory changed')
 if sha(src/'DiophantineConsistency'/(name+'.lean'))!=anchors[str(source)]:raise RuntimeError('source snapshot changed')
 if sha(src/'DiophantineConsistency'/(checks+'.lean'))!=checkhash:raise RuntimeError('checks snapshot changed')
def deps(mod,phase):
 f=src/'DiophantineConsistency'/(mod+'.lean')
 r=subprocess.run([str(LEAN),'--deps',str(f)],cwd=R,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 if r.returncode:raise RuntimeError('deps failed '+mod+' '+r.stdout)
 paths=[Path(x) for x in r.stdout.splitlines() if x]
 expected=([lib/'DiophantineConsistency/AdaptiveGap85SeededTwoStep.olean',lib/'DiophantineConsistency/AdaptiveGap85CurrentIndices.olean']
           if mod==name else [lib/'DiophantineConsistency'/(name+'.olean')])
 if not all(p in paths for p in expected):raise RuntimeError('unexpected direct dependency resolution '+r.stdout)
 normalized=r.stdout.replace(str(w),'${RUN_ROOT}')
 (logs/(mod+'.'+phase+'.deps')).write_text(normalized)
 return hashlib.sha256(normalized.encode()).hexdigest()
save();print('ROOT',w,'PARENT_OBJECTS',sum(map(len,objects)),'COMMON',len(common),'INVENTORY',len(watched),flush=True)
try:
 audit();d0=deps(name,'before')
 for mod in [name,checks]:
  f=src/'DiophantineConsistency'/(mod+'.lean');o=lib/'DiophantineConsistency'/(mod+'.olean');l=logs/(mod+'.log')
  if mod==checks:d2=deps(checks,'before')
  with l.open('w') as out:r=subprocess.run([str(LEAN),'-M6000','-j1','-DElab.async=false','--root='+str(src),str(f),'-o',str(o)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  content=l.read_text();s['records'].append({'module':mod,'exit':r.returncode,'source_sha256':sha(f),'object_sha256':sha(o) if o.exists() else None,'log_sha256':sha(l),'warnings':content.count('warning:')});save()
  if r.returncode or 'sorryAx' in content or 'error:' in content or 'warning:' in content:raise RuntimeError('compile failed '+mod+': '+content)
  if mod==checks:
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',content,re.S)
   if len(axioms)!=1 or any({a.strip() for a in x.split(',') if a.strip()}-{'propext','Classical.choice','Quot.sound'} for x in axioms):raise RuntimeError('unexpected axiom report')
 d1=deps(name,'after');d3=deps(checks,'after')
 if d0!=d1 or d2!=d3:raise RuntimeError('direct dependencies changed')
 s['dependency_rows']=[{'module':name,'normalized_sha256':d0},{'module':checks,'normalized_sha256':d2}]
 audit()
 for row in s['records']:
  if sha(lib/'DiophantineConsistency'/(row['module']+'.olean'))!=row['object_sha256'] or sha(logs/(row['module']+'.log'))!=row['log_sha256']:raise RuntimeError('output changed')
 s['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save();print('FAILED',str(e),flush=True);raise
