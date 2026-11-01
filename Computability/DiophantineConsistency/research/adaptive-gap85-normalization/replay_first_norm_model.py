#!/usr/bin/env python3
"""Replay fixed-port first-factor completion; historical transitive ancestry inherited."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/research/adaptive-gap85-normalization';P=Path('/tmp/gap85-balance-model-replay-tl0z09ru');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
name='AdaptiveGap85FirstNormModel';checks=name+'Checks';source=S/(name+'.lean');state=json.loads((P/'state.json').read_text());assert state['status']=='PASS';boundary=list(map(Path,state['boundary']));H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
objects=sorted(p for p in (P/'lib/DiophantineConsistency').glob('*.olean*') if p.is_file());anchors={str(p):H(p) for p in [Path(__file__).resolve(),LEAN,P/'state.json',source,*objects]}
checkbytes=('import DiophantineConsistency.'+name+'\n'+''.join('#print axioms DiophantineConsistency.'+name+'.'+n+'\n' for n in ('carrier_algebra','first_factor_unit','completion_first_factor','positive_completion','current_completion'))).encode();ch=hashlib.sha256(checkbytes).hexdigest()
w=Path(tempfile.mkdtemp(prefix='gap85-first-norm-model-'));lib=w/'lib';src=w/'src/DiophantineConsistency';logs=w/'logs';lib.mkdir();src.mkdir(parents=True);logs.mkdir()
for p in (P/'lib').iterdir():
 if p.name!='DiophantineConsistency':(lib/p.name).symlink_to(p,target_is_directory=p.is_dir())
(lib/'DiophantineConsistency').mkdir()
for p in (P/'lib/DiophantineConsistency').iterdir():
 if not p.name.startswith(name+'.') and not p.name.startswith(checks+'.'):(lib/'DiophantineConsistency'/p.name).symlink_to(p,target_is_directory=p.is_dir())
shutil.copyfile(source,src/(name+'.lean'));(src/(checks+'.lean')).write_bytes(checkbytes)
env=dict(os.environ,LEAN_PATH=':'.join(map(str,[lib,*boundary])),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');imports=['Init','DiophantineConsistency/AdaptiveGap85FirstDivisibility','DiophantineConsistency/AdaptiveDirectOrdinate86FixedForward','DiophantineConsistency/ArithmeticAdaptiveConstructionFactorLemmas2011']
def scan(paths):
 out={}
 for p in paths:
  p=Path(p)
  if os.path.lexists(p):assert p.is_file(),p;out[str(p)]={'realpath':str(p.resolve()),'sha256':H(p)}
  else:out[str(p)]=None
 return out
watched=[root/(mod+suf) for root in [lib,*boundary] for mod in imports for suf in suffixes];initial=scan(watched)
def overlay():
 out={}
 for p in sorted((lib/'DiophantineConsistency').iterdir()):
  if p.name.startswith(name+'.') or p.name.startswith(checks+'.'):continue
  out[p.name]={'link':os.readlink(p) if p.is_symlink() else None,'realpath':str(p.resolve()),'file':p.is_file()}
 return out
ov=overlay();ovhash=hashlib.sha256(json.dumps(ov,sort_keys=True).encode()).hexdigest()
def audit():
 assert all(Path(p).is_file() and H(p)==h for p,h in anchors.items())
 assert H(src/(name+'.lean'))==anchors[str(source)] and H(src/(checks+'.lean'))==ch
 assert scan(watched)==initial and overlay()==ov
r={'status':'RUNNING','root':str(w),'provider':str(P),'parent_project_object_count':len(objects),'anchors':anchors,'boundary':list(map(str,boundary)),'candidate_guards':initial,'overlay_hash':ovhash,'overlay_entries':len(ov),'checks_sha256':ch,'records':[],'scope':'Every IΣ₁ model: fixed-port positive first-factor completion from positive first Pell-norm data and q³ divisibility, outside the reverse gap. Other factor units and the iPRA reverse implication remain open. Guarded focused inputs only; transitive project/package and dynamic ancestry historical.'}
def save():(w/'state.json').write_text(json.dumps(r,indent=2)+'\n')
def deps(n,phase):
 d=subprocess.run([str(LEAN),'--deps',str(src/(n+'.lean'))],env=env,capture_output=True,text=True);assert d.returncode==0 and not d.stderr,(n,d.stderr)
 lines=d.stdout.splitlines();assert all(Path(x).is_absolute() and Path(x).is_file() for x in lines)
 expected=imports if n==name else ['Init','DiophantineConsistency/'+name]
 assert {str(Path(x).relative_to(root))[:-6] for x in lines for root in [lib,*boundary] if Path(x).is_relative_to(root)}==set(expected),(n,lines)
 text=d.stdout.replace(str(w),'${RUN_ROOT}');(logs/(n+'.'+phase+'.deps')).write_text(text);return hashlib.sha256(text.encode()).hexdigest()
save();print('ROOT',w,'PARENT_OBJECTS',len(objects),'CANDIDATES',len(watched),flush=True)
try:
 audit()
 for n in (name,checks):
  before=deps(n,'before');obj=lib/'DiophantineConsistency'/(n+'.olean');assert not os.path.lexists(obj);log=logs/(n+'.log')
  with log.open('w') as out:p=subprocess.run([str(LEAN),'-M8000','-j1','-DElab.async=false','--root='+str(src.parent),str(src/(n+'.lean')),'-o',str(obj)],cwd=R,env=env,stdout=out,stderr=subprocess.STDOUT)
  text=log.read_text();assert p.returncode==0 and obj.is_file() and not any(x in text for x in ('error:','warning:','sorryAx')),(n,text)
  if n==checks:
   axioms=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text,re.S);assert len(axioms)==5 and all({a.strip() for a in x.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'} for x in axioms),axioms
  after=deps(n,'after');assert before==after
  r['records'].append({'module':n,'exit':p.returncode,'source_sha256':H(src/(n+'.lean')),'object_sha256':H(obj),'log_sha256':H(log),'deps_sha256':before});save();print(n,'0',flush=True)
 audit();r['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:
 r.update(status='FAILED',failure=repr(e));save();raise
