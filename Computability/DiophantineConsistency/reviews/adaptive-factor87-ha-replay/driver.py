#!/usr/bin/env python3
"""Rebuild the HA sentence bridge on a guarded adaptive literal provider."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile, time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
B=Path('/tmp/foundation-ha-current-transfer-root-peer-gx4g2m1q')
C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl')
p=argparse.ArgumentParser();p.add_argument('--literal',type=Path,required=True);p.add_argument('--expected',type=Path);a=p.parse_args();A=a.literal.resolve()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def check(p,h):
 if not Path(p).is_file() or sha(p)!=h:raise RuntimeError('hash mismatch: '+str(p))
base=read(A/'state.json');assert base['status']=='PASS';check(A/'providers.json',base['providers_sha256']);guard=read(C/'guards.json');cs=read(C/'state.json');assert cs['status']=='PASS';check(C/'guards.json',cs['guards_sha256'])
packet=read(B/'packet.json'); historical_changed={'PAHF.PASyntax','DiophantineConsistency.HAProofs','DiophantineConsistency.FoundationPAHFSyntax','DiophantineConsistency.WangTiles942Data','DiophantineConsistency.CurrentMaskData2011','DiophantineConsistency.CurrentEquationSyntax2011'}
for pth,h in guard.items():check(pth,h)
changed=set()
for row in packet['modules']:
 if row.get('source_sha256') and sha(row['source']) != row['source_sha256']:changed.add(row['module'])
assert changed==historical_changed, changed
skip={'HAProofs','ArithmeticExpression','ArithmeticRepresentation','NaturalExpression','NaturalExpressionSemiring','Representation'};seen=set();order=[]
def visit(n):
 if n in seen:return
 seen.add(n);p=S/(n+'.lean')
 if p.exists():
  for i in re.findall(r'^\s*(?:public\s+)?import\s+DiophantineConsistency\.([\w]+)',p.read_text(),re.M):visit(i)
  if n not in skip:order.append(n)
for n in ['FoundationHAPeano','FoundationHANoZero']:visit(n)
order += ['AdaptiveFactor87HA','AdaptiveFactor87HAChecks']
sources={n:sha(S/(n+'.lean')) for n in order};snapshot={n:sha(S/(n+'.lean')) for n in seen if (S/(n+'.lean')).exists()};w=Path(tempfile.mkdtemp(prefix='adaptive-factor87-ha-build-'));lib=w/'lib';lib.mkdir();logs=w/'logs';logs.mkdir();print('ROOT',w,flush=True)
state={'status':'RUNNING','literal':str(A),'foundation':str(B),'root':str(w),'order':order,'sources':sources,'local_source_closure':snapshot,'historical_changed':sorted(changed),'records':[],'boundary':base['boundary'],'scope':'Actual HA proof relating two 13-variable no-zero sentences; not consistency. Foundation/mathlib and the guarded literal provider are inherited.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save()
try:
 subprocess.run(['cp','-as',str(A/'lib')+'/.',str(lib)],check=True)
 additions=[]
 for src in (B/'lib').rglob('*.olean'):
  if not src.is_file():continue
  rel=src.relative_to(B/'lib')
  if str(rel)=='PAHF/PASyntax.olean':continue
  dst=lib/rel;dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():dst.symlink_to(src.resolve());additions.append({'path':str(src),'sha256':sha(src)})
 (w/'additions.json').write_text(json.dumps(additions,indent=2)+'\n');state['additions_sha256']=sha(w/'additions.json');save()
 env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*base['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 expected=read(a.expected/'state.json') if a.expected else None
 for n in order:
  src=S/(n+'.lean');check(src,sources[n]);out=lib/'DiophantineConsistency'/(n+'.olean');out.unlink(missing_ok=True);log=logs/(n+'.log');cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false',str(src),'-o',str(out)];print('START',n,flush=True);start=time.monotonic()
  with log.open('w') as f:proc=subprocess.run(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT)
  rec={'name':n,'exit':proc.returncode,'seconds':time.monotonic()-start,'source_sha256':sha(src),'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(log)};state['records'].append(rec);save()
  if proc.returncode or re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()):raise RuntimeError('build failed: '+n+'\n'+log.read_text())
  if expected:
   prior=next(x for x in expected['records'] if x['name']==n)
   for k in ['source_sha256','object_sha256','log_sha256']:assert rec[k]==prior[k],(n,k)
  print('PASS',n,flush=True)
 for n,h in snapshot.items():check(S/(n+'.lean'),h)
 for pth,h in guard.items():check(pth,h)
 for row in additions:check(row['path'],row['sha256'])
 for row in packet['modules']:
  if row['module'] not in historical_changed and row.get('source_sha256'):check(row['source'],row['source_sha256'])
 check(A/'providers.json',base['providers_sha256']);check(C/'guards.json',cs['guards_sha256'])
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as exc:
 state['status']='FAILED';state['failure']=str(exc);save();print('FAILED',w,str(exc),flush=True);raise
