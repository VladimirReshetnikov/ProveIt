#!/usr/bin/env python3
"""Check proposed modules in a new isolated overlay of an already built pinned checkout.

No repository source or existing object is modified. See README for prerequisite
lake build commands. --objects may point to an independently fresh object tree.
"""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
BUNDLE=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--repo',type=Path,required=True)
p.add_argument('--work-dir',type=Path,required=True)
p.add_argument('--lean',default='lean')
p.add_argument('--objects',type=Path)
p.add_argument('--packages',type=Path)
a=p.parse_args()
a.repo=a.repo.resolve();a.work_dir=a.work_dir.resolve()
objects=(a.objects or a.repo/'.lake/build/lib/lean').resolve()
packages=(a.packages or a.repo/'.lake/packages').resolve()
if a.work_dir.exists() and any(a.work_dir.iterdir()):
 raise SystemExit('Use a new empty --work-dir; existing results will not be overwritten.')
a.work_dir.mkdir(parents=True,exist_ok=True)
subprocess.run(['python3',str(BUNDLE/'scripts/check_sources.py'),'--repo',str(a.repo)],check=True)
version=subprocess.check_output([a.lean,'--version'],cwd=a.repo,text=True)
if 'version 4.32.0,' not in version:
 raise SystemExit('Expected pinned Lean 4.32.0; got '+version)
libs=sorted(str(x) for x in packages.glob('*/.lake/build/lib/lean'))
if not objects.is_dir() or not libs:
 raise SystemExit('Build prerequisites first; object tree or dependency libraries missing.')
overlay=a.work_dir/'objects';overlay.mkdir()
for x in objects.iterdir():
 (overlay/x.name).symlink_to(x,target_is_directory=x.is_dir())
logs=a.work_dir/'logs';logs.mkdir()
records=[]

def local_dir(path):
 if path==overlay:return
 local_dir(path.parent)
 if path.is_symlink():
  source=path.resolve();path.unlink();path.mkdir()
  for x in source.iterdir():
   (path/x.name).symlink_to(x,target_is_directory=x.is_dir())
 elif not path.exists():path.mkdir()

def output_for(module):
 target=overlay/(module.replace('.','/')+'.olean')
 local_dir(target.parent)
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  path=target.with_suffix(suffix)
  if path.is_symlink():path.unlink()
 return target

def run(label,source,root,module=None,patched=True):
 paths=[str(overlay if patched else objects)]+libs
 env=dict(os.environ,LEAN_PATH=':'.join(paths))
 cmd=[a.lean,'--root='+str(root)]
 if module:cmd+=['-o',str(output_for(module))]
 cmd+=[str(source)]
 start=time.monotonic();log=logs/(label+'.log')
 with log.open('w') as f:
  result=subprocess.run(cmd,cwd=a.repo,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=360)
 record={'label':label,'source':str(source),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3),'log':log.name,'command':cmd}
 if module:
  obj=overlay/(module.replace('.','/')+'.olean')
  record['object_size']=obj.stat().st_size if obj.exists() else 0
  if result.returncode==0 and not record['object_size']:
   raise SystemExit('Empty compiled object: '+str(obj))
 records.append(record)
 (a.work_dir/'records.json').write_text(json.dumps({'compiler':version.strip(),'records':records},indent=2)+'\n')
 print(json.dumps({k:record[k] for k in ['label','exit_code','seconds']}),flush=True)
 if result.returncode:
  print(log.read_text());raise SystemExit(result.returncode)
 if 'sorryAx' in log.read_text():raise SystemExit('Unexpected admitted proof dependency')
 return log.read_text()

base=run('baseline-changed-axioms',BUNDLE/'lean/ChangedAxioms.lean',BUNDLE/'lean',patched=False)
for m in ['WangTiles942HelicalQuotient','RatioReparameterization','PolynomialRangeBounds','MarginSeparation']:
 run('patched-'+m,BUNDLE/'proposed/DiophantineConsistency'/(m+'.lean'),BUNDLE/'proposed','DiophantineConsistency.'+m)
new=run('patched-changed-axioms',BUNDLE/'lean/ChangedAxioms.lean',BUNDLE/'lean')
if base!=new:raise SystemExit('Baseline and proposed axiom reports differ; inspect logs.')
source_root=a.repo/'Computability/DiophantineConsistency/Lean'
for m in ['WangTiles942HelicalQuotientChecks','RatioMarginFinalizer']:
 run('client-'+m,source_root/'DiophantineConsistency'/(m+'.lean'),source_root,'DiophantineConsistency.'+m)
for m in ['SignedPrefix','RankPotentialActual','HelicalOrbit','AlgebraDeltas']:
 run('extension-'+m,BUNDLE/'lean'/(m+'.lean'),BUNDLE/'lean',m)
summary={'success':True,'compiler':version.strip(),'axiom_reports_identical':True,'direct_modules':4,'direct_proofs':5,'focused_clients':2,'extension_and_example_files':4,'records':records}
(a.work_dir/'records.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))
