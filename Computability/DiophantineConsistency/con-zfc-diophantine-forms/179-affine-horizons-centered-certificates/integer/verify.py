#!/usr/bin/env python3
"""Read-only certificate replay and optional retained-parent rebuild."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,zipfile,shutil
ROOT=Path(__file__).resolve().parent
FLAGS=['-B']+(['-O']if sys.flags.optimize else[])
def run(script,*args,cwd=ROOT):
 p=subprocess.run([sys.executable,*FLAGS,str(script),*map(str,args)],cwd=cwd,text=True,capture_output=True)
 if p.returncode:raise ValueError(str(script)+'\n'+p.stdout+'\n'+p.stderr)
 return p.stdout

def main(parent=False):
 out={'status':'PASS','optimized':bool(sys.flags.optimize),'algebra':json.loads(run(ROOT/'check.py')),'exports':json.loads(run(ROOT/'export_readable.py','--check'))}
 with tempfile.TemporaryDirectory(prefix='conzfc215-')as td:
  copied=Path(td)/'relocated-source';shutil.copytree(ROOT,copied)
  dest=Path(td)/'rebuild';run(copied/'build.py','--out',dest,cwd=copied);n=0
  for p in dest.rglob('*.json'):
   if p.read_bytes()!=(ROOT/p.relative_to(dest)).read_bytes():raise ValueError('rebuild '+str(p.relative_to(dest)))
   n+=1
  out['byte_identical_rebuilt_json']=n;out['rebuild_from_relocated_package']=True
  if parent:
   p=Path(td)/'parent';p.mkdir()
   with zipfile.ZipFile(ROOT/'inherited/Round21_Integer217.zip')as z:
    for i in z.infolist():
     if i.filename.startswith('/')or'..'in Path(i.filename).parts:raise ValueError('unsafe parent archive')
    z.extractall(p)
   q=p/'Round21_Integer217';out['parent']=json.loads(run(q/'verify_all.py','--parent',cwd=q))
 manifest=ROOT/'MANIFEST_SHA256.json'
 if manifest.exists():
  entries=json.loads(manifest.read_text())
  for p,h in entries.items():
   if hashlib.sha256((ROOT/p).read_bytes()).hexdigest()!=h:raise ValueError('manifest '+p)
  out['manifest_files']=len(entries)
 return out
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--parent',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args();result=main(a.parent);s=json.dumps(result,indent=2)+'\n';print(s,end='')
 if a.receipt:a.receipt.write_text(s)
