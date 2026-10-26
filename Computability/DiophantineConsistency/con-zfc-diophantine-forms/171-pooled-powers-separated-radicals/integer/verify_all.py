#!/usr/bin/env python3
"""Read-only normal/-O audit plus byte-identical frozen reconstruction."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
FLAGS=['-B']+(['-O']if sys.flags.optimize else[])
def run(script,*args,cwd=ROOT):
 p=subprocess.run([sys.executable,*FLAGS,str(script),*map(str,args)],cwd=cwd,capture_output=True,text=True)
 if p.returncode:raise ValueError(str(script)+' failed\n'+p.stdout+'\n'+p.stderr)
 return p.stdout

def main(parent=False):
 result={'status':'PASS','optimized':bool(sys.flags.optimize),'finite_audit':json.loads(run(ROOT/'check.py'))}
 result['readable_exports']=json.loads(run(ROOT/'export_readable.py','--check'))
 with tempfile.TemporaryDirectory(prefix='conzfc217-replay-')as td:
  dest=Path(td)/'new';run(ROOT/'build.py','--out',dest);count=0
  for f in dest.rglob('*.json'):
   target=ROOT/f.relative_to(dest)
   if f.read_bytes()!=target.read_bytes():raise ValueError('byte reconstruction '+str(target))
   count+=1
  result['byte_identical_json_files']=count
  if parent:
   source=Path(td)/'parent';source.mkdir()
   with zipfile.ZipFile(ROOT/'inherited/ConZFC_Strict_Horizons_2026-10-25.zip')as z:
    for i in z.infolist():
     if i.filename.startswith('/')or '..'in Path(i.filename).parts:raise ValueError('unsafe archive member')
    z.extractall(source)
   p=source/'ConZFC_Strict_Horizons_2026-10-25';result['parent_replay']=json.loads(run(p/'verify.py','--rebuild',cwd=p))
 manifest=ROOT/'MANIFEST_SHA256.json'
 if manifest.exists():
  data=json.loads(manifest.read_text())
  for p,h in data.items():
   if hashlib.sha256((ROOT/p).read_bytes()).hexdigest()!=h:raise ValueError('manifest '+p)
  result['manifest_files']=len(data)
 return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--parent',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args();r=main(a.parent);s=json.dumps(r,indent=2)+'\n';print(s,end='')
 if a.receipt:a.receipt.write_text(s)
