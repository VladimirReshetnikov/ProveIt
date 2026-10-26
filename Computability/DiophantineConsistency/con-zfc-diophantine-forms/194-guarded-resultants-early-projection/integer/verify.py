#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
FLAGS=['-B']+(['-O']if sys.flags.optimize else[])
def run(p,*args,cwd=ROOT):
 s=subprocess.run([sys.executable,*FLAGS,str(p),*map(str,args)],cwd=cwd,text=True,capture_output=True)
 if s.returncode:raise ValueError(str(p)+'\n'+s.stdout+'\n'+s.stderr)
 return s.stdout

def main(parent=False):
 r={'status':'PASS','optimized':bool(sys.flags.optimize),'algebra':json.loads(run(ROOT/'check.py')),'exports':json.loads(run(ROOT/'export_readable.py','--check'))}
 with tempfile.TemporaryDirectory(prefix='affine209-')as td:
  td=Path(td);copy=td/'relocated-package';shutil.copytree(ROOT,copy);out=td/'rebuild';run(copy/'build.py','--out',out,cwd=copy);count=0
  for p in out.rglob('*.json'):
   if p.read_bytes()!=(ROOT/p.relative_to(out)).read_bytes():raise ValueError('relocated rebuild '+str(p.relative_to(out)))
   count+=1
  r['relocated_byte_identical_json']=count
  arc=copy/'inherited/Source210.zip'
  if hashlib.sha256(arc.read_bytes()).hexdigest()!='33fecaaa728d5f38608b8b0930c09b08dbe9a01e03f6269f092ec6142d72a0ee':raise ValueError('original210archive')
  with zipfile.ZipFile(arc)as z:
   prefix='ConZFC_Pell_Growth_210_2026-10-25/'
   if z.read(prefix+'equations/principal210/equation.json')!=(ROOT/'sources/parent210.json').read_bytes():raise ValueError('immediate source210 stage binding')
   if parent:
    for i in z.infolist():
     if i.filename.startswith('/')or'..'in Path(i.filename).parts:raise ValueError('unsafe archive')
    dest=td/'parent';z.extractall(dest)
  r['original_source_archive_and_stage_binding']=True
  if parent:
   src=dest/prefix.rstrip('/');q=json.loads(run(src/'verify.py',cwd=src))
   r['parent']={'status':q['status'],'optimized':q['python_optimized'],'manifest_files':q['integrity']['manifest_files_checked'],'inherited_manifest_files':q['inherited_parent']['integrity']['manifest_files_checked'],'inherited_reconstructed_stages':q['inherited_parent']['coefficient_rebuild']['reconstructed_stage_count'],'fresh_rebuild':q['fresh_rebuild'],'complete_receipt_sha256':hashlib.sha256(json.dumps(q,sort_keys=True,separators=(',',':')).encode()).hexdigest()}
 if (ROOT/'MANIFEST_SHA256.json').exists():
  entries=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())
  for name,h in entries.items():
   if Path(name).is_absolute()or'..'in Path(name).parts:raise ValueError('absolute manifest')
   if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h:raise ValueError('manifest '+name)
  r['manifest_files']=len(entries)
 return r
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--parent',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args();s=json.dumps(main(a.parent),sort_keys=True,indent=2)+'\n';print(s,end='')
 if a.receipt:a.receipt.write_text(s)
