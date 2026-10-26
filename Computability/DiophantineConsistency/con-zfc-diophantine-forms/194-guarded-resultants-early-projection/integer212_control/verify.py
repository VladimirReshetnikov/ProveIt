#!/usr/bin/env python3
"""Read-only replay, including a genuinely relocated deterministic rebuild."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
FLAGS=['-B']+(['-O']if sys.flags.optimize else[])
def run(script,*args,cwd=ROOT):
 p=subprocess.run([sys.executable,*FLAGS,str(script),*map(str,args)],cwd=cwd,text=True,capture_output=True)
 if p.returncode:raise ValueError(str(script)+'\n'+p.stdout+'\n'+p.stderr)
 return p.stdout

def main(parent=False):
 result={'status':'PASS','optimized':bool(sys.flags.optimize),'algebra':json.loads(run(ROOT/'check.py')),'exports':json.loads(run(ROOT/'export_readable.py','--check'))}
 with tempfile.TemporaryDirectory(prefix='scaled-pell212-')as td:
  td=Path(td);copy=td/'relocated-source';shutil.copytree(ROOT,copy)
  output=td/'rebuilt';run(copy/'build.py','--out',output,cwd=copy)
  count=0
  for p in output.rglob('*.json'):
   if p.read_bytes()!=(ROOT/p.relative_to(output)).read_bytes():raise ValueError('relocated rebuild '+str(p.relative_to(output)))
   count+=1
  result['relocated_byte_identical_json']=count
  arc=copy/'inherited/Source173.zip'
  if hashlib.sha256(arc.read_bytes()).hexdigest()!='760428ab91a1f39019ebb452d8b347235b5bb1a0935346e23de78b4542e68677':raise ValueError('original source173 archive')
  with zipfile.ZipFile(arc)as z:
   prefix='ConZFC_CRT_Index_Anchor_215_2026-10-25/'
   if z.read(prefix+'stages/affine213/equation.json')!=(ROOT/'sources/parent213.json').read_bytes():raise ValueError('immediate preoptimization source binding')
   if parent:
    for i in z.infolist():
     if i.filename.startswith('/')or'..'in Path(i.filename).parts:raise ValueError('unsafe archive')
    dest=td/'source173';z.extractall(dest)
  result['source173_original_archive_and_stage_binding']=True
  if parent:
   src=dest/prefix.rstrip('/');r=json.loads(run(src/'verify.py',cwd=src))
   result['parent']={'status':r['status'],'optimized':r['python_optimized'],'manifest_files':r['integrity']['manifest_files_checked'],'reconstructed_stages':r['coefficient_rebuild']['reconstructed_stage_count'],'all_equations_byte_identical':r['coefficient_rebuild']['all_equations_byte_identical'],'all_expansions_byte_identical':r['coefficient_rebuild']['all_expansions_byte_identical'],'complete_receipt_sha256':hashlib.sha256(json.dumps(r,sort_keys=True,separators=(',',':')).encode()).hexdigest()}
 manifest=ROOT/'MANIFEST_SHA256.json'
 if manifest.exists():
  entries=json.loads(manifest.read_text())
  for name,digest in entries.items():
   if Path(name).is_absolute()or'..'in Path(name).parts:raise ValueError('nonrelative manifest path')
   if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:raise ValueError('manifest '+name)
  result['manifest_files']=len(entries)
 return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--parent',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args();result=main(a.parent);s=json.dumps(result,sort_keys=True,indent=2)+'\n';print(s,end='')
 if a.receipt:a.receipt.write_text(s)
