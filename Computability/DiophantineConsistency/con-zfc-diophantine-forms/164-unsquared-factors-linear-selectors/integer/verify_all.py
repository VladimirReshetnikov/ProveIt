#!/usr/bin/env python3
"""Portable deterministic new-component replay and independent artifact checks."""
import hashlib,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def need(t,s):
 if not t:raise ValueError(s)
def run(name,*args):
 cmd=[sys.executable,'-B']+(['-O']if not __debug__ else [])+[str(ROOT/name),*map(str,args)]
 p=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True)
 need(p.returncode==0,name+' failed\n'+p.stdout+p.stderr)
 return p.stdout

def manifest():
 base=ROOT/'inherited_factorial_free';count=0
 for line in (base/'MANIFEST.sha256').read_text().splitlines():
  if not line.strip():continue
  h,rel=line.split(None,1);rel=rel.lstrip('*');p=base/rel
  need(p.resolve().is_relative_to(base.resolve()),'safe manifest path')
  need(hashlib.sha256(p.read_bytes()).hexdigest()==h,'inherited file '+rel);count+=1
 return count

def report_bindings():
 text=(ROOT/'report_section.tex').read_text()
 for profile,name in [('Dimension','integer239'),('Balanced','integer240_balanced'),('Sparse','integer240_sparse')]:
  m=json.loads((ROOT/name/'METRICS.json').read_text());line=f"{profile} & {m['variables']} & {m['rows']} & {m['monomials']:,} & {m['height']:,}"
  need(line in text,'reported profile '+profile)
 return {'status':'pass','profiles':3}

def main():
 result={'status':'pass','normal_interpreter':__debug__,'inherited_manifest_files':manifest()}
 for name in ['check_source_interface.py','check.py','check_selected.py','check_lemmas.py']:
  result[name]=json.loads(run(name))
 result['report_bindings']=report_bindings()
 result['readable_exports']=json.loads(run('export_readable.py','--check'))
 with tempfile.TemporaryDirectory(prefix='r20-direct-')as td:
  tmp=Path(td);run('build.py','--out',tmp);run('build_selected.py','--out',tmp);count=0
  for p in sorted(tmp.rglob('*.json')):
   rel=p.relative_to(tmp);need((ROOT/rel).read_bytes()==p.read_bytes(),'fresh rebuild '+str(rel));count+=1
 result['byte_identical_rebuilt_files']=count
 result['verification_boundary']='Finite new-source and row-basis certificates checked; unbounded new proof in PROOF.md, inherited arithmetic and C222 calibration retained with original scope.'
 print(json.dumps(result,sort_keys=True,indent=2))
if __name__=='__main__':main()
