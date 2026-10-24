#!/usr/bin/env python3
"""Copy just the three component directories, rebuild and replay outside CWD."""
from pathlib import Path
import tempfile, shutil, subprocess, hashlib, json, sys
R=Path(__file__).resolve().parents[2]
files=['low_degree/p13_degree30.json','low_degree/p12_product_split2.json','low_degree/p12_sos_split2.json','mixed_source/parent_source.json','mixed_source/source21.json','mixed_source/source24.json','mixed_source/source26.json']
def hashes(root): return {f:hashlib.sha256((root/f).read_bytes()).hexdigest() for f in files}
expected=hashes(R); runs=[]
with tempfile.TemporaryDirectory(prefix='positive-portable-') as tmp:
 root=Path(tmp)/'packet'; root.mkdir()
 for component in ['low_degree','mixed_source','review/positive']:
  shutil.copytree(R/component,root/component,ignore=shutil.ignore_patterns('__pycache__'))
 for opt in [[],['-O']]:
  commands=[['low_degree/build13.py'],['low_degree/build12.py'],*[[ 'mixed_source/build.py',n] for n in ['21','24','26']],['low_degree/check13.py'],['low_degree/check12.py'],['mixed_source/check.py'],['review/positive/check.py']]
  for command in commands:
   p=subprocess.run([sys.executable,*opt,str(root/command[0]),*command[1:]],cwd='/',text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   if p.returncode: raise RuntimeError('Failed '+str(command)+'\n'+p.stdout)
   runs.append({'optimized':bool(opt),'command':' '.join(command),'returncode':p.returncode})
  if hashes(root)!=expected: raise RuntimeError('Rebuild changed frozen JSON bytes')
 receipt={'status':'passed','executions':runs,'byte_identical_rebuilt_or_preserved_files':expected,'layout':'package/{low_degree,mixed_source,review/positive}','cwd':'/','dependencies':'Python 3; SymPy for mixed_source and independent projection audit; standard library only for low_degree'}
 (R/'review/positive/PORTABILITY.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
