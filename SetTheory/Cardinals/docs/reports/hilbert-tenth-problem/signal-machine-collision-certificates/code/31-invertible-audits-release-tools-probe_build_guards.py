#!/usr/bin/env python3
"""Instrument only the inspected typesetter's output boundary; never load science programs."""
import runpy,sys
from pathlib import Path
mode,script=sys.argv[1:3]
args=sys.argv[3:]
mod=runpy.run_path(script,run_name='guard_probe')
g=mod['main'].__globals__;original=g['run'];passes=0
extra=Path('/usr/share/texlive/texmf-dist/tex/latex/base/size12.clo')
def wrapped(argv,cwd,env,timeout=240):
 global passes
 out=original(argv,cwd,env,timeout)
 if argv[0]=='/usr/bin/pdflatex':
  passes+=1
  if mode=='first-pass-input' and passes==1:
   p=cwd/'Report61.fls';p.write_bytes(p.read_bytes()+b'INPUT '+str(extra).encode()+b'\n')
 if argv[0]=='/usr/bin/pdftoppm':
  prefix=Path(argv[-1]);pages=prefix.parent
  files=sorted(pages.iterdir());middle=files[len(files)//2]
  if mode=='middle-png-corruption':middle.write_bytes(middle.read_bytes()[:-1])
  if mode=='missing-middle-page':middle.unlink()
  if mode=='extra-page':(pages/'page-999.png').write_bytes(files[0].read_bytes())
 return out
g['run']=wrapped
sys.argv=[script,*args]
mod['main']()
