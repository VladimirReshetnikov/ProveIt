#!/usr/bin/env python3
"""Replay AX11G without modifying frozen machine or evidence files."""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without -O')

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--quick',action='store_true',help='Skip both universal physical replays; still check source, table, startup and command algebra.')
 ap.add_argument('--output',type=Path)
 a=ap.parse_args()
 with tempfile.TemporaryDirectory(prefix='pa194ax11g-')as td:
  td=Path(td);out=td/'machine'
  cmd=[sys.executable,'-B',str(HERE/'build.py'),'--output',str(out)]
  if a.quick:cmd.append('--quick')
  subprocess.run(cmd,check=True,stdout=subprocess.DEVNULL)
  files=['machine.tm','machine.native.tm','raw.native.tm','grammar.json','labels.json','nodes.json','sites.json','instructions.json','folds.json','local_folds.json']
  for name in files:assert(out/name).read_bytes()==(HERE/'machine'/name).read_bytes(),name
  subprocess.run([sys.executable,'-B',str(HERE/'check_commands.py'),'--output',str(td/'commands.json')],check=True,stdout=subprocess.DEVNULL)
  physical=None
  if not a.quick:
   subprocess.run([sys.executable,'-B',str(HERE/'verification/check_physical.py'),str(out),'--output',str(td/'physical')],check=True,stdout=subprocess.DEVNULL)
   physical=json.loads((td/'physical/PA194AX11G/receipt.json').read_text())
  result={'status':'PASS','family':'PA194AX11G','core_files_identical':files,'quick':a.quick,'construction':json.loads((out/'receipt.json').read_text()),'commands':json.loads((td/'commands.json').read_text()),'independent_physical':physical}
  if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps(result,indent=2))
if __name__=='__main__':main()
