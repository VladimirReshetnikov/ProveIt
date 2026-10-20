#!/usr/bin/env python3
"""Run the pinned complete upstream-to-K218 lineage with explicit input paths."""
from pathlib import Path
import argparse,os,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
def main():
 if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
  raise RuntimeError('Assertions must remain enabled')
 ap=argparse.ArgumentParser();ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 out=a.output.resolve()
 if out==ROOT or ROOT in out.parents:raise ValueError('Construction output must be outside this packet')
 subprocess.run([sys.executable,'-B',str(ROOT/'portable/lineage/build_lineage.py'),
  '--upstream-table',str(a.baseline/'machine/k219.native.tm'),
  '--upstream-source',str(a.baseline/'machine/sites219.json'),'--out',str(out)],
  check=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
if __name__=='__main__':main()
