#!/usr/bin/env python3
"""Replay PA194NS checks in a new temporary directory without editing release."""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def main():
 assert __debug__ and not sys.flags.optimize,'Assertions must be enabled.'
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true');ap.add_argument('--work',type=Path);args=ap.parse_args()
 if args.work:
  args.work.mkdir(parents=True,exist_ok=False);work=args.work
 else:work=Path(tempfile.mkdtemp(prefix='pa194ns-verify-'))
 def call(*parts):subprocess.run([sys.executable,'-B',str(ROOT/parts[0]),*map(str,parts[1:])],check=True)
 call('proof/check_commands.py','--output',work/'commands.json')
 call('construction/build.py','--output',work/'construction')
 for name in ['machine.tm','machine.native.tm','raw.native.tm','sites.json','instructions.json','folds.json','labels.json']:
  assert (work/'construction'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),name
 if args.full:call('verification/check.py','--output',work/'independent')
 print(json.dumps({'status':'PASS','full_independent_audit':args.full,'fresh_evidence':str(work),'kernel_checked':False},indent=2))

if __name__=='__main__':main()
