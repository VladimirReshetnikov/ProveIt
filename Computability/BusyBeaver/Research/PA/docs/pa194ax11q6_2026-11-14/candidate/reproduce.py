#!/usr/bin/env python3
"""Rebuild and verify PA194AX11Q6 in a fresh temporary directory.

Default: construction and independent literal universal checks, exact source
splice, free-term command proofs, finite K/S exchange, whole blank startup,
and exact bytes compared to the frozen machine. --quick omits the two long
universal tape replays and is only a structural smoke check.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def main():
 assert __debug__ and not sys.flags.optimize,'Run without -O.'
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--quick',action='store_true')
 parser.add_argument('--work',type=Path,help='Fresh directory; must not exist.')
 parser.add_argument('--receipt',type=Path,help='Optional permanent JSON receipt.')
 args=parser.parse_args();started=time.monotonic()
 if args.work:
  work=args.work.resolve();work.mkdir(parents=True,exist_ok=False)
 else:work=Path(tempfile.mkdtemp(prefix='pa194ax11q6-replay-'))
 copied=work/'source'
 shutil.copytree(ROOT,copied,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.log'))
 machine=work/'rebuilt';commands=[]
 def run(label,command):
  print(label,flush=True)
  log=work/(label+'.log')
  with log.open('w')as f:
   result=subprocess.run([sys.executable,'-B']+list(map(str,command)),cwd=copied,stdout=f,stderr=subprocess.STDOUT)
  commands.append(dict(label=label,returncode=result.returncode,log=str(log)))
  if result.returncode:
   print(log.read_text()[-12000:],file=sys.stderr)
   raise SystemExit('Verification failed: '+label)
 run('build',[copied/'build_ax11q6.py','--output',machine]+(['--quick']if args.quick else[]))
 for name in('machine.tm','machine.native.tm','raw.native.tm','labels.json','grammar.json','nodes.json','instructions.json','sites.json'):
  assert(machine/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),name
 run('source_splice',[copied/'proof/source_splice.py','--machine',machine])
 run('command_words',[copied/'proof/commands.py','--machine',machine,'--output',machine/'commands.json'])
 run('premise_exchange',[copied/'proof/exchange_certificate.py'])
 if not args.quick:run('independent_tape',[copied/'verification/check.py',machine])
 receipt=dict(status='PASS',machine='PA194AX11Q6',working_states=194,
   full_universal_tape_replays=not args.quick,exact_rebuild=True,
   source_splice=json.loads((machine/'source_splice.json').read_text()),
   command_words=json.loads((machine/'commands.json').read_text()),
   construction=json.loads((machine/'receipt.json').read_text()),
   independent=None if args.quick else json.loads((machine/'independent/receipt.json').read_text()),
   elapsed_seconds=time.monotonic()-started,work=str(work),commands=commands)
 text=json.dumps(receipt,indent=2)+'\n';(work/'receipt.json').write_text(text)
 if args.receipt:args.receipt.resolve().write_text(text)
 print(json.dumps(dict(status='PASS',full=not args.quick,states=194,work=str(work),receipt=str(args.receipt or work/'receipt.json'))),flush=True)
if __name__=='__main__':main()
