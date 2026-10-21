#!/usr/bin/env python3
"""Replay selected K218 source experiments using five pinned upstream files.

--upstream accepts either the ProveIt checkout root or its Research/ZFC directory.
The default core group takes roughly ten seconds. Larger groups include bounded
searches and may take several minutes. All outputs remain beside these scripts.
No binary runtime theorem is checked by this driver.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
PINS={
 'candidate-k218/sites218.json':'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9',
 'candidate-k218/k218.native.tm':'2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f',
 'k218-quantifier-stability/pricing/source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
 'k218-quantifier-stability/pricing/build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
 'k218-quantifier-stability/pricing/measure_pinned.py':'342537f773807e185ed250a18db27afe5122abf2b8bda0e8a31f073e0d1ca397',
}
GROUPS={
 'core':['row_order_search.py','all_tag_permutations.py','all_four_tag_permutations.py','reversed_implication_price.py'],
 'rows':['row_order_search.py'],
 'tags':['all_tag_permutations.py','all_four_tag_permutations.py'],
 'implication':['reversed_implication_price.py','reversed_implication_repair.py'],
 'dual':['dual_rho6_price.py','dual_rho6_inplace.py'],
 'fields':['axiom_field_search.py'],
 'wrappers':['wrapper_price.py','wrapper_precompute_price_bounded.py'],
 'classical':['classical_price.py'],
}
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--upstream',type=Path,default=HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC')
 ap.add_argument('--experiment',choices=[*GROUPS,'seed','all'],default='core')
 ap.add_argument('--verify-only',action='store_true')
 args=ap.parse_args();up=args.upstream.resolve()
 if (up/'Computability/BusyBeaver/Research/ZFC').is_dir():up=up/'Computability/BusyBeaver/Research/ZFC'
 if args.experiment!='seed':
  for name,sha in PINS.items():
   raw=(up/name).read_bytes();actual=hashlib.sha256(raw).hexdigest()
   if actual!=sha:raise ValueError(f'Upstream SHA mismatch: {name}: {actual}')
  print('Five pinned source inputs verified.',flush=True)
 env=dict(os.environ,PROVEIT_ZFC_ROOT=str(up),PYTHONDONTWRITEBYTECODE='1')
 command=[sys.executable,'-B',str(HERE/'replay_seed3.py'),'--check-only',str(HERE/'seed3-certificate/seed3-proof.json'),'--output',str(HERE/'seed3-reproduced')]
 subprocess.run(command,check=True,env=env)
 if args.verify_only or args.experiment=='seed':return
 names=GROUPS.get(args.experiment)
 if names is None:names=list(dict.fromkeys(n for group in GROUPS.values()for n in group))
 logdir=HERE/'reproduction-logs';logdir.mkdir(exist_ok=True);receipts=[]
 for name in names:
  print(f'Running {name}...',flush=True);start=time.monotonic()
  with (logdir/(name+'.log')).open('w')as stream:
   result=subprocess.run([sys.executable,'-B',str(HERE/name)],check=False,env=env,stdout=stream,stderr=subprocess.STDOUT)
  item=dict(script=name,returncode=result.returncode,seconds=time.monotonic()-start,log=str(logdir/(name+'.log')));receipts.append(item)
  (logdir/'replay.json').write_text(json.dumps(receipts,indent=2)+'\n')
  print(json.dumps(item),flush=True)
  if result.returncode:raise RuntimeError(f'{name} failed; inspect its log.')
if __name__=='__main__':main()
