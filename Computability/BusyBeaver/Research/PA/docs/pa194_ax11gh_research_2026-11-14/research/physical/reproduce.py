#!/usr/bin/env python3
"""Offline replay of the new bounded negative screens. Writes only to --work."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--work',type=Path,required=True)
 ap.add_argument('--derive-contexts',action='store_true',help='Regenerate both full symbolic context files, instead of using frozen ones.')
 a=ap.parse_args();a.work.mkdir(parents=True,exist_ok=False)
 if not __debug__:raise SystemExit('Python assertions must be enabled.')
 py=sys.executable;receipts={}
 def run(cmd,out,err=None):
  with (a.work/out).open('w') as log:
   if err:
    with (a.work/err).open('w') as errors:subprocess.run(cmd,stdout=log,stderr=errors,check=True)
   else:subprocess.run(cmd,stdout=log,check=True)
 run([py,'-B',str(ROOT/'code/alias_analysis.py')],'alias_summary.json')
 assert json.loads((a.work/'alias_summary.json').read_text())==json.loads((ROOT/'recorded/alias_summary.json').read_text())
 run([py,'-B',str(ROOT/'code/relay_transfer.py')],'relay_transfer.json')
 assert json.loads((a.work/'relay_transfer.json').read_text())==json.loads((ROOT/'recorded/relay_transfer.json').read_text())
 pairctx=ROOT/'recorded/paircontexts10.txt';ghctx=ROOT/'recorded/contexts6.txt'
 if a.derive_contexts:
  run([py,'-B',str(ROOT/'code/collect_pair_contexts.py'),'10',str(a.work/'paircontexts10.txt')],'pair_context_receipt.json')
  run([py,'-B',str(ROOT/'code/collect_gh_contexts.py'),'6',str(a.work/'contexts6.txt')],'gh_context_receipt.json')
  for p in [pairctx,ghctx]:assert (a.work/p.name).read_bytes()==p.read_bytes()
  pairctx=a.work/pairctx.name;ghctx=a.work/ghctx.name
 for name in ['fold_pair_synth','action_merge_future','eliminate']:
  subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'code'/f'{name}.cpp'),'-o',str(a.work/name)],check=True)
 for keep,rem,expected in [(88,301,5649890),(122,16,4791766)]:
  tag=f'fold_{keep}_{rem}'
  run([str(a.work/'fold_pair_synth'),str(ROOT/'inputs/primary/machine.native.tm'),'10','80',str(pairctx),str(keep),str(rem)],tag+'_hits.txt',tag+'.log')
  assert (a.work/(tag+'_hits.txt')).read_bytes()==(ROOT/'recorded'/(tag+'_hits.txt')).read_bytes()
  count,hits=map(int,re.search(r'checked (\d+) hits (\d+)',(a.work/(tag+'.log')).read_text()).groups())
  assert count==expected
  receipts[tag]=dict(candidates=count,local_hits=hits)
 run([py,'-B',str(ROOT/'code/validate_router_hits.py'),str(a.work/'fold_88_301_hits.txt')],'router_validation.json')
 actual=json.loads((a.work/'router_validation.json').read_text());old=json.loads((ROOT/'recorded/validation_88_301.json').read_text())
 assert len(actual)==len(old)==18
 for new,was in zip(actual,old):
  for key in was:assert new[key]==was[key],(key,new,was)
 for name in ['action_merge_future','eliminate']:
  run([str(a.work/name),str(ROOT/'inputs/gh/machine.native.tm'),'6','180',str(ghctx)],name+'_hits.jsonl',name+'.log')
  assert not (a.work/(name+'_hits.jsonl')).read_text()
  receipts[name]=dict(radius=6,local_step_bound=180,hits=0)
 receipts['context_files_rederived']=a.derive_contexts
 receipts['inputs']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'inputs').rglob('*')) if p.is_file()}
 receipts['conclusion']='No sub-194 blank-start construction was certified. These are bounded-family results, not state lower bounds.'
 (a.work/'reproduction.json').write_text(json.dumps(receipts,indent=2)+'\n')
 print(json.dumps(receipts,indent=2))
if __name__=='__main__':main()
