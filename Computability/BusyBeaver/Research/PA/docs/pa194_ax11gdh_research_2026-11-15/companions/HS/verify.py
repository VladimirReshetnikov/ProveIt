#!/usr/bin/env python3
"""Offline replay for PA194AX11GDHS; --full repeats the independent literal proof checks."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
CORE=['machine.tm','machine.native.tm','raw.native.tm','nodes.json','grammar.json','reference_grammar.json','sites.json','instructions.json','folds.json','labels.json','local_cases.json']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert __debug__,'Run without Python -O'
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--full',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
 with tempfile.TemporaryDirectory(prefix='pa194-ax11gdhs-')as temp:
  out=Path(temp)/'machine'
  subprocess.run([sys.executable,'-B',str(HERE/'build.py'),'--output',str(out)],check=True)
  for f in CORE:assert(out/f).read_bytes()==(HERE/'machine'/f).read_bytes(),('rebuild differs',f)
  command=Path(temp)/'commands.json'
  subprocess.run([sys.executable,'-B',str(HERE/'check_commands.py'),'--output',str(command)],check=True,stdout=subprocess.DEVNULL)
  stored=HERE/'machine/independent';receipt=json.loads((stored/'receipt.json').read_text())
  assert receipt['dense_sha256']==sha(out/'machine.tm')and receipt['native_sha256']==sha(out/'machine.native.tm')
  assert receipt['contracts_sha256']==sha(stored/'contracts.json')
  contracts=json.loads((stored/'contracts.json').read_text());ins=json.loads((out/'instructions.json').read_text())
  expected={(i,b)for i,row in enumerate(ins)for b in([False,True]if row[0]=='dec'else[False])}
  actual={(x['site'],x['positive'])for x in contracts};assert expected==actual and len(contracts)==len(actual)==4774
  assert all(len(x['duration'])==13 and all(c>=0 for c in x['duration'])and x['duration'][0]>=3 for x in contracts)
  assert len(json.loads((stored/'list_lemmas.json').read_text()))==4
  if a.full:
   subprocess.run([sys.executable,'-B',str(HERE/'independent/check.py'),str(out)],check=True)
   fresh=json.loads((out/'independent/receipt.json').read_text())
   for k in ['status','states','rows','source_sites','source_outcomes','symbolic_steps','maximum_symbolic_steps','minimum_positive_duration_constant','list_lemmas_from_literal_table','box_oracles','independent_source_resolvers_agree','dense_native_conjugacy','whole_blank_startup','startup_steps','dense_sha256','native_sha256','contracts_sha256']:assert fresh[k]==receipt[k],k
  result={'status':'PASS','machine':'PA194AX11GDHS','dense_sha256':sha(out/'machine.tm'),'core_artifacts_reconstructed':len(CORE),'free_term_commands':'PASS','independent_outcomes_bound':4774,'full_independent_replay_performed':a.full,'recorded_full_independent_replay':'PASS','scope':'Exact construction and finite/symbolic proof-premise checks; the mathematical calibration is separately identified. No completed Lean endpoint claimed.'}
  if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps(result,indent=2))
if __name__=='__main__':main()
