#!/usr/bin/env python3
"""Check recorded witness scores and words without restarting a search."""
if not __debug__:
    raise RuntimeError('Verification requires Python without -O or -OO.')
from pathlib import Path
import json
import ax_association_search as s
HERE=Path(__file__).resolve().parent

def word(t):
 if t in('node60','node61'):return word(s.RAW[t])
 if not s.l.isnode(t):return(t,)
 return word(t[0])+word(t[1])

def main():
 records=json.loads((HERE/'provenance.json').read_text())['recorded_runs'];checked=[]
 for r in records:
  name=r['name'];receipt=json.loads((HERE/'recorded'/f'{name}.receipt.json').read_text())
  assert receipt['seed']==r['seed']and receipt['max_zero']==r['max_zero']
  assert receipt['trials']==r['recorded_attempts']and receipt['best_effective_ax']==r['best_effective_cost']
  assert r['seconds_budget']<=receipt['seconds']<r['seconds_budget']+2
  path=HERE/'recorded'/f'{name}.best.json';data=json.loads(path.read_text());t=s.l.read_grammar(path)
  recomputed=s.cost_data(t)
  assert json.loads(json.dumps(recomputed))==data['search']['cost']
  initial=s.l.read_grammar(HERE/'diagonal191.grammar.json')if name.startswith('diagonal')else s.original()
  assert word(t)==word(initial)
  effective,n,folds,(height,left,zero),bad,entry_bad=recomputed
  assert zero<=r['max_zero']and not entry_bad and height<=42
  checked.append({'name':name,'recorded_attempts':receipt['trials'],'recorded_seconds':receipt['seconds'],'cost':effective,'new_readers':n,'potential_folds':folds,'word_length':len(word(t)),'max_zero':zero,'word_preserved':True})
 print(json.dumps({'result':'PASS','search_restarted':False,'recorded_witnesses':checked,'scope':'Recorded witness scoring and source-word checks, not literal-machine verification or independent reconstruction of historical trial counts.'},indent=2))
if __name__=='__main__':main()
