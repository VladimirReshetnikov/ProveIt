#!/usr/bin/env python3
"""Finite ledger scan of the nine certified positions and three proven tails."""
from pathlib import Path
import json
from build_nine import build
ROOT=Path(__file__).resolve().parent

def main():
 out=[]
 for p in sorted((ROOT.parent/'packing').glob('CERTIFICATE*.json')):
  data=json.loads(p.read_text());modes=['horner','rows','sum']
  if min(r['target_exponent']for r in data['rows'])>=2*data['maximum_weight']:modes.append('shared')
  for maj in ['simple64','support2048','quotient2048']:
   objs=[build(p,mode,True,maj)for mode in modes];best=min(objs,key=lambda o:o['total_operations'])
   out.append(dict(certificate=p.name,majorant=maj,encoding=best['encoding'],operations=best['total_operations'],degree=best['degree']))
 frontier=[x for x in out if not any(y['operations']<=x['operations']and y['degree']<=x['degree']and(y['operations'],y['degree'])!=(x['operations'],x['degree'])for y in out)]
 frontier.sort(key=lambda x:x['operations']);(ROOT/'SEARCH_METRICS.json').write_text(json.dumps(dict(candidates=out,frontier=frontier),indent=2)+'\n');print(json.dumps(frontier,indent=2))
if __name__=='__main__':main()
