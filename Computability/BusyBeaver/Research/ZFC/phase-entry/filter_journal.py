#!/usr/bin/env python3
"""Select old degree1 recipes whose first stop is an excluded source guard."""
from pathlib import Path
from collections import Counter
import gzip,json,hashlib
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
if not __debug__:parser.error('Keep assertions enabled')
ROOT=args.repo.resolve();OUT=args.output.resolve()
if OUT==ROOT or ROOT in OUT.parents:parser.error('External scratch output required')
OUT.mkdir(parents=True,exist_ok=True)
p=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/50-terms-machine_experiments-entry_degree1.jsonl.gz'
excluded={8202,8203,8204,8358,8359,8360}
hits=[];hist=Counter();total=0
with gzip.open(p,'rt') as f:
 for line in f:
  x=json.loads(line);total+=1
  if x.get('outcome')=='prune':
   hist[x['first_failure_case']]+=1
   if x['first_failure_case'] in excluded:hits.append(x)
assert total==132179 and sum(hist.values())==132048
assert len(hits)==3 and all(x['completions']==1 for x in hits)
r={'source':str(p),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'journal_rows':total,'first_failure_histogram':dict(hist),'excluded_cases':sorted(excluded),'phase_unlocked_recipes':hits,'phase_unlocked_recipe_count':len(hits)}
(OUT/'journal-filter.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'journal_rows':total,'phase_unlocked':len(hits),'by_deleted':dict(Counter(x['deleted_state'] for x in hits))},indent=2))
