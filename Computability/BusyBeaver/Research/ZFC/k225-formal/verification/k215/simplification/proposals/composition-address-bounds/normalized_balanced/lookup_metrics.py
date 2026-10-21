#!/usr/bin/env python3
"""Replay the independent constructor-visit census for the exact normalized data."""
import json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
E=[tuple(map(int,r)) for r in re.findall(r'\((\d+)%positive,(\d+)%positive,(\d+)%N,(\d+)%N\)',(ROOT/'NormalizedCert215.v').read_text())]
if len(E)!=1426:raise SystemExit('Wrong certificate length')
# The separately kernel-checked LookupCost215 classifies the actual tsite results.
# For these exact serialized entries, row19 is the unique halt and has successors0,0.
if [i for i,x in enumerate(E) if x[2:]==(0,0)]!=[19]:raise SystemExit('Changed halt-row encoding')
def depth(n,j):
 if n==1:return 1
 k=n//2
 return 1+(depth(k,j) if j<k else depth(n-k,j-k))
refs=[0]+[v for _,_,j,k in E if (j,k)!=(0,0) for v in (j,k)]
r={'entries':len(E),'successor_queries':len(refs),'normalized_list_visits':sum(j+1 for j in refs),'normalized_tree_visits':sum(depth(len(E),j) for j in refs),'max_lookup_depth':max(depth(len(E),j) for j in refs)}
expected=json.loads((ROOT/'lookup_metrics.json').read_text())
for k,v in r.items():
 if expected[k]!=v:raise SystemExit('Metric mismatch: '+k)
print(json.dumps(r,indent=2))
