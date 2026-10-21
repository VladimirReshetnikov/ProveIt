"""Owned six logically new contextual-alternate pair screen."""
from pathlib import Path
import time,json,collections
import three_cell_selectors as S
S.path=S.ROOT/'research217_review/contextual/selected/machine/k218.native.tm';S.T=S.R.table(S.path);S.states=sorted({q for q,b in S.T})
S.incoming=collections.defaultdict(list)
for(q,b),(w,d,z)in S.T.items():S.incoming[z].append((q,b,w,d))
S.markers={}
for q in S.states:
 if q==0 or not S.incoming[q]or any(d!=1 or p==0 for p,b,w,d in S.incoming[q]):continue
 if any(not S.incoming[p]or any(dd!=1 for pp,bb,ww,dd in S.incoming[p])for p,b,w,d in S.incoming[q]):continue
 S.markers[q]=sorted({(ww,w)for p,b,w,d in S.incoming[q]for pp,bb,ww,dd in S.incoming[p]})
S.pairs=json.load(open(S.OUT/'CONTEXTUAL_ALTERNATE_COMPARISON.json'))['structurally_new_history_pairs']
for pair in S.pairs:
 for q,markers in zip(pair['states'],pair['markers']):assert list(map(list,S.markers[q]))==markers
 pair['markers']=[list(map(tuple,ms))for ms in pair['markers']]
 assert S.T[pair['states'][0],pair['shared_read']]==S.T[pair['states'][1],pair['shared_read']]
S.start=time.monotonic();S.steps=0;S.CAP_STEPS=30000;S.CAP_SECS=2;S.OUTPUT_PATH=S.OUT/'CONTEXTUAL_SIX_SELECTOR_SCREEN.json'
S.main()
