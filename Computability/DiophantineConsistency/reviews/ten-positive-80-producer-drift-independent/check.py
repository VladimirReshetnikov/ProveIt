#!/usr/bin/env python3
"""Recheck producer record comparisons and reconstruct selected reverse graph; no Lean replay."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json
D=Path(__file__).resolve().parents[2];R=D/'reviews';S=R/'ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json'; P=R/'ten-positive-80-nine-prefix-producer-audit/observations/attempt01.json'; A=R/'ten-positive-80-adaptive-producer-drift/observations/attempt01.json'; Q=R/'ten-positive-80-nine-prefix-producer-audit/observations/survey01.json';B=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
x=j(S);p=j(P);a=j(A);q=j(Q);base=j(B);assert x['status']=='PASS' and p['closure_sha256']==sha(S)
assert len(x['project'])==1765 and len(x['outside'])==80 and len(x['fresh_headers'])==157 and not x['different_shadowed']
seen=[]
for name,case in p['cases'].items():
 rp=Path(case['receipt']);t=j(rp);assert sha(rp)==case['receipt_sha256'] and t['status']=='PASS' and t['module']==name
 assert t['output']['sha256']==case['output']['sha256']==x['project'][name]['selected']['sha256']==sha(case['output']['path'])
 assert sha(case['source'])==case['source_sha256']==t['source_sha256'] and sha(case['log'])==case['log_sha256']==t['log_sha256']
 assert set(t['direct'])==set(x['fresh_headers'][name])==set(case['direct_imports_compared'])
 for dep,info in case['direct_imports_compared'].items():
  old=t['direct'][dep]['record']['sha256'];sel=x['project'].get(dep,{}).get('selected',x['outside'].get(dep));assert sel and sha(sel['path'])==sel['sha256']
  assert info['producer_recorded']['sha256']==old and info['final_selected']==sel and info['equal_to_final']==(old==sel['sha256'])
  if old!=sel['sha256']:seen.append((name,dep,old,sel['sha256']))
assert len(p['cases'])==6 and len(seen)==9
for d in p['drifts']:assert (d['module'],d['dependency'],d['producer_recorded']['sha256'],d['final_selected']['sha256']) in seen
assert len(a['matched'])==13 and len(a['drifts'])==2
for path,digest in a['inputs'].items():assert sha(path)==digest
state=j(R/'ipra-adaptive-native-fixed-continuation-verification-peer/author-state.json');peerdata=j(R/'ipra-adaptive-native-fixed-continuation-verification-peer/receipt.json')
assert state['status']=='PASS' and peerdata['status']=='MATCHED_PASS'
extra=[]
for name,c in a['matched'].items():
 record=c['historical_record'];peer=c['peer_record'];sel=x['project'][name]['selected']
 assert record in state['records'] and peer in peerdata['matched_rows']
 assert record['object_sha256']==peer['object_sha256']==sel['sha256']==sha(sel['path']) and record['exit']==0
 for dep,info in c['direct_compared'].items():
  old=record['direct_imports'][dep]['sha256'];final=x['project'].get(dep,{}).get('selected',x['outside'].get(dep));assert final and sha(final['path'])==final['sha256']
  assert info['recorded']['sha256']==old and info['final_selected']==final and info['matches']==(old==final['sha256'])
  if old!=final['sha256']:extra.append((name,dep,old,final['sha256']))
assert len(extra)==2
for d in a['drifts']:assert (d['module'],d['dependency'],d['recorded']['sha256'],d['final_selected']['sha256']) in extra
prior=base['post_headers']['project'];graph={n:v['imports'] for n,v in prior.items() if n in x['project']};graph.update(x['fresh_headers']);assert set(graph)==set(x['project'])
reverse=defaultdict(set)
for n,imports in graph.items():
 for dep in imports:reverse[dep].add(n)
def closure(seeds):
 seen=set(seeds);todo=deque(seeds)
 while todo:
  for n in reverse[todo.popleft()]:
   if n not in seen:seen.add(n);todo.append(n)
 return seen
oldseeds={r[0] for r in seen};oldcone=closure(oldseeds);seeds=oldseeds|{r[0] for r in extra};cone=closure(seeds)
assert len(oldseeds)==5 and len(oldcone)==114 and oldcone==set(q['ordered']) and len(seeds)==7 and len(cone)==122 and cone==set(a['affected']) and 'Direct80SymbolicFixedIPRA' in cone
assert not cone&set(prior)
print('Closure: 1765 project, 157 fresh headers, 80 outside; all 11 record comparisons checked against source receipts and final selected object bytes.')
for row in seen+extra:print(*row)
print('Historical record coverage: nine-prefix cases 6; adaptive byte-matched cases 13; mismatches 9+2.')
print('Captured import graph reverse reachability: 5 seed modules -> 114; 7 seed modules -> 122; endpoint included; all 122 fresh-header.')
for file in (S,P,Q,A):print('input',file,sha(file))
print('PASS recorded mismatch/reachability comparison; not proof of unique producer, unsoundness or full ancestry.')
