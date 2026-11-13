#!/usr/bin/env python3
"""Check four recorded HA87 producers and recompute expanded closure reachability."""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,subprocess,sys
D=Path(__file__).resolve().parents[2]; R=D/'reviews';S=R/'ten-positive-80-fixed-ipra-serialized-closure/observations/attempt01/result.json';A=R/'ten-positive-80-adaptive-producer-drift/observations/attempt01.json';H=R/'ten-positive-80-ha87-producer-drift/observations/attempt01.json';B=D/'research/ordinary12-direct90-ipra-join/observations/attempt03/result.json';STATE=R/'ha87-isolated-full-author-pass/state.json'
def j(p):return json.loads(Path(p).read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
x=j(S);a=j(A);h=j(H);b=j(B);state=j(STATE);assert state['status']=='PASS' and h['status']=='COMPARED_WITH_DRIFTS'
for p,digest in h['inputs'].items():assert sha(p)==digest
assert h['author_search_path']==state['LEAN_PATH'] and len(h['records'])==4
seen=[]
for name,c in h['records'].items():
 rec=c['historical_record'];sel=x['project'][name]['selected'];assert rec in state['records'] and rec['module']==name and rec['verified'] and rec['exit']==0
 assert rec['object_sha256']==sel['sha256']==c['selected']['sha256']==sha(sel['path'])
 assert set(rec['dependency_hashes'])==set(c['direct_compared'])
 for dep,item in c['direct_compared'].items():
  final=x['project'].get(dep,{}).get('selected',x['outside'].get(dep));assert final is not None and sha(final['path'])==final['sha256']
  old=rec['dependency_hashes'][dep];assert item['recorded_sha256']==old and item['final_selected']==final and item['matches']==(old==final['sha256'])
  if old!=final['sha256']:seen.append((name,dep,old,final['sha256']))
assert len(seen)==11 and len(h['drifts'])==11
for d in h['drifts']:assert (d['module'],d['dependency'],d['recorded_sha256'],d['final_selected']['sha256']) in seen
prior=b['post_headers']['project'];graph={n:v['imports'] for n,v in prior.items() if n in x['project']};graph.update(x['fresh_headers']);assert set(graph)==set(x['project'])
rev=defaultdict(set)
for n,deps in graph.items():
 for dep in deps:rev[dep].add(n)
seeds=set(a['combined_seeds'])|{z[0] for z in seen};affected=set(seeds);q=deque(seeds)
while q:
 for n in rev[q.popleft()]:
  if n not in affected:affected.add(n);q.append(n)
assert len(seeds)==11 and len(affected)==127 and affected==set(h['affected']) and set(a['affected'])<=affected and not affected&set(prior)
subprocess.run([sys.executable,'-I','-S','-B',str(R/'ten-positive-80-producer-drift-independent/check.py')],check=True,stdout=subprocess.DEVNULL)
for row in seen:print(*row)
print('PASS four byte-matching historical records, 11 differing recorded dependencies, captured graph 122→127, 11 seeds, endpoint included:', 'Direct80SymbolicFixedIPRA' in affected)
print('input report SHA',sha(H),'state SHA',sha(STATE),'scope: historical hashes only, no unique producer or theorem-unsoundness claim')
