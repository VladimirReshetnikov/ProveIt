#!/usr/bin/env python3
"""Independent four-attachment symmetry, integer-face and pruning audit.
No production module imports. Rebuilds every action, every mask orbit, component
rank bounds, invariant support arrays and the exact outstanding-gap task set.
"""
from pathlib import Path
from itertools import permutations
from collections import Counter
from functools import lru_cache
import json,hashlib,time
D=Path('/workspace/shared/preorder-gamma-degree4/four-attachment');O=Path(__file__).parent
start=time.time()
def check(ok,msg):
 if not ok:raise AssertionError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=['templates.json','a4_polynomials.jsonl','a4_gaps.jsonl','face_orbits.json','face_tasks.tsv','face_orbit_summary.json']
hashes={f:digest(D/f) for f in inputs}
T=json.loads((D/'templates.json').read_text());R=[json.loads(x) for x in (D/'a4_polynomials.jsonl').read_text().splitlines()];G=[json.loads(x) for x in (D/'a4_gaps.jsonl').read_text().splitlines()];F=json.loads((D/'face_orbits.json').read_text())
check(len(T)==len(R)==len(G)==len(F)==76,'template domain')
counts=Counter();taskset=set();all_masks=0;actions_total=0

def transform_mask(mask,action):
 out=0
 while mask:
  bit=mask&-mask;i=bit.bit_length()-1;out|=1<<action[i];mask-=bit
 return out

def permitted_actions(r):
 rows=r['core_rows'];s=r['orientation_mask'];types=r['types'];index={t:i for i,t in enumerate(types)};result=set()
 for p in permutations(range(4)):
  for dual in (0,1):
   okay=True
   for i in range(4):
    if ((s>>p[i])&1)^dual != ((s>>i)&1):okay=False;break
    for j in range(4):
     before=(rows[p[j]]>>p[i])&1 if dual else (rows[p[i]]>>p[j])&1
     if before!=((rows[i]>>j)&1):okay=False;break
    if not okay:break
   if not okay:continue
   image=[sum(1<<j for j in range(4) if t>>p[j]&1) for t in types]
   check(set(image)==set(types),'core symmetry did not preserve complete legal type set')
   result.add(tuple(index[t] for t in image))
 return result

def action_witness(r,a):
 p=a['core_permutation'];dual=a['dual'];check(sorted(p)==list(range(4)) and dual in (0,1),'bad action witness')
 rows=r['core_rows'];s=r['orientation_mask'];types=r['types'];ix={t:i for i,t in enumerate(types)}
 for i in range(4):
  check((((s>>p[i])&1)^dual)==((s>>i)&1),'orientation not fixed by claimed symmetry')
  for j in range(4):check((((rows[p[j]]>>p[i])&1) if dual else ((rows[p[i]]>>p[j])&1))==((rows[i]>>j)&1),'relation not fixed by claimed symmetry')
 image=[sum(1<<j for j in range(4) if t>>p[j]&1) for t in types]
 check(set(image)==set(types),'action fails type preservation')
 vm=tuple(ix[t] for t in image);check(vm==tuple(a['variable_map']),'variable action mismatch');return vm

def structural(r,mask):
 types=[t for i,t in enumerate(r['types']) if mask>>i&1];n=4+len(types);rows=r['core_rows'];adj=[set() for _ in range(n)]
 for i in range(4):
  for j in range(i):
   if rows[i]>>j&1 or rows[j]>>i&1:adj[i].add(j);adj[j].add(i)
 for i,t in enumerate(types,4):
  for a in range(4):
   if t>>a&1:adj[i].add(a);adj[a].add(i)
 @lru_cache(None)
 def rank(core):
  if not core:return 0
  v=min(core);rest=core-{v};return max([rank(rest)]+[1+rank(rest-{w}) for w in rest if w in adj[v]])
 unseen=set(range(n));proof=[]
 while unseen:
  root=min(unseen);component={root};todo=[root];colors={root:0};bip=True
  for v in todo:
   for w in adj[v]:
    if w not in component:component.add(w);todo.append(w);colors[w]=1-colors[v]
    elif colors[w]==colors[v]:bip=False
  unseen-=component
  active=set()
  for v in component:
   if v>=4:active |= adj[v]
  residual=frozenset((component&set(range(4)))-active);maximum=len(active)+rank(residual)
  check(maximum<=4,'component rank above four');proof.append((bip,maximum))
 return all(bip or maximum<=3 for bip,maximum in proof)

with (O/'face_orbit_coverage.jsonl').open('w') as ledger:
 for rid,(r,gamma,gaps,record) in enumerate(zip(T,R,G,F)):
  check(r['id']==gamma['id']==gaps['id']==record['id']==rid,'ID mismatch');d=len(r['types']);check(record['variables']==d,'variable dimension')
  actual=permitted_actions(r);witnesses=[action_witness(r,a) for a in record['actions']];check(len(witnesses)==len(set(witnesses)) and set(witnesses)==actual,'incomplete/repeated action set')
  check(tuple(range(d)) in actual,'missing identity');actions_total+=len(actual)
  for a in actual:
   for b in actual:check(tuple(b[a[i]] for i in range(d)) in actual,'action set not a group')
  # Verify each claimed symmetry on all five independently audited gamma arrays.
  qindex={tuple(q):j for j,q in enumerate(gamma['quota'])}
  for a in actual:
   for q,j in qindex.items():
    new=[0]*d
    for i,x in enumerate(q):new[a[i]]=x
    h=qindex[tuple(new)]
    check(all(row[j]==row[h] for row in gamma['gamma']),'symmetry fails support polynomial invariance')
  # Negative-support flags are reconstructed from the already audited complete gaps.
  negative={k:{sum(1<<i for i in range(d) if (code>>(3*i))&7) for code,c in gaps['gap'+str(k)] if c<0} for k in (2,3)}
  covered=set();orbit_by_rep={}
  for item in record['faces']:
   rep=item['representative'];check(type(rep)==int and 0<=rep<(1<<d),'bad representative')
   orbit={transform_mask(rep,a) for a in actual};check(rep==min(orbit),'representative not least orbit member');check(not(covered&orbit),'overlapping face orbits')
   members=item['members'];check(len(members)==len(orbit) and {m for m,a in members}==orbit,'incomplete orbit members')
   for member,aid in members:
    check(type(aid)==int and 0<=aid<len(witnesses),'bad action index');check(transform_mask(rep,witnesses[aid])==member,'invalid representative-to-member transport')
   check(type(item['structural'])==bool,'bad structural flag');red=structural(r,rep);check(red==item['structural'],'structural pruning mismatch')
   needed=[] if red else [k for k in (2,3) if any(support&~rep==0 for support in negative[k])]
   check(item['remaining_gaps']==needed,'outstanding gap list mismatch')
   # Reductions and gap eligibility must be invariant throughout every orbit.
   for member in orbit:
    for k in (2,3):check(any(s&~rep==0 for s in negative[k])==any(s&~member==0 for s in negative[k]),'negative-support criterion not invariant')
   for k in needed:check((rid,k,rep) not in taskset,'duplicate task');taskset.add((rid,k,rep))
   counts['orbits']+=1;counts['structural']+=red;counts['gap2']+=2 in needed;counts['gap3']+=3 in needed
   covered|=orbit;orbit_by_rep[rep]=len(orbit)
   ledger.write(json.dumps({'template':rid,'representative':rep,'orbit_size':len(orbit),'structural':red,'remaining_gaps':needed},separators=(',',':'))+'\n')
  check(covered==set(range(1<<d)),'uncovered integer population masks');check(list(orbit_by_rep)==sorted(orbit_by_rep),'unordered/duplicate representatives');all_masks+=1<<d
  if (rid+1)%10==0:print('Checked face groups',rid+1,'orbits',counts['orbits'],'elapsed',round(time.time()-start,2),flush=True)
listed=[tuple(map(int,line.split())) for line in (D/'face_tasks.tsv').read_text().splitlines()];check(len(listed)==len(set(listed)) and set(listed)==taskset,'task TSV has omissions/extras/duplicates')
summary=json.loads((D/'face_orbit_summary.json').read_text());check(dict(counts)==summary['counts'] and len(taskset)==summary['tasks'],'summary mismatch')
check(counts==Counter(orbits=24342,structural=3583,gap2=19657,gap3=19710),'unexpected counts');check(len(taskset)==39367,'task count')
check(hashes=={f:digest(D/f) for f in inputs},'input files changed during audit')
receipt={'verdict':'complete symmetry-face coverage and structural/binomial pruning approved; outstanding task positivity pending','templates':76,'distinct_actions_total':actions_total,'integer_population_masks':all_masks,'counts':dict(counts),'outstanding_gap_tasks':len(taskset),'seconds':time.time()-start,'input_sha256':hashes,'audit_code_sha256':digest(Path(__file__)),'coverage_ledger_sha256':digest(O/'face_orbit_coverage.jsonl')}
(O/'face_orbit_audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2),flush=True)
