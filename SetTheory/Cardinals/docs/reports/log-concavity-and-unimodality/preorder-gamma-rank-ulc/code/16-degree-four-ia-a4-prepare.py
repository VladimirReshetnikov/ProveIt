from pathlib import Path
from math import comb
from itertools import combinations_with_replacement
import json,hashlib
D=Path('/workspace/shared/preorder-gamma-degree4/four-attachment');O=Path(__file__).parent
R=[json.loads(x) for x in (D/'a4_polynomials.jsonl').read_text().splitlines()];T=json.loads((D/'templates.json').read_text());P=[json.loads(x) for x in (D/'a4_gaps.jsonl').read_text().splitlines()]
assert len(R)==len(T)==len(P)==76
nq=terms=0
with (O/'representatives.txt').open('w') as f:
 for i,(r,t,p) in enumerate(zip(R,T,P)):
  assert r['id']==t['id']==p['id']==i
  for key in ['core_rows','orientation_mask','types']:assert r[key]==t[key]
  rows=r['core_rows'];assert len(rows)==4 and all(type(x)==int and 0<=x<16 and not(x>>j&1) for j,x in enumerate(rows))
  s=r['orientation_mask'];assert 0<=s<16
  ts=r['types'];d=len(ts);assert p['variables']==d and ts==sorted(set(ts)) and all(1<=v<=15 for v in ts)
  Q=list(map(tuple,r['quota']));expected=set()
  for k in range(5):
   for selected in combinations_with_replacement(range(d),k):
    q=[0]*d
    for j in selected:q[j]+=1
    expected.add(tuple(q))
  assert len(Q)==len(set(Q))==comb(d+4,4) and set(Q)==expected
  assert len(r['gamma'])==5 and all(len(g)==len(Q) for g in r['gamma'])
  assert all(type(c)==int and c>=0 for g in r['gamma'] for c in g)
  f.write(' '.join(map(str,[i,*rows,s,sum(1<<v for v in ts),d,len(Q)]))+'\n')
  for j,q in enumerate(Q):f.write(' '.join(map(str,[*q,*(r['gamma'][k][j] for k in range(5))]))+'\n')
  for k in [2,3]:
   a=p['gap'+str(k)];assert a==sorted(a) and len(a)==len({e for e,c in a})
   for code,c in a:
    assert type(code)==type(c)==int and c and 0<=code<(1<<(3*d))
    e=tuple((code>>(3*j))&7 for j in range(d));assert sum(e)<=2*k
   f.write(str(len(a))+'\n');f.write(' '.join(str(z) for pair in a for z in pair)+'\n');terms+=len(a)
  nq+=len(Q)
# Exact TSV consistency with the authoritative JSON templates.
lines=(D/'templates.tsv').read_text().splitlines();assert len(lines)==76
for t,line in zip(T,lines):assert list(map(int,line.split()))==[t['id'],*t['core_rows'],t['orientation_mask'],len(t['types']),*t['types']]
receipt={'templates':76,'quota_vectors':nq,'scalar_coefficients':5*nq,'newton_gap_terms':terms,'input_sha256':{x:hashlib.sha256((D/x).read_bytes()).hexdigest() for x in ['generate_templates.py','polynomials.cpp','templates.json','templates.tsv','a4_polynomials.jsonl','a4_gaps.jsonl']}}
(O/'preparation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
