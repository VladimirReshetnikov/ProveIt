import json, math, hashlib, itertools
from pathlib import Path
D=Path('/workspace/shared/preorder-gamma-degree4/three-attachment')
O=Path(__file__).parent
rows=[json.loads(x) for x in (D/'a3_polynomials.jsonl').read_text().splitlines()]
assert len(rows)==6213
unique={}; aliases=[]; first=[]; quota_count=0
with (O/'representatives.txt').open('w') as f:
 for i,r in enumerate(rows):
  assert r['id']==i and len(r['core_rows'])==6
  assert all(type(x)==int and 0<=x<64 and not(x>>v&1) for v,x in enumerate(r['core_rows']))
  assert 0<=r['orientation_mask']<8
  ts=r['types']; assert ts==sorted(set(ts)) and all(1<=t<=7 for t in ts)
  d=len(ts); Q=[tuple(q) for q in r['quota']]
  expected={q for q in itertools.product(range(4),repeat=d) if sum(q)<=3}
  assert len(Q)==len(set(Q))==math.comb(d+3,3) and set(Q)==expected
  assert len(r['gamma'])==5 and all(len(g)==len(Q) for g in r['gamma'])
  assert all(type(c)==int and c>=0 for g in r['gamma'] for c in g)
  L=sum(1<<t for t in ts)
  f.write(' '.join(map(str,[i,*r['core_rows'],r['orientation_mask'],L,d,len(Q)]))+'\n')
  for j,q in enumerate(Q):f.write(' '.join(map(str,[*q,*(r['gamma'][k][j] for k in range(5))]))+'\n')
  key=(tuple(Q),tuple(map(tuple,r['gamma'])))
  if key not in unique:unique[key]=len(unique); first.append(i)
  aliases.append(unique[key]); quota_count+=len(Q)
assert len(unique)==3437
assert aliases==json.loads((D/'a3_gamma_aliases.json').read_text())
U=[json.loads(x) for x in (D/'a3_unique_gamma.jsonl').read_text().splitlines()]
assert len(U)==len(first)
for i,(u,j) in enumerate(zip(U,first)):
 assert u['id']==i and u['template_id']==j
 for k in ('core_rows','orientation_mask','types','quota','gamma'):assert u[k]==rows[j][k]
receipt={'templates':len(rows),'unique_gamma':len(unique),'quota_vectors':quota_count,'alias_and_representative_comparison':'passed','sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [D/'enumerate.cpp',D/'canonical.inc',D/'a3_polynomials.jsonl',D/'a3_gamma_aliases.json',D/'a3_unique_gamma.jsonl']}}
(O/'preparation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
