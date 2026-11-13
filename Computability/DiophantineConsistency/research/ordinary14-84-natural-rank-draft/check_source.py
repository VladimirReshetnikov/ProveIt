#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
g=json.loads((D/'research/ordinary14-qcube84-probe/candidate.json').read_bytes())
def calc(v):
 v=v.copy()
 for name,op,x,y in g['source']:
  x=v[x] if isinstance(x,str) else x;y=v[y] if isinstance(y,str) else y
  v[name]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
rng=random.Random(840106)
for _ in range(200):
 v={x:rng.randint(1,5) for x in g['witnesses']};p={x:rng.randint(0,5) for x in g['fixed_numerals']};q=1+v['J']*p['beta'];v['F']=rng.randint(0,q);z=calc(v|p)
 rank=(v['alpha']+(q-v['F'])*v['J']*p['beta'])*(q*q-1)+v['J']*(p['MC']+p['MF']*q)
 assert z['R']==rank and q>=1 and v['F']<=q and rank>=0
s=(P/'NaturalRank.lean').read_text()
for t in ('P72Root.ι_tsub hF','P72Root.ι_tsub hq2','gap_of_84_zero','hMC','hMF','le_mul_of_one_le_right'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
p=D/'research/ordinary14-84-guard-gap-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'NaturalRank.lean',p/'GuardGap.lean',D/'Lean/DiophantineConsistency/Compact44/P72Root.lean']
print(json.dumps({'scope':'source inventory, finite rank controls and guard-draft receipt replay; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
