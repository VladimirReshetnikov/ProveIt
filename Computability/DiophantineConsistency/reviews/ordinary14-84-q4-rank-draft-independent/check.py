#!/usr/bin/env python3
"""Independent q⁴ source and factor-three controls; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-q4-rank-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'Q4Rank.lean','2e57f850c02ce0511c13e9965c7281e8e0f9b63f64c50a9803cc01561969bae6').decode()
pin(A/'check_source.py','882b3cd32c7ddd6cbb446551fe9fef7687d6cc09e9cbff2077621e0c94c43956')
receipt=pin(A/'observation.json','809d8df4e190ddb52a96644ec366533bd5696e89bf895235372f84e7f1ef6009')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-q4-rank-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='781f8d4f93a732f93920742655b9a398a5404e174602de68451f5638f39b0c95'
for path,h in {
 'ordinary14-84-positive-main-balance-draft/PositiveMainBalance.lean':'89e879da8772594d6da35d55a54512e9378812cdff526d1a5020987605febc4f',
 'ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean':'d16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e',
}.items():pin(D/'research'/path,h)
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)',
 '(hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'q^4∣magnitude (R+1,AuxGraphNormClientDraft.k v)',
 'have hY : q^3∣Y','have hU : U=q^5*v 7',
 'q4_from_modified_balance q Y X R k U (v 7) (X+a*c) d (v 12)',
 'hq hY hU hbal\''):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-positive-main-balance-draft-independent','ordinary14-modified-carrier-model-facts-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for q in range(1,9):
 for X in range(4):
  for s in (1,2,3):
   Y=q**3*s;U=Y*q*q;H=3+4*Y*(X+1)
   assert U==q**5*s
   for T in range(-400,401):
    if H*T%q**5==0:
     assert T%q**4==0;cases+=1
q=3;X=2;Y=q**3;H=3+4*Y*(X+1);T=q**4
assert H*T%q**5==0 and T%q**4==0 and T%q**5!=0
print(json.dumps({'scope':'source and finite factor-three controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'divisibility_cases':cases,
 'q3_q4_sharp':True},sort_keys=True,indent=2))
