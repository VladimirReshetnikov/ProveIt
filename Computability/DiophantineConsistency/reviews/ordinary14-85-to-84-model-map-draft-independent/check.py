#!/usr/bin/env python3
"""Independent reverse-map source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-to-84-model-map-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'ModelMap85To84.lean','8f82ad48c583b1bb6b91bf94f78a39097b0462b827cce748c148639387810368').decode()
pin(A/'check_source.py','450e6b1462ee8d333021285f4d8f8d73be69da3bc7af9e29cdb1748df9bedb47')
receipt=pin(A/'observation.json','7709c1441c6012202dc355781880ff70e3b41a15e15d98cd6179fd32eafa1217')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-to-84-model-map-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='055e082cd37e2ae93489ea2d99555eb9b6c0313bcf0074034fddb9e4802bf461'
for path,h in {
 'research/ordinary14-85-power-recovery-draft/PowerRecovery85.lean':'5bec57c11a9f364527748f75f87dfa7d256b91837c8352ab210f26c20547c129',
 'research/ordinary14-85-divides-3x-draft/Divides3X85.lean':'bd13831f6d3aa49a336cd90413a8d64ac2ea473aa4c45e71d405925760ebb5c7',
 'research/ordinary14-modified-carrier-model-facts-draft/ModifiedCarrierFacts.lean':'d16c6dca1f5bb5240db5e2b72d6d1895568c9e178c933a68e92f82b6be2be43e',
 'research/ordinary14-84-85-conditional-model-draft/ConditionalComparison.lean':'204cf248239f6a070176c407f1d8d2ddb8506afad9784e79ac5ab0a0d2638790',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveMersenne2011.lean':'c8a132e1b28bd1cf1ed76d80e953d5568ff0c77f566ad7b2b66715c8be9641ef',
}.items():pin(D/path,h)
for f in ('(hbeta : 0<beta) (hbeta46 : 46≤beta) (ht : 4≤t) (hradix : beta=Exp.exp t-1)',
 '(hMC : MC<beta) (hMF : MF<2*beta) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'PowerRecovery85Draft.power p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz',
 'Divides3X85Draft.divides_three_X p beta K MC MF v hbeta hport hK hMCcast hMFcast hMC hMF hv hz',
 'qq=(Exp.exp t-1)*v 0+1',
 'mersenne_divides_X t R qq (v 0) (v 6) ht hq hX h3',
 'map_85_to_84 p beta v hport hv hd hz'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-power-recovery-draft-independent','ordinary14-84-85-conditional-model-draft-independent','ordinary14-modified-carrier-model-facts-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=hits=maps=0
for t in range(4,10):
 beta=2**t-1
 for J in range(1,21):
  q=1+J*beta
  for R in range(21):
   X=2**R;cases+=1
   if 3*X%q==0:
    assert X%q==0;hits+=1
  for w in range(1,5):
   X=q*w
   for gamma in range(1,5):
    gp=gamma+w
    assert X//q==w and gp>w and gp-w==gamma
    maps+=1
assert hits and 3*(2**4)%3==0 and 2**4%3!=0
print(json.dumps({'scope':'source and finite Mersenne/map controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'mersenne_cases':cases,
 'divisibility_hits':hits,'positive_quotient_maps':maps},sort_keys=True,indent=2))
