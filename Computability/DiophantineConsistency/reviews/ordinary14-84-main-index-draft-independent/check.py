#!/usr/bin/env python3
"""Independent main-index source and Pell controls; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-main-index-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'MainIndex.lean','fb9fa47c9d358e5bfe0fbd22f843172bd6df47d71ada1584e20ec68aa4147e75').decode()
pin(A/'check_source.py','98af41c0ab7f47560c4d92a4f960942e5fc5302b8c6137b405461f33ab624c0f')
receipt=pin(A/'observation.json','4f95d1b1e751411a90b811b89eb9af25fccd21f31a45b9a9af004d43fb2aded2')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-main-index-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='9493ce9b75ec48a50eec387606a2fb0d9dac69b8babeaeb909583813b2f6c12d'
pin(D/'research/ordinary14-84-positive-main-balance-draft/PositiveMainBalance.lean','89e879da8772594d6da35d55a54512e9378812cdff526d1a5020987605febc4f')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellClassification.lean','77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean','63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16')
for f in ('(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
 '(hK : (p 1 : DiffRing V)=ι K) (hMC : (p 2 : DiffRing V)=ι MC)',
 '(hMF : (p 3 : DiffRing V)=ι MF) (hv : ∀ j, 0<v j)',
 '(hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '∃ d m : V, m≤c ∧ xcoord m a=d ∧ ycoord m a=c',
 'obtain ⟨d,hn,hbal⟩ := PositiveMainBalance84Draft.norm_and_balance',
 'ArithmeticPellClassification.solution_index a d c hnorm',
 'exact ⟨d,m,hm,hx,hy,hnorm,hbal⟩'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-positive-main-balance-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0
for a in range(25):
 delta=(a+1)*(a+3);assert delta==3+4*a+a*a
 d,c=1,0
 for m in range(7):
  assert m<=c and d*d==1+delta*c*c
  d,c=(a+2)*d+delta*c,d+(a+2)*c
  cases+=1
print(json.dumps({'scope':'source and finite Pell controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'pell_controls':cases,
 'zero_index_included':True},sort_keys=True,indent=2))
