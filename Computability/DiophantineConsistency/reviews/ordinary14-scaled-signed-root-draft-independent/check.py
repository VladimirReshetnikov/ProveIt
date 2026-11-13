#!/usr/bin/env python3
"""Independent signed square source review; never invokes Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2]; A=D/'research/ordinary14-scaled-signed-root-draft'
def sha(d): return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes(); assert sha(d)==h,str(p); return d
src=pin(A/'SignedScaledRoot.lean','900ff0f8acda716fe01f96ffdd463636fae411149df172946e1c34d27ab8cadd').decode()
pin(A/'check_source.py','e6afb0f3b3f32bb84f160c3f8a84e3ec060fce049620d2075644c0f2301f8180')
receipt=pin(A/'observation.json','793e06074ef4edd5300fc208e24be3f757141b07e6bc8980c932109351b22352')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-scaled-signed-root-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='4814df281585590a2c0dd0c83359d92a4551a74882c5e3d02c1b13b8a175ce14'
for path,h in {
 'ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884',
 'ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
}.items(): pin(D/'Lean/DiophantineConsistency'/path,h)
for f in ('(hU : 0<U)','(h : Z*Z=(ι U*ι U)*ι n)',
 '∃ d : V, d*d=n ∧ (Z=ι (U*d) ∨ Z= -ι (U*d))',
 'rcases nonneg_or_nonpos Z with ⟨z,hz⟩ | ⟨z,hz⟩',
 'obtain ⟨d,hd,hn⟩ := scaled_quotient U z n hU hsq',
 'refine ⟨d,hn,Or.inl ?_⟩','refine ⟨d,hn,Or.inr ?_⟩'):
 assert f in src,f
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not run.stderr and run.stdout==receipt
positive=negative=zero=0
for U in range(1,21):
 for Z in range(-100,101):
  for n in range(31):
   if Z*Z != U*U*n: continue
   assert abs(Z)%U==0
   d=abs(Z)//U; assert d*d==n and Z in (U*d,-U*d)
   positive+=Z>0; negative+=Z<0; zero+=Z==0
assert positive and negative and zero
assert 0*0==0*0*2 and all(d*d!=2 for d in range(3))
print(json.dumps({'scope':'source and finite controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'positive':positive,'negative':negative,
 'zero':zero,'zero_scale_boundary':True},sort_keys=True,indent=2))
