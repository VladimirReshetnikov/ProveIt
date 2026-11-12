#!/usr/bin/env python3
"""Bounded ring certificates and source pins only; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src': 'd4c30dc20ef93cbcad180d4ba350d77d0c0534e8ef485254509a9c1604026cf2', 'research/ordinary13-residue-main-congruence-model-draft/ResidueMainCongruence.lean.src': 'c92cbbca34371870b01f03042de0a4a024bd56a6175d909c43b6887736700ce8', 'research/ordinary13-residue-main-congruence-model-draft/check.py': 'be56af156340a50b859237b4efd8ce50c209a5114869f16eaf0dd5692cb509bc', 'research/ordinary13-residue-main-congruence-model-draft/receipt.json': 'ac2ce7760b3fcc5448f507b19cb7a0620d0ae113500f624b6893e517dac4e168', 'research/ordinary13-residue-aux-bounds-adapter-draft/ResidueAuxBoundsAdapter.lean.src': '4b6e7be4c6dd5aad302146018e304ae0fc8b523371b73c68707f02dfa8dd2e11', 'research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src': '169c4e604a573fa1da69ca5d642d9d9de4b125515badb88f67b17f78b24601f1', 'research/ordinary13-residue-aux-bounds-adapter-draft/check.py': '5b3c427a150d0f5050314f5cd5e4a4a044fd0b1cd4377e4df6d5083d25316e3d', 'research/ordinary13-residue-aux-bounds-adapter-draft/receipt.json': '6b1b0f99fc9b6d0980004053abbc5ec68dfb98719222e5e0fa0631302b897bb2', 'Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean': '4d764b377ae95cc13b4548ab63266cb97084a061c8c14dd9d8922ac88cbc6885', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue-main-congruence-model-draft','ordinary13-residue-aux-bounds-adapter-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
src=(P/'ResidueThreeProjection.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',src)
for x in ['theorem q_dvd_threeX','(hindex :','(hbalance :','Trace75IntegralTransport.natural_dvd_of_signed','linear_combination -hBalR+ι H*hIdxR+4*ι H*ι X*ι w*hYsq']:
 assert x in src,x
rng=random.Random(133013);cases=0
for _ in range(1000):
 q,X,Y,c,k,R,gamma,main,ss,w=[rng.randrange(-8,9) for _ in range(10)];a=X*Y+Y;H=3+4*a;U=Y*q*q;S=Y*q
 bal=U*main+H*k-U*(X+a*c)-H*(U*gamma+X*Y*q+R+1)
 idx=k-R-1-4*X*Y*Y*w;yr=Y-q*(q*q)*ss;ysq=Y*Y-U*q*ss
 assert ysq==Y*yr
 witness=main+4*H*X*q*ss*w-X-a*c-H*gamma
 target=H*X*S-U*witness
 assert target==-bal+H*idx+4*H*X*w*ysq
 Y=q*(q*q)*ss;H=3+4*(X*Y+Y);z=rng.randrange(-8,9)
 assert 3*X-q*(z-4*q*q*ss*(X+1)*X)==H*X-q*z
 cases+=1
print(json.dumps({'scope':'bounded source and signed ring controls, no Lean','pinned_files':len(pins),'finite_certificate_cases':cases,'Bezout_assumption_used':False,'q_divides_X_or_power_claimed':False,'source_sha256':hashlib.sha256(src.encode()).hexdigest()},sort_keys=True,indent=2))
