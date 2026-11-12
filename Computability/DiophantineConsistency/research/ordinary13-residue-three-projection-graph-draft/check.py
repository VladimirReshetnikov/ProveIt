#!/usr/bin/env python3
"""Bounded source/sign controls, not a Lean proof."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-three-projection-graph-draft/ResidueThreeProjectionGraph.lean.src': '589fb5cd96875a7ee9728035c8ca49bf3406336c8c9362eebd112d2d6e3e3f7b', 'research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src': 'd4c30dc20ef93cbcad180d4ba350d77d0c0534e8ef485254509a9c1604026cf2', 'research/ordinary13-residue-three-projection-model-draft/check.py': '814f4ebeac311f1f2df7bf2c60717edfc10f25768a1947de0691ad10e807681e', 'research/ordinary13-residue-three-projection-model-draft/receipt.json': '394e0861f7d66cc45269b4a0ed0aa350c2658abe9084871fd20db4dd9adcff8f', 'research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src': '169c4e604a573fa1da69ca5d642d9d9de4b125515badb88f67b17f78b24601f1', 'research/ordinary13-residue-aux-bounds-adapter-draft/check.py': '5b3c427a150d0f5050314f5cd5e4a4a044fd0b1cd4377e4df6d5083d25316e3d', 'research/ordinary13-residue-aux-bounds-adapter-draft/receipt.json': '6b1b0f99fc9b6d0980004053abbc5ec68dfb98719222e5e0fa0631302b897bb2', 'research/ordinary13-residue-main-congruence-model-draft/ResidueMainCongruence.lean.src': 'c92cbbca34371870b01f03042de0a4a024bd56a6175d909c43b6887736700ce8', 'research/ordinary13-residue-main-congruence-model-draft/check.py': 'be56af156340a50b859237b4efd8ce50c209a5114869f16eaf0dd5692cb509bc', 'research/ordinary13-residue-main-congruence-model-draft/receipt.json': 'ac2ce7760b3fcc5448f507b19cb7a0620d0ae113500f624b6893e517dac4e168', 'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean': '29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue-three-projection-model-draft','ordinary13-residue-aux-bounds-adapter-draft','ordinary13-residue-main-congruence-model-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
s=(P/'ResidueThreeProjectionGraph.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['actual_main_balance','DirectMainNorm.direct_main_orientation','rank p v+v 6*Y p v*q p v','linear_combination -hbalance','q_dvd_threeX_of_graph','exact_indices_of_graph','(hgap :','(hwindow :','q_dvd_threeX']:
 assert x in s,x
assert '⟨_,n,w,_,_,_,_,_,_,_,heq,_,hks⟩' in s
rng=random.Random(139003);cases=0
for _ in range(1000):
 U,H,k,X,a,c,gamma,Y,q,R,main=[rng.randrange(-9,10) for _ in range(11)]
 P=U*(X+a*c)+H*(U*gamma+(R+X*Y*q)+1);N=H*k
 desired=U*main+H*k-U*(X+a*c)-H*(U*gamma+X*Y*q+R+1)
 assert desired==-(P-N-U*main);cases+=1
print(json.dumps({'scope':'bounded source and oriented-balance controls, no Lean','pinned_files':len(pins),'finite_balance_cases':cases,'q_divides_3X_only':True,'fixed_port_and_endpoint_open':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
