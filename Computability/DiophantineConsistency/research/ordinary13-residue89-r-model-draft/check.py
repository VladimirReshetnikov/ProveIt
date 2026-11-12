#!/usr/bin/env python3
"""Bounded signed branch/size sanity, not a Lean proof."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue89-r-model-draft/Residue89RArithmetic.lean.src': 'be421b34e6701a194c3f68806a06099e373d2d64fba4bda9134fafd0460748aa', 'research/ordinary13-natural-residue-forced89-degree56/candidate.json': 'c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a', 'research/ordinary13-natural-residue-forced89-degree56/check.py': '350537f8a3024121b139d3c4a6a9cc1b9c59d7ca080e30c58812e04b2f10f71c', 'research/ordinary13-natural-residue-forced89-degree56/receipt.json': 'beb633428beee90b6049162d9e77ae063755dcdf2c63a07283a97a2bcb12e123', 'research/ordinary13-residue-root-switch-model-audit/check.py': '2928aec8b11b2ede9bbd12537d6f143e2d91ac3cff147f2df0adc9873c2c0e47', 'research/ordinary13-residue-root-switch-model-audit/result.json': 'ffe60a4ae3c8b5228b0cde6e32f363fffdfb269670454c08b2f4ee49aa020f27', 'Lean/DiophantineConsistency/Compact44/P72Root.lean': '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,receipt in [('ordinary13-natural-residue-forced89-degree56','receipt.json'),('ordinary13-residue-root-switch-model-audit','result.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/receipt).read_bytes(),packet
s=(P/'Residue89RArithmetic.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['r_positive_of_branches','branches_of_signed_root','tau_gt_ell','P_below_m','k*(P-1)+t<ell+ell','(hK : K+1≤q^2)']:
 assert x in s,x
rng=random.Random(1389);algebra=0;size=0
for _ in range(600):
 b,P,t,ell,k,tau,z=[rng.randrange(-15,16) for _ in range(7)]
 root=z-(b*(ell+k-k*P)-P);hp=P-b*t
 for sign in (1,-1):
  hs=z-sign*b*tau
  assert root-hs-hp==b*(k*(P-1)+t-ell+sign*tau)
  algebra+=1
for q in range(2,8):
 for X in range(1,6):
  for Y in (q**3,q**3+1):
   for K in (0,q*q-1):
    for C in range(q):
     F=1;P=C*(X+K)-F;m=X*Y*Y
     if P>0:
      assert K+1<=q*q and P<m;size+=1
print(json.dumps({'scope':'bounded source and ring/size controls, no Lean','pinned_files':len(pins),'signed_branch_algebra_cases':algebra,'positive_P_size_cases':size,'kernel_bound_and_graph_extraction_explicit':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
