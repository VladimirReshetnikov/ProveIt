#!/usr/bin/env python3
"""Bounded source and arithmetic controls; no Lean execution."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-first-norm-gap-draft/Residue90FirstNormGap.lean.src': '874a0b7254b5319e9a3f1891c700b3667854cd18a8ef1804474484fb70c93c1c', 'research/ordinary13-residue90-norm-model-draft/Residue90CompactGraphGamma.lean.src': '02c81eb303910d459890f3a001b8bdd65dccbe5f52e9bc05a24a6ddac383604b', 'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src': '11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphGamma.lean.src': '1260994075d32f7ba5f927c1444ee8ad9c954134ec0f563185c3e2b846a52d5b', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-residue90-norm-model-draft/Residue90Literal.lean.src': '00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af', 'research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src': 'efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925', 'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src': 'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a', 'research/ordinary13-residue90-norm-model-draft/check.py': '7bd046c946b2ab60d2f9157dfec9cfb98b3b4da296489b97f6d93607077dd16d', 'research/ordinary13-residue90-norm-model-draft/receipt.json': 'df70467acf2a7671cd1059407d0da5e084ac7203860774053efbeb4545b015dd', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'research/ordinary13-natural-residue-forced90-degree56/check.py': '5f55c54a80c510b7862d5459c2ffddab585d18904d9b6d66c6a0fd0446195b5c', 'research/ordinary13-natural-residue-forced90-degree56/receipt.json': '81187a393eefdd7936c8bc9a1c4ad501c171b1e9ba01fd720ac8a06815d11efc', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'research/ordinary13-residue90-norm-model-draft'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes()
s=(P/'Residue90FirstNormGap.lean.src').read_text()
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['theorem first_norm_gap','theorem first_norm_C_pos','theorem compact_gamma_of_JX','first_ring_norm p v hz','(hJ : 0<v 0)','(hbeta : 0<(p 0:V))','(hX : 1≤v 6)','mul_self_lt_mul_self']:
 assert x in s,x
rng=random.Random(1390);cases=0
for _ in range(500):
 beta=rng.randrange(1,8);J=rng.randrange(1,7);b=J*beta;q=1+b
 F=rng.randrange(1,q+4);alpha=rng.randrange(max(1,q-F),q+5)
 X=rng.randrange(0,8);K=rng.randrange(0,8);Y=rng.randrange(1,12);r=rng.randrange(1,8);eta=rng.randrange(1,8);zeta=rng.randrange(1,8)
 k=eta+zeta;m=X*Y*Y;ell=m*k;C=q-F-alpha
 assert C<=0
 Bt=C*(X+K)-F;Z=b*(ell+k+r-k*Bt)-Bt;N=1+m*(m+1)*k*k
 assert Bt<0 and Z>b*(ell+k)>=0 and (ell+k)**2>N and Z*Z>b*b*N
 cases+=1
print(json.dumps({'scope':'bounded source and finite integer controls, no Lean','pinned_files':len(pins),'integer_cases':cases,'natural_port_representation_explicit':True,'J_and_X_remain_compact_client_premises':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
