#!/usr/bin/env python3
"""Source/interface and finite recurrence sanity, not Lean verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src': '0b69fb042a913232ef9f4a92757107f60d8a590f855176134587939012b1b93b', 'reviews/ordinary13-residue82-first-index-interface-audit/check.py': '14ab92b5278c6b9d941b9cc64ca5cf838737437579c7d96b8644476579129e10', 'reviews/ordinary13-residue82-first-index-interface-audit/result.json': 'eb01dc5f085d6d8519cbd9af512d4a87bc927b7b5d738f009e36ebb98b10bcec', 'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean': '374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5', 'Lean/DiophantineConsistency/ArithmeticPellCongruences.lean': '75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1', 'Lean/DiophantineConsistency/ArithmeticAdaptiveFirstDivisibility2011.lean': 'b7d4f6e12aba5b0b814cc7111478c89b558b2f33aafa6fef6f019b8c3dbdd74c', 'Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean': 'ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'reviews/ordinary13-residue82-first-index-interface-audit'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'result.json').read_bytes()
s=(P/'ResidueFirstIndexModel.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['positive_parameter_solution Q tau k','residue_quotients n B (q^4)','residue_quotients n B (2*Q)','(hcong : q^4 ∣ magnitude (R+1,k))','(2*n)%(q^4)=R+1','k=2*n+4*Q*w']:
 assert x in s,x
assert 'core.z' not in s.split('theorem early_index_of_natural_norm',1)[1]
q=3;X=1;ss=1;Y=q**3*ss;Q=X*Y*Y;B=2*(Q-1)+1;delta=(B+1)*(B+3);x=1;y=0;cases=0
for n in range(1,26):
 x,y=(B+2)*x+delta*y,x+(B+2)*y
 if n<13:continue
 tau=x;k=2*y;R=2*n-1
 assert tau*tau==1+Q*(Q+1)*k*k
 assert R>=24 and R+q**3+q+1<=q**4 and abs(R+1-k)%(q**4)==0
 assert (2*n)%(q**4)==R+1 and R+1<=2*n<=k and (k-2*n)%(4*Q)==0
 cases+=1
print(json.dumps({'scope':'source interface and finite recurrence checks, no Lean','pinned_files':len(pins),'finite_recurrence_cases':cases,'old_core_z_not_in_theorem':True,'rank_congruence_and_graph_binding_explicit':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
