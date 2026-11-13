from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-rank-representation-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-rank-representation-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=(p/'IndependentKRankRepresentation.lean.src').read_text()
for x in ('theorem first_norm_F_lt_q','by_cases hc : 0<C','apply ι_lt_ι.mp',
          'mul_self_eq_mul_self_iff.mp hnorm\'','have hrzero : r=0',
          'theorem rank_representation','Residue90GraphNormsDraft.rank_representation p v hFq',
          '  linear_combination h'):
 assert x in s,x
old=Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src').read_text()
assert 'ι (rank p v) =\n      (ι (v 2+1)' in old
assert '(rankExpr (fun j => (p j:ℤ))).evalRing (fun j => ι (v j)) =\n      ι (Residue90GraphNormsDraft.rank p v)' in s
assert 'def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in old
assert '(hFq : v 1+1≤q p v)' in old
assert '(hFq : v 1+1≤Residue90GraphNormsDraft.q p v)' in s
# Ordered graph tree vs independently defined reconstructed expression.
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());d={name:('v',i) for i,name in enumerate(g['witnesses'])};d.update({name:('p',i) for i,name in enumerate(g['fixed_numerals'])})
for n,op,x,y in g['source']:
 d[n]=(op,d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
J,F0,A0,beta,MC,MF=(d[x] for x in ('n_J','n_F','n_alpha','beta','MC','MF'))
add=lambda x,y:('+',x,y);sub=lambda x,y:('-',x,y);mul=lambda x,y:('*',x,y)
b=mul(J,beta);q=add(1,b);F=add(F0,1);alpha=add(A0,1)
G=add(alpha,mul(sub(q,F),b));R=add(mul(G,sub(mul(q,q),1)),mul(J,add(MC,mul(MF,q))))
assert d['R']==R
for x in ('let b := J*beta','let q := 1+b','let G := alpha+(q-F)*b','G*(q*q-1)+J*(MC+MF*q)'):assert x in s
# Both algebraic branches, including d=0, over actual naturals.
count=0
for beta0 in range(1,8):
 for J0 in range(1,5):
  b0=beta0*J0;q0=b0+1
  for F0 in range(1,q0+4):
   for alpha0 in range(6):
    for d0 in range(7):
     C=q0-F0-alpha0;Bt=C*d0-F0
     for r0 in range(5):
      if (b0*r0-Bt)**2!=b0*b0:continue
      assert F0<q0
      if C<=0:assert Bt<0 and r0==0 and Bt==-b0
      count+=1
# For h: A=E, goal E=A, eq_of_eq requests E+E=A+A when given +h.
assert 1+1!=0+0 and 1+0==0+1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_checker_reproduced':True,'exact_ordered_rank_expression':True,
 'generic_helper_hypothesis_and_direction_checked':True,
 'first_norm_branch_controls':count,'rank_helper_orientation_hazard':True,
 'lean_executed':False,'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
