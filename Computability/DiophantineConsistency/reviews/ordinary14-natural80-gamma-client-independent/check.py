#!/usr/bin/env python3
"""Bounded source-interface and independent arithmetic checks; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
from collections import Counter
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
pins={
'research/ordinary14-natural80-gamma-client-draft/Natural80GammaClient.lean':'7fca431907062c8578970ae7840f37d3710f09f49c0e1e4a784ba7a94cb8288b',
'research/ordinary14-natural80-gamma-client-draft/check_source.py':'216bda7dbe6832a3445e9d9b2663846a2bd5d133b4571f01d1a966388b826c2a',
'research/ordinary14-natural80-gamma-client-draft/result.json':'06d1e7eb2120f549cca315a2042bc0aead4b2334f3c7a99353aa1142646cd454',
'research/ordinary14-natural80-gamma-premises-draft/GammaPremises.lean':'cfdbb97e748edbef9a8bf121cc3e44ac09bc91dc1e60e362b32d675df7ad7192',
'research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean':'f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7',
'research/ordinary14-natural80-main-pairs-draft/Natural80MainPairs.lean':'22350958652773aa4f900c69e99b0891b4811168d70c479a4c463bb0924028c0',
'research/ordinary14-natural80-partial74-bridge-draft/Natural80Partial74.lean':'942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16',
'research/ordinary14-natural80-jpos-model-draft/Natural80JPos.lean':'6ac50565b28ac25581504ff28c1b4d6785c61607423d0bed7c22532d6ec8e221',
'research/ordinary14-natural80-ownzero-norm-draft/Natural80OwnZeroNorm.lean':'670f8a6e7208afccde1051d72b3154990e1347cbf8d51a3845a89f56f81fcb74',
'research/ordinary14-natural80-guard-gap-draft/Natural80GuardGap.lean':'df59908f11990a28b4b788d0014757a897f2bdc1a4011772e0e825397cad43eb',
'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean':'fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4',
'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean':'29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd',
'Lean/DiophantineConsistency/Compact44/DirectMainProjection.lean':'913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956',
'Lean/DiophantineConsistency/BFS943/Direct80IndexOne.lean':'db0462fd907b629d9720106cfd9ea19fc8fa9e74e659d8286a039affbdc50761',
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16',
'Lean/DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean':'ad8a0d17ccf06c2f75ce8b095698b66f79869041ae07cf9ff0a376894b4c3968',
}
s={}
for path,digest in pins.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;s[Path(path).name]=b.decode()
def sig(file,name):
 m=re.search(r'\btheorem\s+'+re.escape(name)+r'\b(.*?)(?=\s+:=\s*by\b)',s[file],re.S);assert m,(file,name)
 return re.sub(r'\s+',' ',m.group(1)).strip()
client=s['Natural80GammaClient.lean']
h=sig('Natural80GammaClient.lean','gamma_pos_of_80_zero')
for tok in ('(hbeta : (p 0 : DiffRing V)=ι beta)','(hK : (p 1 : DiffRing V)=ι K)', '(hMC : (p 2 : DiffRing V)=ι MC)', '(hMF : (p 3 : DiffRing V)=ι MF)', '(hb : 0<beta)', '(hKpos : 0<K)', '(hMCbound : MC<beta)', '(hMFbound : MF<2*beta)', '(hz : InternalZero (P80NaturalForcedGamma.graph p).output v)', ': 0<v 12'):
 assert tok in h,tok
for tok in ('0<v 12','0 < v 12','MC>0','MF>0','46≤beta','46 ≤ beta'):
 # gamma positivity occurs only as the conclusion, not as a premise.
 assert tok not in h.split(') : 0<v 12')[0],tok
for tok in ('Natural80JPosDraft.J_pos_of_zero','m_at_least_two beta u hb hJ hw hs',
 'radix_bounds beta u hb hJ hw hs','gap_of_80_zero p beta K v hbeta hK hb hKpos hz',
 'units_of_80_zero p beta K v hbeta hK hb hKpos hz','norm_of_80_zero p beta K MC MF v hbeta hK hMC hMF hb hKpos hz',
 'direct_main_orientation (scale beta u) (X beta u) (Y beta u)',
 'large_ordinate_of_two_norms (m beta u) (u 8) (k u) (u 9) (u 10)',
 'ArithmeticAdaptiveRankWindow2011.scalar_rank_window','hMCbound hMFbound hqeq hgap',
 'narrow_inequalities (q beta u) (X beta u) (Y beta u) (k u)',
 'have hgammaU : u 12=0', 'gamma_zero_impossible (scale beta u)',
 '#print axioms DiophantineConsistency.Natural80GammaClientDraft.radix_bounds',
 '#print axioms DiophantineConsistency.Natural80GammaClientDraft.gamma_pos_of_80_zero'):
 assert tok in client,tok
r=sig('Natural80GammaClient.lean','radix_bounds')
for tok in ('(hb : 0<beta)', '(hJ : 0<u 0)', '(hw : 0<u 6)', '(hs : 0<u 7)', '2≤q beta u', '(q beta u)^3≤Y beta u', '8≤Y beta u','0<scale beta u'):assert tok in r,tok
n=sig('DirectMainNorm.lean','direct_main_orientation')
for tok in ('(hU : 0<U)','(hY : 8≤Y)','(hk : 0<k)','(hnorm :','U*G','m*m=1+(H+a*a)*(c*c)'):assert tok in n,tok
assert '0<G' not in n and '0 < G' not in n
k=sig('GammaPremises.lean','large_ordinate_of_two_norms')
for tok in ('(hm : 0<m)', '(heta : 0<eta)', '(hzeta : 0<zeta)', '(hY : 1≤Y)', '(hk : k=eta+zeta)', '(hfirst :', '(hmain :', '8*m+4≤k'):assert tok in k,tok
for tok in ('ArithmeticPellClassification.solution_index a d c hmain\'',
            'Direct80IndexOne.impossible Y (a+1) 0 eta zeta j',
            'positive_parameter_solution m tau k hm hfirst',
            'first_ordinate_lower m n k hm hn2 hcoord'):
 assert tok in s['GammaPremises.lean'],tok
n=sig('GammaPremises.lean','narrow_inequalities')
for tok in ('(hq : 2≤q)', '(hX : q≤X)', '(hY : q^3≤Y)', '(heta : 0<eta)', '(hk : 8*(X*Y*Y)+4≤k)', '(hR : R+q^3+q+1≤q^4)', 'R+1<k ∧ X<eta+Y*k'):assert tok in n,tok
n=sig('GammaZeroNarrow.lean','gamma_zero_impossible')
for tok in ('(hU : 0 < U)', '(hY : 8 ≤ Y)', '(hk : 0 < k)', '(hgap : R+1 < k)', '(hcX : X < eta+Y*k)', 'U*(0:V)', ': False'):assert tok in n,tok
assert 'direct_main_orientation U X Y k eta (0:V) R hU hY hk hnorm' in s['GammaZeroNarrow.lean']
rank=sig('ArithmeticAdaptiveRankWindow2011.lean','scalar_rank_window')
for tok in ('(hbeta : 0<beta)', '(hJ : 0<J)', '(hF : 0<F)', '(halpha : 0<alpha)', '(hMC : MC<beta)', '(hMF : MF<2*beta)', '(hq : q=beta*J+1)', '(hgap : F+alpha<q)', '+q^3+q+1≤q^4'):assert tok in rank,tok
for file,name in [('Natural80JPos.lean','J_pos_of_zero'),('Natural80OwnZeroNorm.lean','units_of_80_zero'),('Natural80GuardGap.lean','gap_of_80_zero'),('Natural80MainPairs.lean','norm_of_80_zero')]:
 assert '0<v 12' not in sig(file,name) and '0 < v 12' not in sig(file,name)
assert 'j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12' in s['Natural80Partial74.lean']
for tok in ('def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta', 'def X (beta : V) (v : Fin 14 → V) : V := q beta v*v 6', 'def Y (beta : V) (v : Fin 14 → V) : V := (q beta v*(q beta v*q beta v))*v 7', 'def m (beta : V) (v : Fin 14 → V) : V := X beta v*Y beta v*Y beta v', 'def k (v : Fin 14 → V) : V := v 9+v 10'):assert tok in s['FirstFactor74.lean']
# Verify the three exact rearrangements used for the two norms and rank.
def v(x):return {(x,):1}
def c(x):return {():x} if x else {}
def add(x,y):
 z=dict(x)
 for mon,a in y.items():z[mon]=z.get(mon,0)+a
 return {mon:a for mon,a in z.items() if a}
def sub(x,y):return add(x,{mon:-a for mon,a in y.items()})
def mul(x,y):
 z={}
 for a,xv in x.items():
  for b,yv in y.items():
   mon=tuple(sorted(a+b));z[mon]=z.get(mon,0)+xv*yv
 return {mon:a for mon,a in z.items() if a}
one=c(1);m,k,a,J,b,F,alpha,MC,MF=map(v,('m','k','a','J','b','F','alpha','MC','MF'))
assert add(mul(mul(m,k),add(mul(m,k),k)),one)==add(one,mul(mul(m,add(m,one)),mul(k,k)))
assert add(add(c(3),mul(c(4),a)),mul(a,a))==mul(add(a,one),add(a,c(3)))
q=add(one,mul(J,b));qF=sub(q,F);q2minus=sub(mul(q,q),one)
left=add(mul(add(alpha,mul(qF,mul(J,b))),q2minus),mul(J,add(MC,mul(MF,q))))
right=add(mul(add(mul(sub(q,one),qF),alpha),q2minus),mul(add(MC,mul(q,MF)),J))
assert left==right
# Independent bounded boundary controls for radix/rank, and first-Pell recurrence.
rank_cases=0
for beta in range(1,5):
 for J in range(1,4):
  q=beta*J+1
  for F in range(1,q):
   for alpha in range(1,q-F):
    for MC in range(beta):
     for MF in range(2*beta):
      R=(alpha+(q-F)*J*beta)*(q*q-1)+J*(MC+MF*q)
      assert 24<=R and R+q**3+q+1<=q**4
      rank_cases+=1
assert rank_cases>0
narrow_cases=0
for q in range(2,10):
 for X in (q,q+1,2*q):
  for Y in (q**3,q**3+1):
   for eta in (1,2):
    R=q**4-q**3-q-1
    assert R>=0
    k=8*X*Y*Y+4
    assert R+q**3+q+1<=q**4 and R+1<k and X<eta+Y*k
    narrow_cases+=1
pell_cases=0
for m in range(1,9):
 B=2*(m-1)+1;delta=(B+1)*(B+3);x,y=1,0
 for n in range(7):
  k=2*y;assert x*x==1+m*(m+1)*k*k
  if n==0:assert k==0
  if n==1:assert k==2
  if n>=2:assert 8*m+4<=k
  x,y=(B+2)*x+delta*y,x+(B+2)*y
  pell_cases+=1
# Test finite fact-level gamma-zero inputs independently of any graph witness.
gamma_cases=0
for U in range(1,4):
 for X in range(4):
  for Y in range(8,11):
   for k in range(2,16):
    for eta in range(3):
     for R in range(k-1):
      A=X*Y+Y; C=eta+Y*k; H=3+4*A
      assert X<C and R+1<k
      P=U*(X+A*C)+H*(R+1);N=H*k
      assert P>N and (P-N)**2 != U*U*(1+(H+A*A)*C*C)
      gamma_cases+=1
print(json.dumps({'scope':'bounded source signatures, exact algebra and finite controls only; no Lean elaboration or model/iPRA theorem','pinned_files':len(pins),'exact_algebraic_rearrangements':3,'radix_rank_cases':rank_cases,'narrow_boundary_cases':narrow_cases,'first_pell_recurrence_cases':pell_cases,'gamma_zero_cases':gamma_cases,'gamma_positive_as_premise':False,'axiom_reports_executed':False},sort_keys=True,indent=2))
