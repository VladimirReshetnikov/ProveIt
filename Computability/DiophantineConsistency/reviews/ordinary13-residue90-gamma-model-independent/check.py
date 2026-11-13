#!/usr/bin/env python3
"""Independent source audit of enlarged gap and fact-level gamma client."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-gamma-model-draft/Residue90GammaModel.lean.src','7a9f8a98e28bad9f94a8dccdab57d16753058f7eb55144fb5282f51a19314af7')
pin('research/ordinary13-residue90-gamma-model-draft/receipt.json','956af5033043daa00444ccdecbc2a639be6728d39842e559062be9ec274ea5ef')
pin('reviews/ordinary13-residue90-gamma-route-independent/result.json','fca07581781e7842058b28f0a0d4c40e3f1a68919398426ba719416508bb8ca8')
g=json.loads(pin('research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'))
fm=pin('research/ordinary14-first-main-large-k-draft/FirstMainLargeK.lean','65d2de66fec31d7cc2d79687acc353638e864077c561af12829d93007d430e61')
ng=pin('research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean','f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7')
for x in ['(hq : 2≤q) (hX : 1≤X) (hY : q^3≤Y) (heta : 0<eta)','(hk : 8*(X*Y*Y)+4≤k) (hR : R+q^3+q+1≤q^4)','(R+X*Y*q)+1<k ∧ X<eta+Y*k','mul_le_mul hqY hY (Arithmetic.zero_le (q^3)) (Arithmetic.zero_le Y)','(hcarrier : gamma=0 →','magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))','FirstMainLargeKDraft.first_main_large_k X Y eta zeta tau d Delta','have hklarge\' : 8*(X*Y*Y)+4≤eta+zeta','simpa only [mul_assoc] using hklarge','GammaZeroNarrowDraft.gamma_zero_impossible U X Y (eta+zeta) eta (R+X*Y*q)','hU hY8 hkpos hgap hc (hcarrier hg)']:assert x in s,x
assert '8*X*Y*Y+4≤eta+zeta' in fm and '(hgap : R+1 < k)' in ng and '(hcX : X < eta+Y*k)' in ng
assert '(hX : q≤X)' not in s.split('theorem enlarged_rank_gap',1)[1].split(':= by',1)[0]
for x in ['(hU : 0<U)','(hDelta : (X*Y+Y+2)*(X*Y+Y+2)=Delta+1)','(hfirst : tau*tau=1+(X*Y*Y)*(X*Y*Y+1)*(eta+zeta)*(eta+zeta))','(hmain : d*d=1+Delta*(eta+Y*(eta+zeta))*(eta+Y*(eta+zeta)))']:assert x in s,x
rows={x[0]:x for x in g['source']}
for row in [['E','*','n_X','Y'],['g55','*','E','q'],['g54','*','U','n_gamma'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59']]:assert rows[row[0]]==row
# Bounds are checked on both q>X and q<=X cases as sanity controls; proof is in README.
cases=0;qx=0
for q in range(2,8):
 for x in range(1,7):
  for y in range(q**3,q**3+3):
   R=q**4-q**3-q-1; m=x*y*y;k=8*m+4
   assert q<=y and q**4<=m and x*y*q<=m and R+1<=q**4
   assert R+x*y*q+1<=2*m<k and x<1+y*k
   cases+=1;qx+=int(q>x)
assert qx>0
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',s)
print(json.dumps({'scope':'source-level fact-cut and model-interface audit; no Lean','rank_parameter':'R+X*Y*q','explicit_hypotheses_include_first_main_norms_rank_and_signed_magnitude':True,'associativity_repair_present':True,'q_le_X_not_assumed':True,'finite_controls':cases,'finite_controls_q_greater_than_X':qx,'graph_to_fact_and_port_bindings_remain_open':True},sort_keys=True,indent=2))
