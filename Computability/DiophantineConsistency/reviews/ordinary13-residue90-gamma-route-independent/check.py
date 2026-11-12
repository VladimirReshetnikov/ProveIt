#!/usr/bin/env python3
"""Bounded source audit of compact gamma route and dependency hypotheses."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
pell=pin('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5')
first=pin('research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean','f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504')
main=pin('research/ordinary14-first-main-large-k-draft/FirstMainLargeK.lean','65d2de66fec31d7cc2d79687acc353638e864077c561af12829d93007d430e61')
gamma=pin('research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean','f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7')
rank=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794')
beta=pin('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean','bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea')
orient=pin('Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean','29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd')
old=pin('research/ordinary14-natural80-gamma-premises-draft/GammaPremises.lean','cfdbb97e748edbef9a8bf121cc3e44ac09bc91dc1e60e362b32d675df7ad7192')
pin('research/ordinary13-residue90-gamma-model-route-audit/result.json','a33d898f9b86dcaa69d170f82f1f5870fd01e1dcd526a43c08e165328ab6b49a')
pin('reviews/ordinary13-natural-residue-forced90-independent/result.json','d4cfc1fa4f40cbd6e308814640151b2c954d99487889fe2c91733bd05b8bf97c')
g=json.loads(pin('research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'))
for source,frag in [(pell,'theorem descent (q x k : V)'),(pell,'theorem two_le_ordinate (q x k : V)'),(first,'theorem first_ordinate_large (m tau k : V)'),(main,'theorem first_main_large_k (X Y eta zeta tau d Delta : V)'),(gamma,'theorem gamma_zero_impossible (U X Y k eta R : V)'),(rank,'theorem scalar_rank_window (q beta MC MF J F alpha : V)'),(beta,'theorem bounds (J : V) (hJ : 0<J)'),(orient,'theorem direct_main_orientation (U X Y k eta G R : V)')]:assert frag in source
assert '(hX : q≤X)' in old and '(hgap : R+1 < k)' in gamma and '(hcX : X < eta+Y*k)' in gamma and 'magnitude (P,N)' in gamma
assert '(hMC : MC<beta) (hMF : MF<2*beta)' in rank and '(hgap : F+alpha<q)' in rank
rows={x[0]:x for x in g['source']}
for row in [['E','*','n_X','Y'],['g54','*','U','n_gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['g52','-','k','R'],['r0','-','g52',1],['shift','-','g56','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59']]:assert rows[row[0]]==row
# An explicit q>X witness demonstrates why the old q<=X lemma is inapplicable.
q,X,Y,R,k=3,1,27,10,8*1*27*27+4
assert q>X and q>=2 and Y>=q**3 and R+q**3+q+1<=q**4 and R+X*Y*q+1<k
print(json.dumps({'scope':'source signatures and exact graph mapping, no Lean','graph_rows':90,'actual_narrow_rank_parameter':'R+X*Y*q','old_narrow_requires_q_le_X':True,'counterexample_to_automatic_q_le_X':[q,X,Y,R,k],'parent_model_calibration_not_proved':True},sort_keys=True,indent=2))
