#!/usr/bin/env python3
"""Pin source-level IΣ₁ Pell/gamma interfaces and actual residue graph; no Lean."""
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
graph=json.loads(pin('research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'))
for a,s in [(pell,'theorem descent (q x k : V)'),(pell,'theorem two_le_ordinate (q x k : V)'),(first,'theorem first_ordinate_large (m tau k : V)'),(main,'theorem first_main_large_k (X Y eta zeta tau d Delta : V)'),(gamma,'theorem gamma_zero_impossible (U X Y k eta R : V)'),(rank,'theorem scalar_rank_window (q beta MC MF J F alpha : V)'),(beta,'theorem bounds (J : V) (hJ : 0<J)'),(orient,'theorem direct_main_orientation (U X Y k eta G R : V)')]:assert s in a,s
assert '(hgap : R+1 < k)' in gamma and '(hcX : X < eta+Y*k)' in gamma and '(hY : 8 ≤ Y)' in gamma
assert '(hMC : MC<beta) (hMF : MF<2*beta)' in rank and '(hgap : F+alpha<q)' in rank
r={x[0]:x for x in graph['source']}
for row in [['qm','*','n_J','beta'],['q','+',1,'qm'],['Y','*','q3','shift_s'],['E','*','n_X','Y'],['g26','+','n_X','K0'],['Bt','-','g27','shift_F'],['g54','*','U','n_gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['Dstar','+','g58','g59'],['A0','-','g38','g42'],['A1','-','g61','g65']]:assert r[row[0]]==row,row
print(json.dumps({'scope':'pinned source signatures and literal graph wiring only; source drafts unelaborated, no Lean/model endpoint','first_norm_model_descent_source':True,'exact_large_k_source_draft':True,'two_norms_large_k_source_draft':True,'gamma_narrow_source_draft':True,'rank_window_source':True,'compact_model_bounds_source':True,'actual_gamma_input_unshifted':True,'main_adjustment':'R_prime=R+E*q','graph_rows':len(graph['source']),'lean_elaboration':False},sort_keys=True,indent=2))
