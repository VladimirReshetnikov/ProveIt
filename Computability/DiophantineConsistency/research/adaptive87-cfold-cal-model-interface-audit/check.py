#!/usr/bin/env python3
"""Pinned bounded source interface inventory; does not execute Lean."""
import hashlib,json,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
pins=json.loads((D/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h,p
checks={
'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean':['theorem scaled_quotient (m z n : V) (hm : 0<m)'],
'Lean/DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean':['theorem main_parts_positive (U X Y k eta gamma q R : V)','(hU : 0<U) (hY : 8≤Y) (hk : 0<k)'],
'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean':['theorem oriented_scaled_norm (U P N C : V) (hU : 0<U) (hPN : N<P)'],
'Lean/DiophantineConsistency/ArithmeticAdaptiveMainCongruence2011.lean':['def MainCongruence (p : Fin 4 → ℕ) (v : Fin 13 → V)','H*(E*q+R+1)+q^5*(s*(v 6+a*c+H*v 12)) = H*k+q^5*(s*main)'],
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankCongruence2011.lean':['theorem rank_congruence_of_main (p : Fin 4 → ℕ) (v : Fin 13 → V)','(hmain : MainCongruence p v) : RankCongruence p v'],
'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorThree2011.lean':['theorem cancel_factor_three (q Y X t : V) (hq : 0<q)','(hY : q^3∣Y) (hd : q^5∣(3+4*Y*(X+1))*t) : q^4∣t'],
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':['theorem scalar_rank_window (q beta MC MF J F alpha : V)','(hgap : F+alpha<q)'],
'research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src':['theorem early_index_of_natural_norm (q X Y k R tau s : V)','(hcong : q^4 ∣ magnitude (R+1,k))','k=2*n+4*Q*w'],
'Lean/DiophantineConsistency/Compact44/P72Exact.lean':["theorem indices_ordinary (q X Y k R g c a y0 i' f T u n s μ m η : V)","(hks : k = 2 * n + 4 * ((X * Y) * Y) * s)",'13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1'],
'research/ordinary13-residue-three-projection-model-draft/ResidueThreeProjection.lean.src':['theorem q_dvd_threeX (q X Y c k R gamma main s w : V)',': q∣3*X'],
'research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src':['theorem growth (q X Y R n k c eta zeta : V)','(hindex : 2*n=R+1)'],
'research/ordinary13-residue-qbalance-graph-draft/ResidueQBalance.lean.src':['theorem q_balance (q X Y c k R gamma main s w : V)','q*(main+H*W)=q*(X+a*c+H*gamma)+H*X'],
'research/ordinary13-positive84-power-model-draft/Positive84OrientedPower.lean.src':['theorem power_of_oriented_balance (q X Y R c main gamma W : V)',': X=Exp.exp R'],
'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':['theorem power_bound (X Y r k c eta zeta : V)','theorem projection_quotient (a t : V)'],
'Lean/DiophantineConsistency/CurrentMasks2011.lean':['theorem beta_pos : 0 < beta','theorem lowPort_lt : lowPort < beta','theorem highPort_lt : highPort < beta'],
'../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/Exponential/Exp.lean':['lemma exp_even (a : V) : Exp.exp (2 * a) = (Exp.exp a)^2','lemma lt_exp (a : V) : a < Exp.exp a','lemma exp_monotone_le {a b : V}']}
for p,ts in checks.items():
 t=(R/p).read_text()
 for x in ts:assert x in t,(p,x)
print(json.dumps({'pinned_sources':len(pins),'checked_source_files':len(checks),'checks':'exact textual interface markers and source hashes only','status':'bounded source inventory, not Lean elaboration or proof','lean_executed':False},sort_keys=True,indent=2))
