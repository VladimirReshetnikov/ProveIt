import IPRADerivations.Analysis.Logarithm.FiniteSeries.ComplexLogarithmCauchy
import IPRADerivations.Analysis.Series.ReciprocalSquares.ReciprocalSquareTail
import IPRADerivations.Probability.TowerCommonDen

/-!
# Actual finite canonical Gamma factors and their rational tails

Packet `analysis/gamma_ipra`, Section 2, finite arithmetic behind (C3)
and (C6). The finite factor is
`-z²/(2N²) + Σ_{j=3}^{L+2} (-1)^(j+1)z^j/(jN^j)`.
The signed quadratic term is added to the existing actual cubic Taylor
recursor. All cutoffs, disk radii, Gaussian numerator codes and divisors
are internal. No logarithm identity or Gamma error certificate is assumed.

These are finite rational estimates and a Cauchy modulus for the power
series. Identification with the analytic local logarithm, its exponential
identity, and construction of the full Euler/Gamma approximants are separate
adapters, not conclusions of this module.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Analysis.GammaCanonicalFactors

open_ipra
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im add mul scale zeroCode normSq bounded series bounded_scale bounded_add bounded_neg
    bounded_mul bounded_mono bounded_series normSq_eval eval_re_code eval_im_code)
open LeanProofs.IPRA.Analysis.LogarithmRemainder
  (numerator denominator denominator_positive three finite_taylor_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Actual signed Gaussian numerator of the quadratic-and-higher local factor. -/
def factorNumerator (z N L : PTm n) : PTm n :=
  add (ComplexLogarithmRemainder.neg (scale (denominator N L) (mul z z)))
    (scale (two*N*N) (series z N L))

def factorDenominator (N L : PTm n) : PTm n := two*N*N*denominator N L

/-- A computed natural majorant of the Gaussian numerator, not a supplied bound. -/
def factorRadius (R N L : PTm n) : PTm n :=
  denominator N L*R*R+two*N*N*numerator R N L

ipra_subst factorNumerator

ipra_subst factorDenominator

ipra_subst factorRadius

private alias cancel_positive := Common.mul_cancel_le

theorem factorDenominator_positive (N L : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (factorDenominator N L) := by
  have twoPos : Γ ⊢[PRAAx] le one two := le_of_eq_add (d := one) (by ipra_ring)
  exact le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (le_mul_mono (le_mul_mono twoPos hN) hN) (denominator_positive N L hN))

/-- Numerator domination is proved from the exact Taylor recursor. -/
theorem factor_domination (z N R L : PTm n) (hz : Γ ⊢[PRAAx] bounded z R) :
    Γ ⊢[PRAAx] bounded (factorNumerator z N L) (factorRadius R N L) := by
  have first := bounded_neg (bounded_scale (denominator N L) (bounded_mul hz hz))
  have second := bounded_scale (two*N*N) (bounded_series z N R L hz)
  exact le_congr (.eqRefl _) (by unfold factorRadius <;> ipra_ring) (bounded_add first second)

/-- The cubic part leaves room for the negative quadratic term in (C3). -/
theorem cubic_quadratic_budget (R N L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] le (two*N*N*numerator R N L) (R*R*denominator N L) := by
  have tail := mul_le_mul_right two (finite_taylor_bound R N L hR)
  have radius : Γ ⊢[PRAAx] le (two*(two*R)) (three*N) :=
    le_trans (le_mul_mono (le_refl two) hR)
      (le_of_eq_add (d := N) (by ipra_ring))
  have radiusScaled := le_mul_mono radius (le_refl (R*R*denominator N L))
  have scaled : Γ ⊢[PRAAx] le ((three*N)*(two*N*N*numerator R N L))
      ((three*N)*(R*R*denominator N L)) :=
    le_trans (b := two*R*R*R*denominator N L*two) (le_congr (by ipra_ring) (.eqRefl _) tail)
      (le_congr (by ipra_ring) (.eqRefl _) radiusScaled)
  exact cancel_positive (le_trans hN (le_of_eq_add (d := two*N) (by ipra_ring))) scaled

theorem factor_radius_bound (R N L : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] le (N*N*factorRadius R N L) (R*R*factorDenominator N L) := by
  have half := add_le_add₂ (le_refl (denominator N L*R*R)) (cubic_quadratic_budget R N L hN hR)
  exact le_congr (.eqRefl _) (by unfold factorDenominator <;> ipra_ring)
    (le_mul_mono (le_refl (N*N)) half)

/-- Finite (C3): `|L_L(z/N)|≤R²/N²`, with all denominators cleared. -/
theorem finite_factor_bound (z N R L : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale (N*N) (factorNumerator z N L)) (R*R*factorDenominator N L) :=
  bounded_mono (bounded_scale _ (factor_domination z N R L hz)) (factor_radius_bound R N L hN hR)

/-- Actual rational cross difference at two Taylor cutoffs. -/
def factorDifference (z N L K : PTm n) : PTm n :=
  add (scale (factorDenominator N L) (factorNumerator z N (L+K)))
    (ComplexLogarithmRemainder.neg (scale (factorDenominator N (L+K)) (factorNumerator z N L)))

ipra_subst factorDifference

/-- The common quadratic term cancels from the actual rational cross difference. -/
theorem difference_norm (z N L K C : PTm n) :
    Γ ⊢[PRAAx] normSq (scale C (factorDifference z N L K)) ≐
      normSq (scale (C*(two*N*N)*(two*N*N)) (ComplexLogarithmCauchy.difference z N L K)) := by
  apply deriveNat
  rw [normSq_eval, normSq_eval]
  simp only [factorDifference, factorNumerator, factorDenominator, add, scale,
    ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg,
    ZT.toZ_mul, ZT.toZ_ofNat, ComplexLogarithmCauchy.eval_difference_re,
    ComplexLogarithmCauchy.eval_difference_im, Q.mk_mul, map_mul]
  ring

/-- A genuine internal dyadic Cauchy modulus for these finite canonical factors. -/
theorem finite_factor_cauchy (z N R L K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale (pw two L) (factorDifference z N L K))
      (factorDenominator N L*factorDenominator N (L+K)) := by
  have h := bounded_scale ((two*N*N)*(two*N*N)) (ComplexLogarithmCauchy.dyadic_cauchy z N L R K hz hN hR)
  have eq : Γ ⊢[PRAAx] normSq (scale (pw two L) (factorDifference z N L K)) ≐
      normSq (scale ((two*N*N)*(two*N*N)) (scale (pw two L) (ComplexLogarithmCauchy.difference z N L K))) := by
    apply deriveNat
    rw [natEq (difference_norm (Γ := Γ) z N L K (pw two L))]
    rw [normSq_eval, normSq_eval]
    simp only [scale, eval_re_code, eval_im_code, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    ring
  exact le_congr eq.eqSymm (by unfold factorDenominator <;> ipra_ring) h

/-- Fixed PR symbols for the actual signed numerator and positive denominator. -/
def factorF : PR 3 := PTm.toPR (factorNumerator (var 0) (var 1) (var 2))
def factorDenominatorF : PR 2 := PTm.toPR (factorDenominator (var 0) (var 1))

theorem factor_at (z N L : PTm n) : Γ ⊢[PRAAx] ap3 factorF z N L ≐ factorNumerator z N L := by
  have h := toPR_eq (Γ := Γ) (factorNumerator (var 0) (var 1) (var 2)) ![z,N,L]
  simpa [factorF, ap3] using h

theorem factorDenominator_at (N L : PTm n) : Γ ⊢[PRAAx] ap2 factorDenominatorF N L ≐ factorDenominator N L := by
  have h := toPR_eq (Γ := Γ) (factorDenominator (var 0) (var 1)) ![N,L]
  simpa [factorDenominatorF, ap2] using h

/-! ## Actual finite sums over factor indices, at an arbitrary rational input `z/B` -/

/-- A total integer quotient only decreases the available denominator budget. -/
theorem quotient_budget (D d : PTm n) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] le (d*quo D d) D := by
  have pos : Γ ⊢[PRAAx] d ≐ succ (monus d one) := (eq_add_of_le hd).eqTrans (by ipra_ring)
  have div := Prf.andE₁ (div_mod (Γ := Γ) D (monus d one))
  have eq : Γ ⊢[PRAAx] D ≐ d*quo D d+rem D d :=
    div.eqTrans (congrAdd
      (congrMul pos.eqSymm (congrAp2 quoF (.eqRefl _) pos.eqSymm))
      (congrAp2 remF (.eqRefl _) pos.eqSymm))
  exact le_of_eq_add eq

/-- Computed scalar radius of a factor scaled to an arbitrary common denominator. -/
def termRadius (R B k L D : PTm n) : PTm n :=
  factorRadius R (B*k) L*quo D (factorDenominator (B*k) L)

def radiusData (R B L D : PTm n) : PTm n := pairT R (pairT B (pairT L D))
def radiusBody : PTm 2 := termRadius (fstT (var 1)) (fstT (sndT (var 1))) (var 0)
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
def radiusF : PR 2 := PTm.toPR radiusBody

ipra_subst termRadius

ipra_subst radiusData

theorem radius_at (R B k L D : PTm n) :
    Γ ⊢[PRAAx] ap2 radiusF k (radiusData R B L D) ≐ termRadius R B k L D := by
  have prog := toPR_eq (Γ := Γ) radiusBody ![k,radiusData R B L D]
  have decode := Prf.eqCongr (Γ := Γ)
    (termRadius (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![fstT (radiusData R B L D),fstT (sndT (radiusData R B L D)),k,
      fstT (sndT (sndT (radiusData R B L D))),sndT (sndT (sndT (radiusData R B L D)))])
    (σ' := ![R,B,k,L,D]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact .eqRefl _
      · exact ((congrFst (congrSnd (snd_pair _ _))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
      · exact ((congrSnd (congrSnd (snd_pair _ _))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _))
  have expr : Γ ⊢[PRAAx] inst2 radiusBody k (radiusData R B L D) ≐ termRadius R B k L D := by
    simpa only [radiusBody, inst2, subst_termRadius, subst_fstT, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons] using decode
  exact prog.eqTrans expr

theorem positive_product {a b : PTm n} (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (a*b) := le_congr (one_mul one) (.eqRefl _) (le_mul_mono ha hb)

/-- Derived reciprocal-square majorant, valid even when the quotient is not exact. -/
theorem term_radius_bound (R B k L D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hk : Γ ⊢[PRAAx] le one k) (hR : Γ ⊢[PRAAx] le (two*R) (B*k)) :
    Γ ⊢[PRAAx] le (B*B*k*k*termRadius R B k L D) (R*R*D) := by
  have hBk := positive_product hB hk
  have first := mul_le_mul_right (quo D (factorDenominator (B*k) L)) (factor_radius_bound R (B*k) L hBk hR)
  have second := le_mul_mono (le_refl (R*R))
    (quotient_budget D (factorDenominator (B*k) L) (factorDenominator_positive _ _ hBk))
  exact le_trans (le_congr (by unfold termRadius <;> ipra_ring) (by ipra_ring) first) second

/-- The pointwise majorant is proved from the actual Taylor radius, not supplied. -/
theorem radius_majorant (R B N L D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) (B*N)) :
    Γ ⊢[PRAAx] ReciprocalSquareTail.majorant radiusF (B*B) N (R*R*D) (radiusData R B L D) := by
  refine .allI ?_
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift] using hB.shift
  have start : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift, Syn.shift] using hN.shift
  have radius : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift R) (Syn.shift B*Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hR.shift
  have ge : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift N) (succ (Syn.shift N+var 0)) :=
    le_trans (le_add_right _ _) (le_succ_self _)
  have cap := term_radius_bound (Syn.shift R) (Syn.shift B) (succ (Syn.shift N+var 0))
    (Syn.shift L) (Syn.shift D) b (le_trans start ge)
    (le_trans radius (le_mul_mono (le_refl _) ge))
  have result := le_congr
    ((Prf.eqRefl _).eqTrans
          (congrMul (.eqRefl _) (radius_at _ _ _ _ _).eqSymm)) (.eqRefl _) cap
  simpa only [Syn.shift, PTm.subst_mul, subst_radiusData] using result

/-- Exact scaled factor term for a common denominator `D`. -/
def summand (z B k L D : PTm n) : PTm n :=
  scale (quo D (factorDenominator (B*k) L)) (factorNumerator z (B*k) L)

def sumStep : PTm 7 := add (var 1) (summand (var 2) (var 3) (succ (var 4+var 0)) (var 5) (var 6))
def sumF : PR 6 := recDef (zeroCode : PTm 5) sumStep
def finiteSum (z B N r L D : PTm n) : PTm n := app sumF ![r,z,B,N,L,D]

ipra_subst summand

@[simp] theorem subst_finiteSum {m : ℕ} (σ : Fin n → PTm m) (z B N r L D : PTm n) :
    Syn.subst σ (finiteSum z B N r L D) = finiteSum (Syn.subst σ z) (Syn.subst σ B)
      (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ L) (Syn.subst σ D) := by
  change app _ _ = app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem sum_zero (z B N L D : PTm n) : Γ ⊢[PRAAx] finiteSum z B N zero L D ≐ zeroCode := by
  have h := rec_zero (Γ := Γ) (zeroCode : PTm 5) sumStep ![z,B,N,L,D]
  have eq : (Fin.cases zero ![z,B,N,L,D] : Fin 6 → PTm n) = ![zero,z,B,N,L,D] := by
    funext i; fin_cases i <;> rfl
  rw [eq] at h
  simpa only [finiteSum, sumF, ComplexLogarithmRemainder.subst_zeroCode] using h

theorem sum_succ (z B N r L D : PTm n) :
    Γ ⊢[PRAAx] finiteSum z B N (succ r) L D ≐ add (finiteSum z B N r L D) (summand z B (succ (N+r)) L D) := by
  have h := rec_succ (Γ := Γ) (zeroCode : PTm 5) sumStep r ![z,B,N,L,D]
  have e1 : (Fin.cases (succ r) ![z,B,N,L,D] : Fin 6 → PTm n) = ![succ r,z,B,N,L,D] := by
    funext i; fin_cases i <;> rfl
  have e2 : (Fin.cases r (Fin.cases (app (recDef (zeroCode : PTm 5) sumStep)
      (Fin.cases r ![z,B,N,L,D])) ![z,B,N,L,D]) : Fin 7 → PTm n) =
        ![r,finiteSum z B N r L D,z,B,N,L,D] := by
    funext i; fin_cases i <;> rfl
  rw [e1,e2] at h
  have e5 : (5 : Fin 7) = (4 : Fin 6).succ := rfl
  have e6 : (6 : Fin 7) = (5 : Fin 6).succ := rfl
  have e5' : (5 : Fin 6) = (4 : Fin 5).succ := rfl
  simpa only [finiteSum, sumF, sumStep, ComplexLogarithmRemainder.subst_add, subst_summand,
    PTm.subst_add, ConciseIPRA.PTm.subst_succ, Syn.subst_var, e5,e6,e5',Matrix.cons_val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using h

/-- The actual complex sum is dominated by the actual scalar sum, by QF induction. -/
theorem sum_domination (z R B N r L D : PTm n) (hz : Γ ⊢[PRAAx] bounded z R) :
    Γ ⊢[PRAAx] bounded (finiteSum z B N r L D)
      (ReciprocalSquareTail.tailSum radiusF N r (radiusData R B L D)) := by
  have all : Γ ⊢[PRAAx] .all (bounded
      (finiteSum (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0) (Syn.shift L) (Syn.shift D))
      (ReciprocalSquareTail.tailSum radiusF (Syn.shift N) (var 0)
        (radiusData (Syn.shift R) (Syn.shift B) (Syn.shift L) (Syn.shift D)))) := by
    ipra_qfind (le_QF _ _) [ComplexLogarithmRemainder.subst_bounded, subst_finiteSum,
        ReciprocalSquareTail.subst_tailSum, subst_radiusData]
    · exact le_congr
        ((ComplexLogarithmRemainder.congr_normSq (sum_zero z B N L D)).eqTrans
          ComplexLogarithmRemainder.normSq_zero).eqSymm
        (congrMul (ReciprocalSquareTail.tailSum_zero _ _ _) (ReciprocalSquareTail.tailSum_zero _ _ _)).eqSymm
        (zero_le (zero*zero))
    · let Δ : List (Fm PTm (n+1)) :=
        bounded (finiteSum (Syn.shift z) (Syn.shift B) (Syn.shift N) (var 0) (Syn.shift L) (Syn.shift D))
          (ReciprocalSquareTail.tailSum radiusF (Syn.shift N) (var 0)
            (radiusData (Syn.shift R) (Syn.shift B) (Syn.shift L) (Syn.shift D))) :: Γ.map Fm.shift
      have zbound : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) := by
        simpa only [Fm.shift, ComplexLogarithmRemainder.subst_bounded, Syn.shift] using hz.shift
      have term := bounded_scale
        (quo (Syn.shift D) (factorDenominator (Syn.shift B*succ (Syn.shift N+var 0)) (Syn.shift L)))
        (factor_domination (Syn.shift z) (Syn.shift B*succ (Syn.shift N+var 0)) (Syn.shift R) (Syn.shift L) zbound)
      have point : Δ ⊢[PRAAx] bounded
          (summand (Syn.shift z) (Syn.shift B) (succ (Syn.shift N+var 0)) (Syn.shift L) (Syn.shift D))
          (ap2 radiusF (succ (Syn.shift N+var 0))
            (radiusData (Syn.shift R) (Syn.shift B) (Syn.shift L) (Syn.shift D))) :=
        le_congr (.eqRefl _)
          (congrMul ((mul_comm _ _).eqTrans (radius_at _ _ _ _ _).eqSymm)
            ((mul_comm _ _).eqTrans (radius_at _ _ _ _ _).eqSymm)) term.wk
      have joined := bounded_add Prf.hyp0 point
      exact le_congr (ComplexLogarithmRemainder.congr_normSq (sum_succ _ _ _ _ _ _)).eqSymm
        (congrMul (ReciprocalSquareTail.tailSum_succ _ _ _ _)
          (ReciprocalSquareTail.tailSum_succ _ _ _ _)).eqSymm joined
  simpa only [ComplexLogarithmRemainder.subst_bounded, subst_finiteSum,
    ReciprocalSquareTail.subst_tailSum, subst_radiusData, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r all

/-- Finite (C6) for the computed scaled sum, with no supplied pointwise majorant. -/
theorem finite_sum_bound (z R B N r L D : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two*R) (B*N)) :
    Γ ⊢[PRAAx] bounded (scale (B*B*N) (finiteSum z B N r L D)) (R*R*D) :=
  bounded_mono (bounded_scale _ (sum_domination z R B N r L D hz))
    (le_congr (.eqRefl _) (.eqRefl _)
      (ReciprocalSquareTail.uniform radiusF (B*B) N r (R*R*D) (radiusData R B L D)
        hN (radius_majorant R B N L D hB hN hR)))

/-! ## A computed exact common denominator for every finite tail query -/

def denominatorData (B N L : PTm n) : PTm n := pairT B (pairT N L)
def tailDenominatorBody : PTm 2 := factorDenominator
  (fstT (var 1)*succ (fstT (sndT (var 1))+var 0)) (sndT (sndT (var 1)))
def tailDenominator (B N r L : PTm n) : PTm n := ap2 (prodF tailDenominatorBody) r (denominatorData B N L)

ipra_subst denominatorData

ipra_subst tailDenominator

theorem tailDenominatorBody_at (B N L i : PTm n) :
    Γ ⊢[PRAAx] inst2 tailDenominatorBody i (denominatorData B N L) ≐
      factorDenominator (B*succ (N+i)) L := by
  simp only [tailDenominatorBody, inst2, subst_factorDenominator, PTm.subst_mul, PTm.subst_add,
    subst_fstT, subst_sndT, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h := Prf.eqCongr (Γ := Γ) (factorDenominator (var 0) (var 1) : PTm 2)
    (σ := ![fstT (denominatorData B N L)*succ (fstT (sndT (denominatorData B N L))+i),sndT (sndT (denominatorData B N L))])
    (σ' := ![B*succ (N+i),L]) (fun j => by
      fin_cases j
      · exact congrMul (fst_pair _ _) (congrSucc (congrAdd (snd_pair _ _).fstE (.eqRefl _)))
      · exact (snd_pair _ _).sndE)
  simpa only [subst_factorDenominator, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h

private alias positive_successor := Common.pos_of_one_le

theorem tail_denominator_body_positive (B N L i : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] inst2 tailDenominatorBody i (denominatorData B N L) ≐
      succ (pred (inst2 tailDenominatorBody i (denominatorData B N L))) :=
  positive_successor (le_congr (.eqRefl _) (tailDenominatorBody_at B N L i).eqSymm
    (factorDenominator_positive _ _ (positive_product hB (zero_lt_succ _))))

theorem tailDenominator_positive (B N r L : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (tailDenominator B N r L) := by
  have eq : Γ ⊢[PRAAx] tailDenominator B N r L ≐ succ (pred (tailDenominator B N r L)) := by
    apply prod_pos_bounded
    refine .allI (.impI ?_)
    have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift] using hB.shift
    simpa only [Syn.shift, subst_denominatorData] using
      tail_denominator_body_positive (Syn.shift B) (Syn.shift N) (Syn.shift L) (var 0) b.wk
  exact le_congr (.eqRefl _) eq.eqSymm (zero_lt_succ _)

/-- Every actual quotient multiplier in the finite query clears its denominator exactly. -/
theorem tail_quotient_clears (B N r L i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] factorDenominator (B*succ (N+i)) L *
      quo (tailDenominator B N r L) (factorDenominator (B*succ (N+i)) L) ≐ tailDenominator B N r L := by
  have fresh : Γ.map Fm.shift ⊢[PRAAx] inst2 tailDenominatorBody (var 0) (Syn.shift (denominatorData B N L)) ≐
      succ (pred (inst2 tailDenominatorBody (var 0) (Syn.shift (denominatorData B N L)))) := by
    have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift, Syn.shift] using hB.shift
    simpa only [Syn.shift, subst_denominatorData] using
      tail_denominator_body_positive (Syn.shift B) (Syn.shift N) (Syn.shift L) (var 0) b
  have div := Probability.TowerCommonDen.dvd_prod_term tailDenominatorBody fresh hi
  have eq := DiophantineNumberTheory.Coprime.eq_of_dvd' (tail_denominator_body_positive B N L i hB) div
  exact (eq.eqTrans (congrMul (tailDenominatorBody_at B N L i)
    (congrAp2 quoF (.eqRefl _) (tailDenominatorBody_at B N L i)))).eqSymm

/-- The Gaussian numerator of the actual finite rational Gamma-factor tail;
its computed positive denominator is `tailDenominator B N r L`. -/
def finiteTail (z B N r L : PTm n) : PTm n := finiteSum z B N r L (tailDenominator B N r L)
def finiteTailF : PR 5 := PTm.toPR (finiteTail (var 0) (var 1) (var 2) (var 3) (var 4))

ipra_subst finiteTail

theorem finite_tail_at (z B N r L : PTm n) :
    Γ ⊢[PRAAx] app finiteTailF ![z,B,N,r,L] ≐ finiteTail z B N r L := by
  have h := toPR_eq (Γ := Γ) (finiteTail (var 0) (var 1) (var 2) (var 3) (var 4)) ![z,B,N,r,L]
  simpa only [finiteTailF, subst_finiteTail, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using h

/-- Finite (C6): the sum of the actual finite factors at `z/(B*k)` is bounded
by `(R/B)^2/N`, uniformly in both internal cutoffs. -/
theorem finite_tail_bound (z R B N r L : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two*R) (B*N)) :
    Γ ⊢[PRAAx] le one (tailDenominator B N r L) ⋏
      bounded (scale (B*B*N) (finiteTail z B N r L)) (R*R*tailDenominator B N r L) :=
  .andI (tailDenominator_positive B N r L hB) (finite_sum_bound z R B N r L _ hz hB hN hR)

private theorem cancel_complex_scale {C a R : PTm n} (hC : Γ ⊢[PRAAx] le one C)
    (h : Γ ⊢[PRAAx] bounded (scale C a) (C*R)) : Γ ⊢[PRAAx] bounded a R := by
  have scalar : Γ ⊢[PRAAx] le (C*(C*normSq a)) (C*(C*(R*R))) :=
    le_congr ((ComplexLogarithmRemainder.normSq_scale C a).eqTrans (by ipra_ring)) (by ipra_ring) h
  exact cancel_positive hC (cancel_positive hC scalar)

/-- The exact source (C6) constant for an arbitrary rational complex input
`z/B` on an integer disk `R`: the finite tail is at most `R²/N`. -/
theorem rational_disk_tail_bound (z R B N r L : PTm n) (hz : Γ ⊢[PRAAx] bounded z (R*B))
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] bounded (scale N (finiteTail z B N r L)) (R*R*tailDenominator B N r L) := by
  have radius : Γ ⊢[PRAAx] le (two*(R*B)) (B*N) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl B) hR)
  have original := Prf.andE₂ (finite_tail_bound z (R*B) B N r L hz hB hN radius)
  have eq : Γ ⊢[PRAAx] normSq (scale (B*B) (scale N (finiteTail z B N r L))) ≐
      normSq (scale (B*B*N) (finiteTail z B N r L)) := by
    apply deriveNat
    have a := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) (B*B) (scale N (finiteTail z B N r L)))
    have b := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) N (finiteTail z B N r L))
    have c := natEq (ComplexLogarithmRemainder.normSq_scale (Γ := Γ) (B*B*N) (finiteTail z B N r L))
    simp only [Q.mk_mul, map_mul] at a b c
    rw [a,b,c]
    ring
  have scaled : Γ ⊢[PRAAx] bounded (scale (B*B) (scale N (finiteTail z B N r L)))
      ((B*B)*(R*R*tailDenominator B N r L)) :=
    le_congr eq.eqSymm (by ipra_ring) original
  exact cancel_complex_scale (positive_product hB hB) scaled

/-- Exact rational meaning of a scaled summand: its own denominator times
its numerator is the common denominator times the original factor numerator. -/
theorem summand_clears_re (z B N r L i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (factorDenominator (B*succ (N+i)) L) *
        re (summand z B (succ (N+i)) L (tailDenominator B N r L)))
      (ZT.ofNat (tailDenominator B N r L)*re (factorNumerator z (B*succ (N+i)) L)) := by
  ipra_lc [summand, scale, eval_re_code] ZT.toZ Γ (re (factorNumerator z (B*succ (N+i)) L))*natEq (tail_quotient_clears B N r L i hB hi)

theorem summand_clears_im (z B N r L i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] ZT.eq
      (ZT.ofNat (factorDenominator (B*succ (N+i)) L) *
        im (summand z B (succ (N+i)) L (tailDenominator B N r L)))
      (ZT.ofNat (tailDenominator B N r L)*im (factorNumerator z (B*succ (N+i)) L)) := by
  ipra_lc [summand, scale, eval_im_code] ZT.toZ Γ (im (factorNumerator z (B*succ (N+i)) L))*natEq (tail_quotient_clears B N r L i hB hi)

/-- Variables are Gaussian numerator, divisor, numerator radius, and Taylor cutoff. -/
def factorFormula : Fm PTm 4 :=
  bounded (var 0) (var 2) ⟶ le one (var 1) ⟶ le (two*var 2) (var 1) ⟶
    (le one (factorDenominator (var 1) (var 3)) ⋏
      bounded (scale (var 1*var 1) (factorNumerator (var 0) (var 1) (var 3)))
        (var 2*var 2*factorDenominator (var 1) (var 3)))

theorem finite_factor_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 factorFormula :=
  closeUniv 4 (.impI (.impI (.impI (.andI
    (factorDenominator_positive (var 1) (var 3) Prf.hyp1)
    (finite_factor_bound (var 0) (var 1) (var 2) (var 3) Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

/-- Both Taylor cutoffs and the full rational discrepancy stay internal. -/
theorem finite_factor_cauchy_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (bounded (var 0) (var 2) ⟶ le one (var 1) ⟶ le (two*var 2) (var 1) ⟶
        (le one (factorDenominator (var 1) (var 3)) ⋏
        (le one (factorDenominator (var 1) (var 3+var 4)) ⋏
          bounded (scale (pw two (var 3)) (factorDifference (var 0) (var 1) (var 3) (var 4)))
            (factorDenominator (var 1) (var 3)*factorDenominator (var 1) (var 3+var 4))))) :=
  closeUniv 5 (.impI (.impI (.impI (.andI (factorDenominator_positive _ _ Prf.hyp1)
    (.andI (factorDenominator_positive _ _ Prf.hyp1)
      (finite_factor_cauchy _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

/-- Finite (C6), uniform in the rational input denominator and both cutoffs.
Variables: `z,R,B,N,r,L`. The squared norm code avoids square-root axioms. -/
theorem finite_tail_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (bounded (var 0) (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
        le (two*var 1) (var 2*var 3) ⟶
        (le one (tailDenominator (var 2) (var 3) (var 4) (var 5)) ⋏
          bounded (scale (var 2*var 2*var 3) (finiteTail (var 0) (var 2) (var 3) (var 4) (var 5)))
            (var 1*var 1*tailDenominator (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (finite_tail_bound
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

/-- Source integer-disk constants, still with an arbitrary internal rational denominator. -/
theorem rational_disk_tail_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (bounded (var 0) (var 1*var 2) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
        le (two*var 1) (var 3) ⟶
          bounded (scale (var 3) (finiteTail (var 0) (var 2) (var 3) (var 4) (var 5)))
            (var 1*var 1*tailDenominator (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (rational_disk_tail_bound
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem factor_programs_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((ap3 factorF (var 0) (var 1) (var 2) ≐ factorNumerator (var 0) (var 1) (var 2)) ⋏
        (ap2 factorDenominatorF (var 1) (var 2) ≐ factorDenominator (var 1) (var 2))) :=
  closeUniv 3 (.andI (factor_at _ _ _) (factorDenominator_at _ _))

theorem tail_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (app finiteTailF ![var 0,var 1,var 2,var 3,var 4] ≐ finiteTail (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (finite_tail_at _ _ _ _ _)

#print axioms factor_domination
#print axioms cubic_quadratic_budget
#print axioms factor_radius_bound
#print axioms finite_factor_bound_closed
#print axioms finite_factor_cauchy_closed
#print axioms term_radius_bound
#print axioms radius_majorant
#print axioms sum_succ
#print axioms sum_domination
#print axioms tailDenominator_positive
#print axioms tail_quotient_clears
#print axioms summand_clears_re
#print axioms summand_clears_im
#print axioms finite_tail_bound_closed
#print axioms rational_disk_tail_bound
#print axioms rational_disk_tail_closed
#print axioms factor_programs_closed
#print axioms tail_program_closed

end LeanProofs.IPRA.Analysis.GammaCanonicalFactors
