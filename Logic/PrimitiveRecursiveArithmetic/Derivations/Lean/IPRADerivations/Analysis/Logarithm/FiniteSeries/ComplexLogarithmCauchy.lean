import IPRADerivations.Analysis.Logarithm.FiniteSeries.ComplexLogarithmRemainder

/-!
# Cauchy bounds for finite complex Taylor-logarithm tails

For the exact numerators `G_L` and denominators `D_L` of
`ComplexLogarithmRemainder`, this file bounds the actual difference
`T_K = D_L G_(L+K) - D_(L+K) G_L` with all lengths internal.
An auxiliary positive numerator is computed by genuine primitive recursion;
its bound is proved, rather than supplied as a contract.

The resulting squared inequality is
`|3 N^(L+3) T_K|² ≤ (2 R^(L+3) D_L D_(L+K))²` for `2R ≤ N`.
When `N ≥ 1`, both denominators are positive, so this is the rational
finite Cauchy estimate
`|G_(L+K)/D_(L+K) - G_L/D_L| ≤ 2 R^(L+3)/(3N^(L+3))`.
The closed `uniform_dyadic_cauchy` theorem also supplies the explicit
uniform modulus `|G_(L+K)/D_(L+K) - G_L/D_L| ≤ 2^(-L)`, together
with positivity of both computed denominators.
The polynomial inequality also includes the degenerate zero-divisor case.
No infinite logarithm or functional equation is assumed or identified here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ComplexLogarithmCauchy

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.LogarithmRemainder
  (three denominator denominator_succ denominator_positive)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder
  (re im code add mul scale zeroCode normSq bounded series series_zero series_succ
    power bounded_power bounded_neg bounded_scale bounded_add bounded_mono
    normSq_eval normSq_code normSq_zero congr_normSq eval_re_code eval_im_code)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def ap4 (f : PR 4) (a b c d : PTm n) : PTm n := app f ![a, b, c, d]

@[simp] theorem subst_ap4 {m : ℕ} (σ : Fin n → PTm m) (f : PR 4) (a b c d : PTm n) :
    Syn.subst σ (ap4 f a b c d) = ap4 f (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) := by
  show app _ _ = app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Variables `0 = K`, `1 = U_K`, `2 = L`, `3 = R`, `4 = N`. -/
def positiveStep : PTm 5 :=
  (var 2 + var 0 + three) * var 4 * var 1 +
    denominator (var 4) (var 2) * fact (var 2 + var 0 + two) *
      pw (var 3) (var 2 + var 0 + three)

def positiveF : PR 4 := recDef zero positiveStep
def positive (L R N K : PTm n) : PTm n := ap4 positiveF K L R N

ipra_subst positive

theorem positive_zero (L R N : PTm n) : Γ ⊢[PRAAx] positive L R N zero ≐ zero := by
  have h := rec_zero_vecCons (Γ := Γ) (zero : PTm 3) positiveStep ![L, R, N]
  simpa only [positive, positiveF, ap4, ConciseIPRA.PTm.subst_zero] using h

theorem positive_succ (L R N K : PTm n) :
    Γ ⊢[PRAAx] positive L R N (succ K) ≐
      (L + K + three) * N * positive L R N K +
        denominator N L * fact (L + K + two) * pw R (L + K + three) := by
  have h := rec_succ_vecCons (Γ := Γ) (zero : PTm 3) positiveStep K ![L, R, N]
  simpa [positive, positiveF, ap4, positiveStep] using h

theorem congr_denominator {N L M : PTm n} (h : Γ ⊢[PRAAx] L ≐ M) :
    Γ ⊢[PRAAx] denominator N L ≐ denominator N M :=
  congrMul (congrAp2 factF (congrAdd h (.eqRefl _)) (.eqRefl zero))
    (congrAp2 powF (congrAdd h (.eqRefl _)) (.eqRefl N))

def strong (L R N K : PTm n) : Fm PTm n :=
  le (three * pw N (L + three) * positive L R N K +
      two * denominator N L * fact (L + K + two) * pw N (L + two) * pw R (L + K + three))
    (two * pw R (L + three) * denominator N L * denominator N (L + K))

ipra_subst strong [fact]

theorem strong_zero (L R N : PTm n) : Γ ⊢[PRAAx] strong L R N zero := by
  have a := natEq (positive_zero (Γ := Γ) L R N)
  have p := natEq (congrAp2 (Γ := Γ) powF (congrAdd (add_zero L) (.eqRefl three)) (.eqRefl R))
  have d := natEq (congr_denominator (N := N) (Γ := Γ) (add_zero L))
  unfold strong
  refine le_of_eq_add (d := zero) ?_
  apply deriveNat
  ipra_simps
  rw [a, natEq (congrAp2 (Γ := Γ) factF (congrAdd (add_zero L) (.eqRefl two)) (.eqRefl zero)), p, d]
  simp only [denominator, Q.mk_mul, map_mul]
  ring

theorem strong_step {L R N K : PTm n} (hN : Γ ⊢[PRAAx] le (two * R) N)
    (ih : Γ ⊢[PRAAx] strong L R N K) : Γ ⊢[PRAAx] strong L R N (succ K) := by
  have d := natEq ((congr_denominator (N := N) (Γ := Γ) (add_succ L K)).eqTrans
    (denominator_succ N (L + K)))
  have e₂ : Γ ⊢[PRAAx] L + succ K + two ≐ succ (L + K + two) := by ipra_ring
  have e₃ : Γ ⊢[PRAAx] L + succ K + three ≐ succ (L + K + three) := by ipra_ring
  have e : Γ ⊢[PRAAx] L + three ≐ succ (L + two) := by ipra_ring
  unfold strong at *
  refine le_of_eq_add (d :=
    (L + K + three) * N * monus
      (two * pw R (L + three) * denominator N L * denominator N (L + K))
      (three * pw N (L + three) * positive L R N K +
        two * denominator N L * fact (L + K + two) * pw N (L + two) * pw R (L + K + three)) +
    denominator N L * fact (L + K + two) * pw N (L + two) * pw R (L + K + three) *
      ((L + K + three) * monus N (two * R) + (L + K) * N)) ?_
  ipra_lc (𝔞(L) + 𝔞(K) + 3) * 𝔞(N) * natEq (eq_add_of_le ih) +
    𝔞(denominator N L) * 𝔞(fact (L + K + two)) * 𝔞(pw N (L + two)) * 𝔞(pw R (L + K + three)) * (𝔞(L) + 𝔞(K) + 3) * natEq (eq_add_of_le hN) +
    2 * 𝔞(pw R (L + three)) * 𝔞(denominator N L) * d -
    3 * 𝔞(pw N (L + three)) * natEq (positive_succ (Γ := Γ) L R N K) -
    2 * 𝔞(denominator N L) * 𝔞(pw N (L + two)) * 𝔞(pw R (L + succ K + three)) * natEq ((congrAp2 factF e₂ (.eqRefl zero)).eqTrans (fact_succ (L + K + two) zero)) -
    2 * 𝔞(denominator N L) * 𝔞(pw N (L + two)) * 𝔞(fact (L + K + two)) * (𝔞(L) + 𝔞(K) + 3) * natEq ((congrAp2 powF e₃ (.eqRefl R)).eqTrans (pw_succ R (L + K + three))) -
    3 * 𝔞(denominator N L) * 𝔞(fact (L + K + two)) * 𝔞(pw R (L + K + three)) * natEq ((congrAp2 powF e (.eqRefl N)).eqTrans (pw_succ N (L + two)))

theorem finite_positive_strong (L R N K : PTm n) (hN : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] strong L R N K := by
  have all : Γ ⊢[PRAAx] .all
      (strong (Syn.shift L) (Syn.shift R) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_strong, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
        using strong_zero (Γ := Γ) L R N
    · simp only [subst_strong, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] le (two * Syn.shift R) (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hN.shift
      exact strong_step shifted.wk Prf.hyp0
  simpa only [subst_strong, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    using Prf.allE K all

theorem finite_positive_bound (L R N K : PTm n) (hN : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] le (three * pw N (L + three) * positive L R N K)
      (two * pw R (L + three) * denominator N L * denominator N (L + K)) :=
  le_trans (le_add_right _ _) (finite_positive_strong L R N K hN)

#print axioms finite_positive_strong

/-! ## The actual rational numerator difference -/

def difference (z N L K : PTm n) : PTm n :=
  add (scale (denominator N L) (series z N (L + K)))
    (ComplexLogarithmRemainder.neg (scale (denominator N (L + K)) (series z N L)))

ipra_subst difference

theorem eval_re_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (re a) = ZT.toZ Γ (re b) := by
  simp only [re, ZT.toZ]
  linear_combination natEq (congrFst (congrFst h)) - natEq (congrSnd (congrFst h))

theorem eval_im_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (im a) = ZT.toZ Γ (im b) := by
  simp only [im, ZT.toZ]
  linear_combination natEq (congrFst (congrSnd h)) - natEq (congrSnd (congrSnd h))

theorem eval_difference_re (z N L K : PTm n) :
    ZT.toZ Γ (re (difference z N L K)) =
      𝔞(denominator N L) * ZT.toZ Γ (re (series z N (L + K))) -
        𝔞(denominator N (L + K)) * ZT.toZ Γ (re (series z N L)) := by
  simp only [difference, add, scale, ComplexLogarithmRemainder.neg, eval_re_code, ZT.toZ_add, ZT.toZ_neg,
    ZT.toZ_mul, ZT.toZ_ofNat]
  ring

theorem eval_difference_im (z N L K : PTm n) :
    ZT.toZ Γ (im (difference z N L K)) =
      𝔞(denominator N L) * ZT.toZ Γ (im (series z N (L + K))) -
        𝔞(denominator N (L + K)) * ZT.toZ Γ (im (series z N L)) := by
  simp only [difference, add, scale, ComplexLogarithmRemainder.neg, eval_im_code, ZT.toZ_add, ZT.toZ_neg,
    ZT.toZ_mul, ZT.toZ_ofNat]
  ring

theorem difference_zero (z N L : PTm n) :
    Γ ⊢[PRAAx] normSq (difference z N L zero) ≐ zero := by
  have s : Γ ⊢[PRAAx] series z N (L + zero) ≐ series z N L :=
    congrAp3 ComplexLogarithmRemainder.seriesF (add_zero L) (.eqRefl z) (.eqRefl N)
  have sr := eval_re_congr s
  have si := eval_im_congr s
  apply deriveNat
  rw [normSq_eval, eval_difference_re, eval_difference_im]
  rw [sr, si, natEq (congr_denominator (N := N) (Γ := Γ) (add_zero L))]
  simp

/-- The exact next difference numerator, before taking its squared norm. -/
def nextDifference (z N L K : PTm n) : PTm n :=
  add (scale ((L + K + three) * N) (difference z N L K))
    (ComplexLogarithmRemainder.neg (scale (denominator N L * fact (L + K + two))
      (power (ComplexLogarithmRemainder.neg z) (L + K + three))))

theorem difference_step_norm (z N L K : PTm n) :
    Γ ⊢[PRAAx] normSq (difference z N L (succ K)) ≐ normSq (nextDifference z N L K) := by
  have s : Γ ⊢[PRAAx] series z N (L + succ K) ≐
      add (scale ((L + K + three) * N) (series z N (L + K)))
        (ComplexLogarithmRemainder.neg (scale (fact (L + K + two))
          (power (ComplexLogarithmRemainder.neg z) (L + K + three)))) :=
    (congrAp3 (Γ := Γ) ComplexLogarithmRemainder.seriesF (add_succ L K)
      (.eqRefl z) (.eqRefl N)).eqTrans (series_succ z N (L + K))
  have sr := eval_re_congr s
  have si := eval_im_congr s
  have d := natEq ((congr_denominator (N := N) (Γ := Γ) (add_succ L K)).eqTrans
    (denominator_succ N (L + K)))
  simp only [add, scale, ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code, ZT.toZ_add, ZT.toZ_neg,
    ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_mul, map_mul] at sr si d
  apply deriveNat
  rw [normSq_eval, normSq_eval, eval_difference_re, eval_difference_im]
  simp only [nextDifference, add, scale, ComplexLogarithmRemainder.neg, eval_re_code, eval_im_code,
    ZT.toZ_add, ZT.toZ_neg, ZT.toZ_mul, ZT.toZ_ofNat,
    eval_difference_re, eval_difference_im, Q.mk_mul, map_mul]
  rw [sr, si, d]
  ring

/-- The norm of the actual numerator difference is dominated by the computed
positive shifted tail, uniformly in both truncation lengths. -/
theorem difference_domination (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R) :
    Γ ⊢[PRAAx] bounded (difference z N L K) (positive L R N K) := by
  have all : Γ ⊢[PRAAx] .all
      (bounded (difference (Syn.shift z) (Syn.shift N) (Syn.shift L) (var 0))
        (positive (Syn.shift L) (Syn.shift R) (Syn.shift N) (var 0))) := by
    ipra_qfind (le_QF _ _) [ComplexLogarithmRemainder.subst_bounded, subst_difference, subst_positive]
    · have r := (congrMul (positive_zero (Γ := Γ) L R N) (positive_zero L R N)).eqTrans (mul_zero zero)
      exact le_congr (difference_zero _ _ _).eqSymm r.eqSymm (le_refl zero)
    · have shifted : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift z) (Syn.shift R) := by
        simpa [Fm.shift, Syn.shift] using hz.shift
      have ih : (bounded (difference (Syn.shift z) (Syn.shift N) (Syn.shift L) (var 0))
          (positive (Syn.shift L) (Syn.shift R) (Syn.shift N) (var 0))) :: Γ.map Fm.shift ⊢[PRAAx]
          bounded (difference (Syn.shift z) (Syn.shift N) (Syn.shift L) (var 0))
            (positive (Syn.shift L) (Syn.shift R) (Syn.shift N) (var 0)) := Prf.hyp0
      have first := bounded_scale ((Syn.shift L + var 0 + three) * Syn.shift N) ih
      have second := bounded_neg (bounded_scale
        (denominator (Syn.shift N) (Syn.shift L) * fact (Syn.shift L + var 0 + two))
        (bounded_power (ComplexLogarithmRemainder.neg (Syn.shift z)) (Syn.shift R) (Syn.shift L + var 0 + three)
          (bounded_neg (shifted.wk (ψ := bounded
            (difference (Syn.shift z) (Syn.shift N) (Syn.shift L) (var 0))
            (positive (Syn.shift L) (Syn.shift R) (Syn.shift N) (var 0)))))))
      exact le_congr (difference_step_norm _ _ _ _).eqSymm
        (congrMul (positive_succ _ _ _ _) (positive_succ _ _ _ _)).eqSymm (bounded_add first second)
  simpa only [ComplexLogarithmRemainder.subst_bounded, subst_difference, subst_positive,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE K all

theorem finite_cauchy_bound (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hN : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] bounded (scale (three * pw N (L + three)) (difference z N L K))
      (two * pw R (L + three) * denominator N L * denominator N (L + K)) :=
  bounded_mono (bounded_scale _ (difference_domination z N L R K hz))
    (finite_positive_bound L R N K hN)

#print axioms difference_domination
#print axioms finite_cauchy_bound

/-! ## An explicit uniform dyadic Cauchy modulus -/

def coefficientFormula (R N L : PTm n) : Fm PTm n :=
  le (two * pw two L * pw R (L + three)) (three * pw N (L + three))

ipra_subst coefficientFormula

theorem coefficient_zero (R N : PTm n) (hN : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] coefficientFormula R N zero := by
  have hr : Γ ⊢[PRAAx] le R N :=
    le_trans (le_of_eq_add (d := R) (by ipra_ring)) hN
  have h23 : Γ ⊢[PRAAx] le two three := le_of_eq_add (d := one) (by ipra_ring)
  have b := le_mul_mono h23 (pw_le_pw three hr)
  have l : Γ ⊢[PRAAx] two * pw two zero * pw R (zero + three) ≐ two * pw R three :=
    (congrMul (congrMul (.eqRefl _) (pw_zero two))
      (congrAp2 powF (zero_add three) (.eqRefl R))).eqTrans (by ipra_ring)
  have r : Γ ⊢[PRAAx] three * pw N (zero + three) ≐ three * pw N three :=
    congrMul (.eqRefl _) (congrAp2 powF (zero_add three) (.eqRefl N))
  exact le_congr l.eqSymm r.eqSymm b

theorem coefficient_step {R N L : PTm n} (hN : Γ ⊢[PRAAx] le (two * R) N)
    (ih : Γ ⊢[PRAAx] coefficientFormula R N L) :
    Γ ⊢[PRAAx] coefficientFormula R N (succ L) := by
  have b := le_mul_mono ih hN
  have e : Γ ⊢[PRAAx] succ L + three ≐ succ (L + three) := by ipra_ring
  refine le_congr ?_ ?_ b
  · ipra_lc -2 * 𝔞(pw R (succ L + three)) * natEq (pw_succ (Γ := Γ) two L) -
      4 * 𝔞(pw two L) * natEq ((congrAp2 powF e (.eqRefl R)).eqTrans (pw_succ R (L + three)))
  · ipra_lc -3 * natEq ((congrAp2 powF e (.eqRefl N)).eqTrans (pw_succ N (L + three)))

theorem dyadic_coefficient (R N L : PTm n) (hN : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] coefficientFormula R N L := by
  have all : Γ ⊢[PRAAx] .all (coefficientFormula (Syn.shift R) (Syn.shift N) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_coefficientFormula, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
        using coefficient_zero R N hN
    · simp only [subst_coefficientFormula, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] le (two * Syn.shift R) (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hN.shift
      exact coefficient_step shifted.wk Prf.hyp0
  simpa only [subst_coefficientFormula, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    using Prf.allE L all

theorem power_positive (N k : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le one (pw N k) := by
  have all : Γ ⊢[PRAAx] .all (le one (pw (Syn.shift N) (var 0))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_ap2]
    · exact le_congr (.eqRefl _) (pw_zero N).eqSymm (le_refl one)
    · have shifted : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hN.shift
      have b : (le one (pw (Syn.shift N) (var 0))) :: Γ.map Fm.shift ⊢[PRAAx]
          le (one * one) (pw (Syn.shift N) (var 0) * Syn.shift N) :=
        le_mul_mono Prf.hyp0 shifted.wk
      exact le_congr (one_mul one) (pw_succ _ _).eqSymm b
  simpa only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using Prf.allE k all

private alias cancel_positive := Common.mul_cancel_le

theorem positive_dyadic_bound (L R N K : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hR : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] le (pw two L * positive L R N K) (denominator N L * denominator N (L + K)) := by
  have tail := finite_positive_bound L R N K hR
  have coefficient := dyadic_coefficient R N L hR
  have first : Γ ⊢[PRAAx]
      le ((three * pw N (L + three)) * (pw two L * positive L R N K))
        ((two * pw two L * pw R (L + three)) * (denominator N L * denominator N (L + K))) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (pw two L) tail)
  have second := mul_le_mul_right (denominator N L * denominator N (L + K)) coefficient
  have positive : Γ ⊢[PRAAx] le one (three * pw N (L + three)) :=
    le_trans (power_positive N (L + three) hN)
      (le_of_eq_add (d := two * pw N (L + three)) (by ipra_ring))
  exact cancel_positive positive (le_trans first second)

theorem dyadic_cauchy (z N L R K : PTm n) (hz : Γ ⊢[PRAAx] bounded z R)
    (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two * R) N) :
    Γ ⊢[PRAAx] bounded (scale (pw two L) (difference z N L K))
      (denominator N L * denominator N (L + K)) :=
  bounded_mono (bounded_scale _ (difference_domination z N L R K hz))
    (positive_dyadic_bound L R N K hN hR)

/-- Variables `0 = L`, `1 = R`, `2 = N`, `3 = K`. -/
def positiveFormula : Fm PTm 4 :=
  le (two * var 1) (var 2) ⟶ strong (var 0) (var 1) (var 2) (var 3)

theorem positive_shifted_remainder : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 positiveFormula :=
  closeUniv 4 (.impI (finite_positive_strong _ _ _ _ Prf.hyp0))

/-- Variables `0 = L`, `1 = K`, `2 = z`, `3 = R`, `4 = N`. -/
def cauchyFormula : Fm PTm 5 :=
  bounded (var 2) (var 3) ⟶ le (two * var 3) (var 4) ⟶
    bounded (scale (three * pw (var 4) (var 0 + three))
      (difference (var 2) (var 4) (var 0) (var 1)))
      (two * pw (var 3) (var 0 + three) * denominator (var 4) (var 0) *
        denominator (var 4) (var 0 + var 1))

theorem finite_complex_logarithm_cauchy : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 cauchyFormula :=
  closeUniv 5 (.impI (.impI (finite_cauchy_bound _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- Variables `0 = L`, `1 = K`, `2 = z`, `3 = R`, `4 = N`. -/
def dyadicFormula : Fm PTm 5 :=
  le one (var 4) ⟶ bounded (var 2) (var 3) ⟶ le (two * var 3) (var 4) ⟶
    (le one (denominator (var 4) (var 0)) ⋏
      (le one (denominator (var 4) (var 0 + var 1)) ⋏
        bounded (scale (pw two (var 0)) (difference (var 2) (var 4) (var 0) (var 1)))
          (denominator (var 4) (var 0) * denominator (var 4) (var 0 + var 1))))

theorem uniform_dyadic_cauchy : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 dyadicFormula := by
  refine closeUniv 5 (.impI (.impI (.impI ?_)))
  exact .andI (denominator_positive _ _ hyp2)
    (.andI (denominator_positive _ _ hyp2) (dyadic_cauchy _ _ _ _ _ Prf.hyp1 hyp2 Prf.hyp0))

#print axioms positive_shifted_remainder
#print axioms finite_complex_logarithm_cauchy
#print axioms uniform_dyadic_cauchy

end LeanProofs.IPRA.Analysis.ComplexLogarithmCauchy
