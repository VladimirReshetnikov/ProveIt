import IPRADerivations.Analysis.Optimization.RationalArgmin

/-!
# Exact signed rational endpoint clearing for Minkowski boxes

The endpoints have independent positive predecessor-stored denominators.
Given actual computed cofactors whose products with those denominators are
one positive common mesh, rational weak/strict comparisons transfer to the
integer numerators. Natural widths are computed by monus, and their exact
clearing identity is proved from the endpoint inequalities and the cofactor
identities. No supplied integer endpoint or width correctness is assumed.
The next frontend instantiates these algebraic lemmas with the actual
RationalSupMetric product/quotient programs on its actual endpoint pool.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling

open_ipra exports
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf subst_numeratorOf subst_denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (left rationalLE denominator_positive subst_left)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rationalLT (a b : PTm n) : Fm PTm n := lt (left a b) (left b a)
def scaled (a c : PTm n) : ZT n := ⟨(numeratorOf a).pos*c,(numeratorOf a).neg*c⟩
def scaledLeft (a b c d : PTm n) : PTm n := (scaled a c).pos+(scaled b d).neg
def gap (a b : PTm n) : PTm n := monus (left b a) (left a b)
def scaledGap (a b c d : PTm n) : PTm n := monus (scaledLeft b a d c) (scaledLeft a b c d)

@[simp] theorem subst_rationalLT {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) :
    (rationalLT a b).subst σ = rationalLT (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [rationalLT, subst_lt, subst_left]
@[simp] theorem subst_scaled {l : ℕ} (σ : Fin n → PTm l) (a c : PTm n) :
    (scaled a c).subst σ = scaled (Syn.subst σ a) (Syn.subst σ c) := by simp [scaled, ZT.subst, numeratorOf]
ipra_subst scaledLeft [scaled, numeratorOf]
@[simp] theorem subst_gap {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) :
    Syn.subst σ (gap a b) = gap (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [gap, PTm.subst_monus, subst_left]
@[simp] theorem subst_scaledGap {l : ℕ} (σ : Fin n → PTm l) (a b c d : PTm n) :
    Syn.subst σ (scaledGap a b c d) = scaledGap (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) := by
  simp only [scaledGap, PTm.subst_monus, subst_scaledLeft]

alias positive_cancel := Common.mul_cancel_le

theorem cofactor_positive (a c m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (h : Γ ⊢[PRAAx] denominatorOf a*c ≐ m) : Γ ⊢[PRAAx] le one c := by
  refine .orE (zero_or_succ c) ?_ ?_
  · have zeroEq : (c ≐ zero) :: Γ ⊢[PRAAx] m ≐ zero := h.wk.eqSymm.eqTrans
      ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
    exact lt_zero_absurd _ (lt_congr (.eqRefl zero) zeroEq hm.wk)
  · exact Order.zero_lt_of_eq_succ Prf.hyp0

theorem scaled_left_identity (a b c d m : PTm n)
    (ha : Γ ⊢[PRAAx] denominatorOf a*c ≐ m) (hb : Γ ⊢[PRAAx] denominatorOf b*d ≐ m) :
    Γ ⊢[PRAAx] (c*d)*left a b ≐ m*scaledLeft a b c d := by
  unfold left scaledLeft scaled
  ipra_lc (𝔞((numeratorOf a).pos)*𝔞 c)*natEq hb+(𝔞((numeratorOf b).neg)*𝔞 d)*natEq ha

theorem weak_clear (a b c d m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (ha : Γ ⊢[PRAAx] denominatorOf a*c ≐ m) (hb : Γ ⊢[PRAAx] denominatorOf b*d ≐ m)
    (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx] le (scaledLeft a b c d) (scaledLeft b a d c) := by
  have first := scaled_left_identity a b c d m ha hb
  have last := (congrMul (mul_comm c d) (.eqRefl (left b a))).eqTrans (scaled_left_identity b a d c m hb ha)
  exact positive_cancel hm (le_congr first last (le_mul_mono (le_refl (c*d)) h))

theorem weak_unclear (a b c d m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (ha : Γ ⊢[PRAAx] denominatorOf a*c ≐ m) (hb : Γ ⊢[PRAAx] denominatorOf b*d ≐ m)
    (h : Γ ⊢[PRAAx] le (scaledLeft a b c d) (scaledLeft b a d c)) : Γ ⊢[PRAAx] rationalLE a b := by
  have positive : Γ ⊢[PRAAx] le one (c*d) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (cofactor_positive a c m hm ha) (cofactor_positive b d m hm hb))
  have first := scaled_left_identity a b c d m ha hb
  have last := (congrMul (mul_comm c d) (.eqRefl (left b a))).eqTrans (scaled_left_identity b a d c m hb ha)
  exact positive_cancel positive (le_congr first.eqSymm last.eqSymm (le_mul_mono (le_refl m) h))

theorem strict_clear (a b c d m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (ha : Γ ⊢[PRAAx] denominatorOf a*c ≐ m) (hb : Γ ⊢[PRAAx] denominatorOf b*d ≐ m)
    (h : Γ ⊢[PRAAx] rationalLT a b) : Γ ⊢[PRAAx] lt (scaledLeft a b c d) (scaledLeft b a d c) := by
  refine .orE (lt_or_le (scaledLeft a b c d) (scaledLeft b a d c)) Prf.hyp0 ?_
  have reversed := weak_unclear b a d c m hm.wk hb.wk ha.wk Prf.hyp0
  exact .botE _ (le_lt_absurd _ reversed h.wk)

/-- The computed original rational width numerator and the computed integer
width obey exact denominator clearing; all numerator signs are allowed. -/
theorem width_clears (a b c d m : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (ha : Γ ⊢[PRAAx] denominatorOf a*c ≐ m) (hb : Γ ⊢[PRAAx] denominatorOf b*d ≐ m)
    (h : Γ ⊢[PRAAx] rationalLT a b) :
    Γ ⊢[PRAAx] (denominatorOf a*denominatorOf b)*scaledGap a b c d ≐ m*gap a b := by
  have A := natEq ha
  have B := natEq hb
  simp only [Q.mk_mul, map_mul] at A B
  unfold scaledGap gap
  ipra_lc [left, scaledLeft, scaled] ((𝔞((numeratorOf b).pos)-𝔞((numeratorOf b).neg))*𝔞(denominatorOf a))*B- ((𝔞((numeratorOf a).pos)-𝔞((numeratorOf a).neg))*𝔞(denominatorOf b))*A- (𝔞(denominatorOf a)*𝔞(denominatorOf b))*natEq (eq_add_of_le (le_of_lt (strict_clear a b c d m hm ha hb h)))+
    𝔞 m*natEq (eq_add_of_le (le_of_lt h))

theorem width_clears_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 4) ⟶ (denominatorOf (var 0)*var 2 ≐ var 4) ⟶
        (denominatorOf (var 1)*var 3 ≐ var 4) ⟶ rationalLT (var 0) (var 1) ⟶
          ((denominatorOf (var 0)*denominatorOf (var 1))*scaledGap (var 0) (var 1) (var 2) (var 3) ≐
            var 4*gap (var 0) (var 1))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (width_clears (var 0) (var 1) (var 2) (var 3) (var 4)
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem weak_clear_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 4) ⟶ (denominatorOf (var 0)*var 2 ≐ var 4) ⟶
        (denominatorOf (var 1)*var 3 ≐ var 4) ⟶ rationalLE (var 0) (var 1) ⟶
          le (scaledLeft (var 0) (var 1) (var 2) (var 3)) (scaledLeft (var 1) (var 0) (var 3) (var 2))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (weak_clear (var 0) (var 1) (var 2) (var 3) (var 4)
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiRationalScaling

export_ipra DiophantineNumberTheory.MinkowskiRationalScaling (rationalLT)
