import IPRADerivations.Analysis.GaussianRationalLinearProduct

/-!
# Exact weighted backward budgets for rational approximate factorization

The weights are the actual products of the precomputed source (AF) factors.
A local error recurrence and the next weighted bound imply the previous
bound. All indices, fraction denominators and signed rational error values
are internal; the complete deflation-loop recurrence is not an assumption.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192

namespace LeanProofs.IPRA.Analysis.GaussianWeightedErrorBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianFactorBudget
  (prefixProduct factor L cost eta epsilon prefix_zero prefix_succ prefix_le_L)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticBounds (natCode natCode_represents natCode_multiply add_monotone)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE left)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add multiply represents)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def frac (a F : PTm n) : PTm n := normalize (ZT.ofNat a) F
def weight (N A j u : PTm n) : PTm n := multiply (natCode (prefixProduct N A j)) u
def cap (N A p F j : PTm n) : PTm n := frac (two*p*PTm.monus N j*L N A) F

@[simp] theorem subst_frac {m : ℕ} (σ : Fin n → PTm m) (a F : PTm n) :
    Syn.subst σ (frac a F) = frac (Syn.subst σ a) (Syn.subst σ F) := by
  simp only [frac,RationalIntegerNormalization.subst_normalize,ZT.subst_ofNat]
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (N A j u : PTm n) :
    Syn.subst σ (weight N A j u) = weight (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ j) (Syn.subst σ u) := by
  simp only [weight,RationalArithmetic.subst_multiply,GaussianRationalSyntheticBounds.subst_natCode,GaussianFactorBudget.subst_prefixProduct]
@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (N A p F j : PTm n) :
    Syn.subst σ (cap N A p F j) = cap (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ p) (Syn.subst σ F) (Syn.subst σ j) := by
  simp only [cap,subst_frac,PTm.subst_mul,PTm.subst_monus,GaussianFactorBudget.subst_L,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]

theorem frac_represents (a F : PTm n) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx]
    represents (frac a F) (ZT.ofNat a) F := RationalIntegerNormalization.normalize_preserves_value _ _ hF

theorem frac_congr {a a' F F' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hF : Γ ⊢[PRAAx] F ≐ F') : Γ ⊢[PRAAx]
    frac a F ≐ frac a' F' := by
  simpa only [subst_frac,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (frac (var 0) (var 1) : PTm 2)
      (σ := ![a,F]) (σ' := ![a',F']) (fun i => by fin_cases i; exact ha; exact hF)

theorem frac_add (a b F : PTm n) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx]
    add (frac a F) (frac b F) ≐ frac (a+b) F := by
  have sum := RationalRepresentations.represents_add (Γ := Γ) (frac a F) (frac b F) _ _ _ _
    (frac_represents a F hF) (frac_represents b F hF)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hF) sum (frac_represents (a+b) F hF)
    (RationalAlgebra.positive_product hF hF) hF
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem nat_scale_frac (k a F : PTm n) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx]
    multiply (natCode k) (frac a F) ≐ frac (k*a) F := by
  have product := RationalRepresentations.represents_multiply (Γ := Γ) (natCode k) (frac a F) _ _ _ _
    (natCode_represents k) (frac_represents a F hF)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hF) product (frac_represents (k*a) F hF)
    (RationalAlgebra.positive_product (le_refl one) hF) hF
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem frac_order (a b F : PTm n) (hF : Γ ⊢[PRAAx] le one F) (hab : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (frac a F) (frac b F) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ F F hF hF
    (frac_represents a F hF) (frac_represents b F hF)
    (le_congr (mul_comm a F) (.eqRefl _) (le_mul_mono hab (le_refl F)))

/-- Multiplication by a natural weight is monotone even for arbitrary
signed input fractions. Only the actual comparison gap is scaled. -/
theorem natural_scale_monotone (k u v : PTm n) (h : Γ ⊢[PRAAx] rationalLE u v) : Γ ⊢[PRAAx]
    rationalLE (multiply (natCode k) u) (multiply (natCode k) v) := by
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _
    (RationalRepresentations.represents_multiply _ _ _ _ _ _ (natCode_represents k) (RationalRepresentations.represents_self u))
    (RationalRepresentations.represents_multiply _ _ _ _ _ _ (natCode_represents k) (RationalRepresentations.represents_self v))
    (RationalAlgebra.positive_product (le_refl one) (RationalArgmin.denominator_positive u))
    (RationalAlgebra.positive_product (le_refl one) (RationalArgmin.denominator_positive v))
  apply zle_of_toZ (k*PTm.monus (left v u) (left u v))
  have gap := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  unfold left at gap ⊢
  ipra_simps
  linear_combination -𝔞(k)*gap

theorem natCode_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] natCode a ≐ natCode b :=
  frac_congr h (.eqRefl one)

theorem weight_add (N A j u v : PTm n) : Γ ⊢[PRAAx]
    weight N A j (add u v) ≐ add (weight N A j u) (weight N A j v) := RationalAlgebra.multiply_add _ _ _

theorem weight_factor (N A j v : PTm n) : Γ ⊢[PRAAx]
    weight N A j (multiply (natCode (factor N A j)) v) ≐ weight N A (succ j) v :=
  (RationalAlgebra.multiply_associative _ _ _).eqSymm.eqTrans
    (RationalAlgebra.multiply_congr ((natCode_multiply _ _).eqTrans (natCode_congr (prefix_succ N A j).eqSymm)) (.eqRefl _))

theorem weighted_local_step (u v N A p F j : PTm n) (hF : Γ ⊢[PRAAx] le one F)
    (hstep : Γ ⊢[PRAAx] rationalLE u (add (frac (two*p) F) (multiply (natCode (factor N A j)) v))) : Γ ⊢[PRAAx]
    rationalLE (weight N A j u) (add (frac (prefixProduct N A j*(two*p)) F) (weight N A (succ j) v)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _)
    ((weight_add N A j _ _).eqTrans (RationalAlgebra.add_congr (nat_scale_frac _ _ _ hF) (weight_factor N A j v)))
    (natural_scale_monotone _ _ _ hstep)

theorem cap_step (N A p F j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx]
    add (frac (two*p*L N A) F) (cap N A p F (succ j)) ≐ cap N A p F j := by
  have remaining : Γ ⊢[PRAAx] PTm.monus N j ≐ succ (PTm.monus N (succ j)) := by
    have h : Γ ⊢[PRAAx] N ≐ j+succ (PTm.monus N (succ j)) := (eq_add_of_le hj).eqTrans (by ipra_ring)
    exact (congrMonus h (.eqRefl _)).eqTrans (add_monus' _ _)
  have numerator : Γ ⊢[PRAAx] two*p*L N A+two*p*PTm.monus N (succ j)*L N A ≐ two*p*PTm.monus N j*L N A :=
    (by ipra_ring : Γ ⊢[PRAAx] two*p*L N A+two*p*PTm.monus N (succ j)*L N A ≐ two*p*succ (PTm.monus N (succ j))*L N A).eqTrans
      (congrMul (congrMul (.eqRefl _) remaining.eqSymm) (.eqRefl _))
  exact (frac_add _ _ _ hF).eqTrans (frac_congr numerator (.eqRefl _))

/-- Exact local backward transport of the weighted finite error budget.
The only error inputs are the actual local recurrence and next-stage bound. -/
theorem backward_step (u v N A p F j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) (hF : Γ ⊢[PRAAx] le one F)
    (hstep : Γ ⊢[PRAAx] rationalLE u (add (frac (two*p) F) (multiply (natCode (factor N A j)) v)))
    (hIH : Γ ⊢[PRAAx] rationalLE (weight N A (succ j) v) (cap N A p F (succ j))) : Γ ⊢[PRAAx]
    rationalLE (weight N A j u) (cap N A p F j) := by
  have pref : Γ ⊢[PRAAx] le (prefixProduct N A j*(two*p)) (two*p*L N A) :=
    le_congr (.eqRefl _) (mul_comm (L N A) (two*p))
      (le_mul_mono (prefix_le_L N A j (le_of_lt hj)) (le_refl (two*p)))
  have next := add_monotone _ _ _ _ (frac_order _ _ F hF pref) hIH
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (cap_step N A p F j hj hF)
    (RationalArgmin.transitive (weighted_local_step u v N A p F j hF hstep) next)

/-- The source initial budget is the literal normalized eta code. -/
theorem initial_cap (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    cap N A p (cost N A*q) zero ≐ eta p q := by
  have hF := GaussianFactorBudget.epsilon_denominator_positive N A q hN hq
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hF) (RationalNormalForm.normalize_well_formed _ _ hq)
    (frac_represents _ _ hF) (GaussianFactorBudget.eta_represents p q hq) hF hq
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  have rem := natEq (monus_zero (Γ := Γ) N)
  unfold cost
  ipra_simps
  linear_combination 2*𝔞(p)*𝔞(L N A)*𝔞(q)*rem

/-- Removing the initial unit weight recovers a canonical error code. -/
theorem weight_zero (N A u : PTm n) (hu : Γ ⊢[PRAAx] RationalNormalForm.wellFormed u) : Γ ⊢[PRAAx]
    weight N A zero u ≐ u :=
  (RationalAlgebra.multiply_congr (natCode_congr (prefix_zero N A)) (.eqRefl _)).eqTrans
    ((RationalAlgebra.multiply_commutative _ _).eqTrans (GaussianRationalLinearProduct.scalar_multiply_one u hu))

theorem frac_zero (F : PTm n) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx] frac zero F ≐ natCode zero := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hF) (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (frac_represents _ _ hF) (natCode_represents zero) hF (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem cap_end (N A p F : PTm n) (hF : Γ ⊢[PRAAx] le one F) : Γ ⊢[PRAAx]
    cap N A p F N ≐ natCode zero :=
  (frac_congr ((congrMul (congrMul (.eqRefl _) (monus_self N)) (.eqRefl _)).eqTrans
    (by ipra_ring)) (.eqRefl _)).eqTrans (frac_zero F hF)

theorem two_epsilon (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    add (epsilon N A p q) (epsilon N A p q) ≐ frac (two*p) (cost N A*q) :=
  (frac_add p p _ (GaussianFactorBudget.epsilon_denominator_positive N A q hN hq)).eqTrans
    (frac_congr (by ipra_ring) (.eqRefl _))

/-- A zero terminal error remains zero under every actual prefix weight. -/
theorem weight_of_zero (N A j : PTm n) : Γ ⊢[PRAAx]
    weight N A j (natCode zero) ≐ natCode zero :=
  (natCode_multiply _ _).eqTrans (natCode_congr (mul_zero _))

theorem weight_congr (N A : PTm n) {j j' u u' : PTm n} (hj : Γ ⊢[PRAAx] j ≐ j')
    (hu : Γ ⊢[PRAAx] u ≐ u') : Γ ⊢[PRAAx] weight N A j u ≐ weight N A j' u' :=
  RationalAlgebra.multiply_congr (natCode_congr (congrAp2 (prodF GaussianFactorBudget.factorBody) hj (.eqRefl _))) hu

theorem cap_index_congr (N A p F : PTm n) {j j' : PTm n} (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    cap N A p F j ≐ cap N A p F j' :=
  frac_congr (congrMul (congrMul (.eqRefl _) (congrMonus (.eqRefl _) hj)) (.eqRefl _)) (.eqRefl _)

/-! Fixed actual PR programs and uniformly closed endpoints. -/
def weightF : PR 4 := PTm.toPR (weight (var 0) (var 1) (var 2) (var 3))
def capF : PR 5 := PTm.toPR (cap (var 0) (var 1) (var 2) (var 3) (var 4))

theorem weight_at (N A j u : PTm n) : Γ ⊢[PRAAx] PTm.app weightF ![N,A,j,u] ≐ weight N A j u := by
  simpa only [weightF,subst_weight,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (weight (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,A,j,u]
theorem cap_at (N A p F j : PTm n) : Γ ⊢[PRAAx] PTm.app capF ![N,A,p,F,j] ≐ cap N A p F j := by
  simpa only [capF,subst_cap,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (cap (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![N,A,p,F,j]

theorem weighted_backward_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (lt (var 6) (var 2) ⟶ le one (var 5) ⟶
      rationalLE (var 0) (add (frac (two*var 4) (var 5)) (multiply (natCode (factor (var 2) (var 3) (var 6))) (var 1))) ⟶
      rationalLE (weight (var 2) (var 3) (succ (var 6)) (var 1)) (cap (var 2) (var 3) (var 4) (var 5) (succ (var 6))) ⟶
      rationalLE (weight (var 2) (var 3) (var 6) (var 0)) (cap (var 2) (var 3) (var 4) (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI
    (backward_step _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem initial_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 3) ⟶
      cap (var 0) (var 1) (var 2) (cost (var 0) (var 1)*var 3) zero ≐ eta (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (initial_cap _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem unit_weight_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalNormalForm.wellFormed (var 2) ⟶ weight (var 0) (var 1) zero (var 2) ≐ var 2) :=
  closeUniv 3 (.impI (weight_zero _ _ _ Prf.hyp0))

theorem final_cap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ cap (var 0) (var 1) (var 2) (var 3) (var 0) ≐ natCode zero) :=
  closeUniv 4 (.impI (cap_end _ _ _ _ Prf.hyp0))

theorem weighted_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((PTm.app weightF ![var 0,var 1,var 4,var 2] ≐ weight (var 0) (var 1) (var 4) (var 2)) ⋏
      (PTm.app capF ![var 0,var 1,var 2,var 3,var 4] ≐ cap (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.andI (weight_at _ _ _ _) (cap_at _ _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianWeightedErrorBudget
