import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.Search
import IPRADerivations.Core.LinearCombination

/-!
# An actual small rational factor from a finite product bound

Finite-demand source04 `lem:product-stability`, the bounded-search dependency.
For fixed numerator/denominator bodies `P,Q`, the program searches the actual
finite comparisons `B P_i ≤ A Q_i`. Its success is derived from the exact
product comparison `B^N ∏P_i ≤ A^N ∏Q_i`, with `N≥1`. A quantifier-free
prefix induction proves the strict-product contradiction when every factor
comparison fails. No positive tolerance or supplied successful search is
used: `A=0`, repeated factors and equality at the threshold are included.

This is the finite arithmetic factor selector. It does not yet connect
Gaussian distance products with polynomial evaluation or coefficient error.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalProductWitness

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def product (P : PTm 2) (N x : PTm n) : PTm n := ap2 (prodF P) N x
def scaledProduct (P : PTm 2) (N B x : PTm n) : PTm n := pw B N*product P N x

ipra_subst product
ipra_subst scaledProduct

theorem scaled_product_zero (P : PTm 2) (B x : PTm n) :
    Γ ⊢[PRAAx] scaledProduct P zero B x ≐ one :=
  (congrMul (pw_zero B) (prod_zero P x)).eqTrans (one_mul one)

theorem scaled_product_succ (P : PTm 2) (N B x : PTm n) :
    Γ ⊢[PRAAx] scaledProduct P (succ N) B x ≐ scaledProduct P N B x*(B*inst2 P N x) := by
  have p := natEq (pw_succ (Γ := Γ) B N)
  have q := natEq (prod_succ (Γ := Γ) P N x)
  apply deriveNat
  unfold scaledProduct product inst2
  ipra_simps
  rw [p,q]; ring

theorem scaled_product_congr (P : PTm 2) {N M B x : PTm n} (h : Γ ⊢[PRAAx] N ≐ M) :
    Γ ⊢[PRAAx] scaledProduct P N B x ≐ scaledProduct P M B x :=
  congrMul (congrAp2 powF h (.eqRefl _)) (congrAp2 (prodF P) h (.eqRefl _))

/-! ## Strict multiplication and the quantifier-free prefix invariant -/

theorem strict_mul_left {a b c : PTm n} (hc : Γ ⊢[PRAAx] le one c) (hab : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] lt (c*a) (c*b) := by
  refine le_of_eq_add (d := c*monus b (succ a)+monus c one) ?_
  ipra_lc 𝔞(c)*natEq (eq_add_of_le hab)+natEq (eq_add_of_le hc)

def allLarge (P Q : PTm 2) (N A B x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    lt (Syn.shift A*inst2 Q (var 0) (Syn.shift x)) (Syn.shift B*inst2 P (var 0) (Syn.shift x)))

ipra_subst allLarge [Fm.subst_all, Fm.subst_imp, subst_lt, PTm.subst_mul, subst_inst2, Syn.subst_var, Syn.up_zero,
    Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem large_at (P Q : PTm 2) (N A B x i : PTm n) (h : Γ ⊢[PRAAx] allLarge P Q N A B x)
    (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] lt (A*inst2 Q i x) (B*inst2 P i x) := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ lt (A*inst2 Q i x) (B*inst2 P i x) := by
    simpa only [allLarge,Fm.subst_imp,subst_lt,PTm.subst_mul,subst_inst2,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE i h
  exact .impE rule hi

theorem strict_step (P Q : PTm 2) (k A B x : PTm n)
    (hp : Γ ⊢[PRAAx] le one (scaledProduct P k B x))
    (hweak : Γ ⊢[PRAAx] le (scaledProduct Q k A x) (scaledProduct P k B x))
    (hfactor : Γ ⊢[PRAAx] lt (A*inst2 Q k x) (B*inst2 P k x)) :
    Γ ⊢[PRAAx] lt (scaledProduct Q (succ k) A x) (scaledProduct P (succ k) B x) :=
  lt_congr (scaled_product_succ Q k A x).eqSymm (scaled_product_succ P k B x).eqSymm
    (lt_of_le_of_lt (mul_le_mul_right (A*inst2 Q k x) hweak) (strict_mul_left hp hfactor))

/-- The invariant contains only inequalities of actual PR terms. The
universal factor contract is a context premise, not the induction formula. -/
theorem prefix_bounds (P Q : PTm 2) (N A B x k : PTm n)
    (h : Γ ⊢[PRAAx] allLarge P Q N A B x) (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] le one (scaledProduct P k B x) ⋏
      le (scaledProduct Q k A x) (scaledProduct P k B x) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      (le one (scaledProduct P (var 0) (Syn.shift B) (Syn.shift x)) ⋏
        le (scaledProduct Q (var 0) (Syn.shift A) (Syn.shift x)) (scaledProduct P (var 0) (Syn.shift B) (Syn.shift x)))) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _,le_QF _ _⟩) [subst_le, subst_scaledProduct]
    · exact .impI (.andI (le_congr (.eqRefl _) (scaled_product_zero P B x).eqSymm (le_refl _))
        (le_congr (scaled_product_zero Q A x).eqSymm (scaled_product_zero P B x).eqSymm (le_refl _)))
    · refine .impI ?_
      let Δ : List (Fm PTm (n+1)) := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶
          (le one (scaledProduct P (var 0) (Syn.shift B) (Syn.shift x)) ⋏
            le (scaledProduct Q (var 0) (Syn.shift A) (Syn.shift x)) (scaledProduct P (var 0) (Syn.shift B) (Syn.shift x)))) :: Γ.map Fm.shift
      have old : Δ ⊢[PRAAx] le one (scaledProduct P (var 0) (Syn.shift B) (Syn.shift x)) ⋏
          le (scaledProduct Q (var 0) (Syn.shift A) (Syn.shift x)) (scaledProduct P (var 0) (Syn.shift B) (Syn.shift x)) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have contract : Δ ⊢[PRAAx] allLarge P Q (Syn.shift N) (Syn.shift A) (Syn.shift B) (Syn.shift x) := by
        simpa only [Fm.shift,subst_allLarge,Syn.shift] using h.shift.wk.wk
      have strict := strict_step P Q (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift x)
        (Prf.andE₁ old) (Prf.andE₂ old) (large_at P Q _ _ _ _ _ contract Prf.hyp0)
      exact .andI (lt_of_le_of_lt (zero_le _) strict) (le_of_lt strict)
  have inst := Prf.allE k all
  simp only [Fm.subst_imp,Fm.subst_and,subst_le,subst_scaledProduct,Syn.subst_var,Syn.inst_zero,
    Syn.subst_inst_shift,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] at inst
  exact .impE inst hk

/-- Strict product comparison, including a zero threshold A. -/
theorem strict_product (P Q : PTm 2) (N A B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] allLarge P Q N A B x) :
    Γ ⊢[PRAAx] lt (scaledProduct Q N A x) (scaledProduct P N B x) := by
  let k := monus N one
  have e : Γ ⊢[PRAAx] N ≐ succ k := (eq_add_of_le hN).eqTrans (by ipra_ring)
  have bound : Γ ⊢[PRAAx] lt k N := le_congr (.eqRefl _) e.eqSymm (le_refl _)
  have initialBounds := prefix_bounds P Q N A B x k h (le_of_lt bound)
  exact lt_congr (scaled_product_congr Q e.eqSymm) (scaled_product_congr P e.eqSymm)
    (strict_step P Q k A B x (Prf.andE₁ initialBounds) (Prf.andE₂ initialBounds) (large_at P Q N A B x k h bound))

/-! ## Actual bounded comparison search and its derived success -/

def data (A B x : PTm n) : PTm n := pairT A (pairT B x)
def comparisonBody (P Q : PTm 2) : PTm 2 :=
  monus (fstT (sndT (var 1))*inst2 P (var 0) (sndT (sndT (var 1))))
    (fstT (var 1)*inst2 Q (var 0) (sndT (sndT (var 1))))
def selected (P Q : PTm 2) (N A B x : PTm n) : PTm n := Search.mu (comparisonBody P Q) N (data A B x)

ipra_subst data
ipra_subst selected [Search.mu]

theorem comparison_at (P Q : PTm 2) (i A B x : PTm n) : Γ ⊢[PRAAx]
    inst2 (comparisonBody P Q) i (data A B x) ≐ monus (B*inst2 P i x) (A*inst2 Q i x) := by
  have a : Γ ⊢[PRAAx] fstT (data A B x) ≐ A := fst_pair _ _
  have b : Γ ⊢[PRAAx] fstT (sndT (data A B x)) ≐ B :=
    (snd_pair _ _).fstE
  have c : Γ ⊢[PRAAx] sndT (sndT (data A B x)) ≐ x :=
    (snd_pair _ _).sndE
  have e : inst2 (comparisonBody P Q) i (data A B x) =
      monus (fstT (sndT (data A B x))*inst2 P i (sndT (sndT (data A B x))))
        (fstT (data A B x)*inst2 Q i (sndT (sndT (data A B x)))) := by
    have es : (fun j : Fin 2 => Syn.subst (![i,data A B x] : Fin 2 → PTm n)
        ((![var 0,sndT (sndT (var 1))] : Fin 2 → PTm 2) j)) = ![i,sndT (sndT (data A B x))] := by
      funext j; fin_cases j <;> simp
    simp [comparisonBody,inst2,Syn.subst_subst,es]
  rw [e]
  exact congrMonus (congrMul b (congrInst2 P (.eqRefl _) c)) (congrMul a (congrInst2 Q (.eqRefl _) c))

theorem failed_factor (P Q : PTm 2) (i A B x : PTm n)
    (h : Γ ⊢[PRAAx] neg (inst2 (comparisonBody P Q) i (data A B x) ≐ zero)) :
    Γ ⊢[PRAAx] lt (A*inst2 Q i x) (B*inst2 P i x) := by
  refine .orE (lt_or_le (A*inst2 Q i x) (B*inst2 P i x)) Prf.hyp0 ?_
  exact .botE _ (.impE h.wk ((comparison_at P Q i A B x).eqTrans Prf.hyp0))

theorem selected_minimal (P Q : PTm 2) (N A B x i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (selected P Q N A B x)) :
    Γ ⊢[PRAAx] lt (A*inst2 Q i x) (B*inst2 P i x) :=
  failed_factor P Q i A B x (Search.search_minimal hi)

theorem all_large_of_no_success (P Q : PTm 2) (N A B x : PTm n)
    (h : Γ ⊢[PRAAx] le N (selected P Q N A B x)) : Γ ⊢[PRAAx] allLarge P Q N A B x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have bound : Δ ⊢[PRAAx] le (Syn.shift N) (selected P Q (Syn.shift N) (Syn.shift A) (Syn.shift B) (Syn.shift x)) := by
    simpa only [Fm.shift,subst_le,subst_selected,Syn.shift] using h.shift.wk
  exact selected_minimal P Q _ _ _ _ _ (lt_of_lt_of_le Prf.hyp0 bound)

/-- The genuine finite product bound forces success of the actual search.
This numerical statement needs neither positive A nor positive factors. -/
theorem selected_found (P Q : PTm 2) (N A B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N)
    (hprod : Γ ⊢[PRAAx] le (scaledProduct P N B x) (scaledProduct Q N A x)) :
    Γ ⊢[PRAAx] lt (selected P Q N A B x) N := by
  refine .orE (lt_or_le (selected P Q N A B x) N) Prf.hyp0 ?_
  have strict := strict_product P Q N A B x hN.wk (all_large_of_no_success P Q _ _ _ _ Prf.hyp0)
  exact le_lt_absurd _ hprod.wk strict

theorem selected_comparison (P Q : PTm 2) (N A B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N)
    (hprod : Γ ⊢[PRAAx] le (scaledProduct P N B x) (scaledProduct Q N A x)) :
    Γ ⊢[PRAAx] le (B*inst2 P (selected P Q N A B x) x) (A*inst2 Q (selected P Q N A B x) x) := by
  have bound := selected_found P Q N A B x hN hprod
  have spec := Search.search_spec (Γ := Γ) (f := comparisonBody P Q) N zero (data A B x)
  exact (comparison_at P Q _ A B x).eqSymm.eqTrans (.impE (Prf.andE₁ (Prf.andE₂ spec)) bound)

theorem selected_least (P Q : PTm 2) (N A B x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N)
    (hsmall : Γ ⊢[PRAAx] le (B*inst2 P i x) (A*inst2 Q i x)) :
    Γ ⊢[PRAAx] le (selected P Q N A B x) i :=
  Prf.andE₂ (Prf.andE₂ (Search.search_found ((comparison_at P Q i A B x).eqTrans hsmall) hi))

/-! ## Positive actual denominator products and the rational output certificate -/

def denominatorGuard (Q : PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ le one (inst2 Q (var 0) (Syn.shift x)))

ipra_subst denominatorGuard [Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, subst_inst2, Syn.subst_var, Syn.up_zero,
    Syn.up_succ, Syn.subst_shift, Syn.shift_subst, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]

theorem denominator_at (Q : PTm 2) (N x i : PTm n) (h : Γ ⊢[PRAAx] denominatorGuard Q N x)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] le one (inst2 Q i x) := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ le one (inst2 Q i x) := by
    simpa only [denominatorGuard,Fm.subst_imp,subst_lt,subst_le,subst_inst2,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using Prf.allE i h
  exact .impE rule hi

theorem denominator_product_positive (Q : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] denominatorGuard Q N x) : Γ ⊢[PRAAx] le one (product Q N x) := by
  have p : Γ ⊢[PRAAx] product Q N x ≐ succ (pred (product Q N x)) := by
    apply prod_pos_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have guard : Δ ⊢[PRAAx] denominatorGuard Q (Syn.shift N) (Syn.shift x) := by
      simpa only [Fm.shift,subst_denominatorGuard,Syn.shift] using h.shift.wk
    have positive := denominator_at Q _ _ _ guard Prf.hyp0
    exact pos_of_eq_succ ((eq_add_of_le positive).eqTrans (by ipra_ring))
  exact le_of_eq_add (d := pred (product Q N x)) (p.eqTrans (by ipra_ring))

def leastFormula (P Q : PTm 2) (N A B x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (selected P Q (Syn.shift N) (Syn.shift A) (Syn.shift B) (Syn.shift x)) ⟶
    lt (Syn.shift A*inst2 Q (var 0) (Syn.shift x)) (Syn.shift B*inst2 P (var 0) (Syn.shift x)))

theorem least_formula (P Q : PTm 2) (N A B x : PTm n) : Γ ⊢[PRAAx] leastFormula P Q N A B x := by
  exact .allI (.impI (selected_minimal P Q _ _ _ _ _ Prf.hyp0))

def correct (P Q : PTm 2) (N A B x : PTm n) : Fm PTm n :=
  lt (selected P Q N A B x) N ⋏
    (le (B*inst2 P (selected P Q N A B x) x) (A*inst2 Q (selected P Q N A B x) x) ⋏
      (le one (inst2 Q (selected P Q N A B x) x) ⋏ leastFormula P Q N A B x))

theorem rational_product_witness (P Q : PTm 2) (N A B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (_hB : Γ ⊢[PRAAx] le one B)
    (hQ : Γ ⊢[PRAAx] denominatorGuard Q N x)
    (hprod : Γ ⊢[PRAAx] le (scaledProduct P N B x) (scaledProduct Q N A x)) :
    Γ ⊢[PRAAx] correct P Q N A B x := by
  have range := selected_found P Q N A B x hN hprod
  exact .andI range (.andI (selected_comparison P Q N A B x hN hprod)
    (.andI (denominator_at Q N x _ hQ range) (least_formula P Q N A B x)))

/-! ## Actual returned index/factor program and zero-threshold certificate -/

def output (P Q : PTm 2) (N A B x : PTm n) : PTm n :=
  pairT (selected P Q N A B x)
    (pairT (inst2 P (selected P Q N A B x) x) (inst2 Q (selected P Q N A B x) x))
def selectedF (P Q : PTm 2) : PR 4 := PTm.toPR (selected P Q (var 0) (var 1) (var 2) (var 3))
def outputF (P Q : PTm 2) : PR 4 := PTm.toPR (output P Q (var 0) (var 1) (var 2) (var 3))
def run (P Q : PTm 2) (N A B x : PTm n) : PTm n := ConciseIPRA.PTm.app (outputF P Q) ![N,A,B,x]

ipra_subst output

theorem selected_at (P Q : PTm 2) (N A B x : PTm n) :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app (selectedF P Q) ![N,A,B,x] ≐ selected P Q N A B x := by
  simpa [selectedF] using toPR_eq (Γ := Γ) (selected P Q (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,A,B,x]

theorem output_at (P Q : PTm 2) (N A B x : PTm n) : Γ ⊢[PRAAx] run P Q N A B x ≐ output P Q N A B x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output P Q (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,A,B,x]

theorem output_index (P Q : PTm 2) (N A B x : PTm n) :
    Γ ⊢[PRAAx] fstT (run P Q N A B x) ≐ selected P Q N A B x :=
  (output_at P Q N A B x).fstE
theorem output_numerator (P Q : PTm 2) (N A B x : PTm n) :
    Γ ⊢[PRAAx] fstT (sndT (run P Q N A B x)) ≐ inst2 P (selected P Q N A B x) x :=
  (output_at P Q N A B x).sndE.fstE
theorem output_denominator (P Q : PTm 2) (N A B x : PTm n) :
    Γ ⊢[PRAAx] sndT (sndT (run P Q N A B x)) ≐ inst2 Q (selected P Q N A B x) x :=
  (output_at P Q N A B x).sndE.sndE

def programCorrect (P Q : PTm 2) (N A B x : PTm n) : Fm PTm n :=
  lt (fstT (run P Q N A B x)) N ⋏
    (le (B*fstT (sndT (run P Q N A B x))) (A*sndT (sndT (run P Q N A B x))) ⋏
      le one (sndT (sndT (run P Q N A B x))))

theorem program_correct (P Q : PTm 2) (N A B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hQ : Γ ⊢[PRAAx] denominatorGuard Q N x)
    (hprod : Γ ⊢[PRAAx] le (scaledProduct P N B x) (scaledProduct Q N A x)) :
    Γ ⊢[PRAAx] programCorrect P Q N A B x := by
  have proof := rational_product_witness P Q N A B x hN hB hQ hprod
  exact .andI (lt_congr (output_index P Q N A B x).eqSymm (.eqRefl _) (Prf.andE₁ proof))
    (.andI (le_congr (congrMul (.eqRefl _) (output_numerator P Q N A B x).eqSymm)
      (congrMul (.eqRefl _) (output_denominator P Q N A B x).eqSymm) (Prf.andE₁ (Prf.andE₂ proof)))
      (le_congr (.eqRefl _) (output_denominator P Q N A B x).eqSymm (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ proof)))))

/-- At zero tolerance the actually returned numerator vanishes. No positive
gap or positive tolerance is introduced by the product argument. -/
theorem zero_threshold_factor (P Q : PTm 2) (N B x : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hprod : Γ ⊢[PRAAx] le (scaledProduct P N B x) (scaledProduct Q N zero x)) :
    Γ ⊢[PRAAx] inst2 P (selected P Q N zero B x) x ≐ zero := by
  have small := selected_comparison P Q N zero B x hN hprod
  have zeroProduct : Γ ⊢[PRAAx] B*inst2 P (selected P Q N zero B x) x ≐ zero :=
    le_antisymm (le_congr (.eqRefl _) (zero_mul _) small) (zero_le _)
  have b : Γ ⊢[PRAAx] B ≐ succ (monus B one) := (eq_add_of_le hB).eqTrans (by ipra_ring)
  exact eq_zero_of_succ_mul ((congrMul b (.eqRefl _)).eqSymm.eqTrans zeroProduct)

/-! ## Closed all-numerical endpoints, fixed factor bodies only external -/

theorem strict_product_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ allLarge P Q (var 0) (var 1) (var 2) (var 3) ⟶
      lt (scaledProduct Q (var 0) (var 1) (var 3)) (scaledProduct P (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (strict_product P Q _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem numerical_witness_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶
      le (scaledProduct P (var 0) (var 2) (var 3)) (scaledProduct Q (var 0) (var 1) (var 3)) ⟶
        (lt (selected P Q (var 0) (var 1) (var 2) (var 3)) (var 0) ⋏
          le (var 2*inst2 P (selected P Q (var 0) (var 1) (var 2) (var 3)) (var 3))
            (var 1*inst2 Q (selected P Q (var 0) (var 1) (var 2) (var 3)) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.andI (selected_found P Q _ _ _ _ Prf.hyp1 Prf.hyp0)
    (selected_comparison P Q _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem rational_witness_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 2) ⟶ denominatorGuard Q (var 0) (var 3) ⟶
      le (scaledProduct P (var 0) (var 2) (var 3)) (scaledProduct Q (var 0) (var 1) (var 3)) ⟶
        correct P Q (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (rational_product_witness P Q _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem program_correct_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 2) ⟶ denominatorGuard Q (var 0) (var 3) ⟶
      le (scaledProduct P (var 0) (var 2) (var 3)) (scaledProduct Q (var 0) (var 1) (var 3)) ⟶
        programCorrect P Q (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (program_correct P Q _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

theorem selected_least_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 4) (var 0) ⟶ le (var 2*inst2 P (var 4) (var 3)) (var 1*inst2 Q (var 4) (var 3)) ⟶
      le (selected P Q (var 0) (var 1) (var 2) (var 3)) (var 4)) :=
  closeUniv 5 (.impI (.impI (selected_least P Q _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem zero_threshold_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶
      le (scaledProduct P (var 0) (var 1) (var 2)) (scaledProduct Q (var 0) zero (var 2)) ⟶
        inst2 P (selected P Q (var 0) zero (var 1) (var 2)) (var 2) ≐ zero) :=
  closeUniv 3 (.impI (.impI (.impI (zero_threshold_factor P Q _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem denominator_product_closed (Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (denominatorGuard Q (var 0) (var 1) ⟶ le one (product Q (var 0) (var 1))) :=
  closeUniv 2 (.impI (denominator_product_positive Q _ _ Prf.hyp0))

theorem programs_closed (P Q : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((ConciseIPRA.PTm.app (selectedF P Q) ![var 0,var 1,var 2,var 3] ≐ selected P Q (var 0) (var 1) (var 2) (var 3)) ⋏
      ((run P Q (var 0) (var 1) (var 2) (var 3) ≐ output P Q (var 0) (var 1) (var 2) (var 3)) ⋏
        ((fstT (run P Q (var 0) (var 1) (var 2) (var 3)) ≐ selected P Q (var 0) (var 1) (var 2) (var 3)) ⋏
          ((fstT (sndT (run P Q (var 0) (var 1) (var 2) (var 3))) ≐ inst2 P (selected P Q (var 0) (var 1) (var 2) (var 3)) (var 3)) ⋏
            (sndT (sndT (run P Q (var 0) (var 1) (var 2) (var 3))) ≐ inst2 Q (selected P Q (var 0) (var 1) (var 2) (var 3)) (var 3)))))) :=
  closeUniv 4 (.andI (selected_at P Q _ _ _ _) (.andI (output_at P Q _ _ _ _)
    (.andI (output_index P Q _ _ _ _) (.andI (output_numerator P Q _ _ _ _) (output_denominator P Q _ _ _ _)))))

end LeanProofs.IPRA.Analysis.RationalProductWitness
