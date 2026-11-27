import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalFiniteSum
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentations

/-!
# Actual numerical budgets for rational approximate factorization

Finite-demand Section 4, (AF): the coefficient bounds A_j, factors 2A_j+5,
their product L, and epsilon=eta/(2NL) are actual primitive recursive
programs. Prefix inequalities and the final rational error budget are
ordinary object-theory derivations. The numerical degree and every index
remain internal. Actual synthetic division, residual production and the
outer deflation/telescoping proof remain separate dependencies.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFactorBudget

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry subst_sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization (normalize positive_form)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def five : PTm n := succ (succ (succ (succ one)))
def boundStep : PTm 3 := (var 1+one)*pw (two*var 1+five) (fstT (var 2))
def boundF : PR 2 := rec2 (sndT (var 0)) boundStep
def bound (N A j : PTm n) : PTm n := ap2 boundF j (pairT N A)
def factor (N A j : PTm n) : PTm n := two*bound N A j+five

def factorBody : PTm 2 := two*ap2 boundF (var 0) (var 1)+five
def prefixProduct (N A j : PTm n) : PTm n := ap2 (prodF factorBody) j (pairT N A)
def L (N A : PTm n) : PTm n := prefixProduct N A N
def prefixBody : PTm 2 := ap2 (prodF factorBody) (var 0) (var 1)
def prefixSum (N A j : PTm n) : PTm n := ap2 (sumF prefixBody) j (pairT N A)

ipra_subst five
ipra_subst bound
ipra_subst factor
ipra_subst prefixProduct
@[simp] theorem subst_L {m : ℕ} (σ : Fin n → PTm m) (N A : PTm n) :
    Syn.subst σ (L N A) = L (Syn.subst σ N) (Syn.subst σ A) := subst_prefixProduct _ _ _ _
ipra_subst prefixSum

theorem bound_zero (N A : PTm n) : Γ ⊢[PRAAx] bound N A zero ≐ A := by
  have h : Γ ⊢[PRAAx] bound N A zero ≐ sndT (pairT N A) := by
    simpa only [bound,boundF,subst_sndT,Syn.subst_var,Matrix.cons_val_zero] using
      rec2_zero (Γ := Γ) (sndT (var 0)) boundStep (pairT N A)
  exact h.eqTrans (snd_pair N A)

theorem bound_succ (N A j : PTm n) : Γ ⊢[PRAAx]
    bound N A (succ j) ≐ (bound N A j+one)*pw (factor N A j) N := by
  have h := rec2_succ (Γ := Γ) (sndT (var 0)) boundStep j (pairT N A)
  have shape : Syn.subst ![j,bound N A j,pairT N A] boundStep =
      (bound N A j+one)*pw (factor N A j) (fstT (pairT N A)) := by
    simp only [boundStep,PTm.subst_mul,PTm.subst_add,subst_ap2,subst_fstT,subst_five,
      Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
    rfl
  change Γ ⊢[PRAAx] bound N A (succ j) ≐ Syn.subst ![j,bound N A j,pairT N A] boundStep at h
  rw [shape] at h
  exact h.eqTrans (congrMul (.eqRefl _) (congrAp2 powF (fst_pair N A) (.eqRefl _)))

theorem factor_positive (N A j : PTm n) : Γ ⊢[PRAAx] le one (factor N A j) := by
  refine le_of_eq_add (d := two*bound N A j+succ (succ (succ one))) ?_
  unfold factor five
  ipra_ring

theorem power_positive (a k : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] le one (pw a k) :=
  le_congr (.eqRefl _) (AnalyticNumberTheory.Valuation.pw_pos' (positive_form ha) k).eqSymm (zero_lt_succ _)

theorem bound_step_monotone (N A j : PTm n) : Γ ⊢[PRAAx] le (bound N A j) (bound N A (succ j)) := by
  have h : Γ ⊢[PRAAx] le ((bound N A j+one)*one) ((bound N A j+one)*pw (factor N A j) N) :=
    le_mul_mono (le_refl _) (power_positive _ N (factor_positive N A j))
  exact le_trans (le_add_right (bound N A j) one)
    (le_congr (by ipra_ring) (bound_succ N A j).eqSymm h)

theorem bound_offset (N A j r : PTm n) : Γ ⊢[PRAAx] le (bound N A j) (bound N A (j+r)) := by
  have all : Γ ⊢[PRAAx] .all (le (bound (Syn.shift N) (Syn.shift A) (Syn.shift j))
      (bound (Syn.shift N) (Syn.shift A) (Syn.shift j+var 0))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_bound]
    · exact le_congr (.eqRefl _) (congrAp2 boundF (add_zero _) (.eqRefl _)).eqSymm (le_refl _)
    · have step := bound_step_monotone (Γ := Γ.map Fm.shift) (Syn.shift N) (Syn.shift A) (Syn.shift j+var 0)
      exact le_trans Prf.hyp0 (le_congr (.eqRefl _) (congrAp2 boundF (add_succ _ _) (.eqRefl _)).eqSymm step.wk)
  simpa only [subst_le,subst_bound,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem bound_monotone (N A i j : PTm n) (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    le (bound N A i) (bound N A j) :=
  le_congr (.eqRefl _) (congrAp2 boundF (eq_add_of_le hij).eqSymm (.eqRefl _)) (bound_offset N A i (PTm.monus j i))

theorem bound_positive (N A j : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le one (bound N A j) :=
  le_trans hA (le_congr (bound_zero N A) (.eqRefl _) (bound_monotone N A zero j (zero_le _)))

theorem factorBody_at (N A j : PTm n) : inst2 factorBody j (pairT N A) = factor N A j := by
  simp only [factorBody,inst2,PTm.subst_add,PTm.subst_mul,subst_ap2,subst_five,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  rfl

theorem prefix_zero (N A : PTm n) : Γ ⊢[PRAAx] prefixProduct N A zero ≐ one := prod_zero _ _
theorem prefix_succ (N A j : PTm n) : Γ ⊢[PRAAx]
    prefixProduct N A (succ j) ≐ prefixProduct N A j*factor N A j := by
  have h : Γ ⊢[PRAAx] prefixProduct N A (succ j) ≐ prefixProduct N A j*inst2 factorBody j (pairT N A) :=
    prod_succ factorBody j (pairT N A)
  simpa only [factorBody_at] using h

theorem prefix_positive (N A j : PTm n) : Γ ⊢[PRAAx] le one (prefixProduct N A j) := by
  refine prod_one_le_bounded factorBody (pairT N A) j (.allI (.impI ?_))
  simp only [Syn.shift, subst_pairT]
  rw [factorBody_at]
  exact factor_positive _ _ _

theorem prefix_step_monotone (N A j : PTm n) : Γ ⊢[PRAAx]
    le (prefixProduct N A j) (prefixProduct N A (succ j)) :=
  le_congr (by ipra_ring) (prefix_succ N A j).eqSymm
    (le_mul_mono (le_refl _) (factor_positive N A j))

theorem prefix_offset (N A j r : PTm n) : Γ ⊢[PRAAx] le (prefixProduct N A j) (prefixProduct N A (j+r)) := by
  have all : Γ ⊢[PRAAx] .all (le (prefixProduct (Syn.shift N) (Syn.shift A) (Syn.shift j))
      (prefixProduct (Syn.shift N) (Syn.shift A) (Syn.shift j+var 0))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_prefixProduct]
    · exact le_congr (.eqRefl _) (congrAp2 (prodF factorBody) (add_zero _) (.eqRefl _)).eqSymm (le_refl _)
    · have step := prefix_step_monotone (Γ := Γ.map Fm.shift) (Syn.shift N) (Syn.shift A) (Syn.shift j+var 0)
      exact le_trans Prf.hyp0 (le_congr (.eqRefl _) (congrAp2 (prodF factorBody) (add_succ _ _) (.eqRefl _)).eqSymm step.wk)
  simpa only [subst_le,subst_prefixProduct,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE r

theorem prefix_le_L (N A j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] le (prefixProduct N A j) (L N A) :=
  le_congr (.eqRefl _) (congrAp2 (prodF factorBody) (eq_add_of_le hj).eqSymm (.eqRefl _))
    (prefix_offset N A j (PTm.monus N j))

theorem L_positive (N A : PTm n) : Γ ⊢[PRAAx] le one (L N A) := prefix_positive _ _ _

theorem prefixBody_at (N A j : PTm n) : inst2 prefixBody j (pairT N A) = prefixProduct N A j := by
  simp only [prefixBody,inst2,subst_ap2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

theorem prefixSum_zero (N A : PTm n) : Γ ⊢[PRAAx] prefixSum N A zero ≐ zero := sum_zero _ _
theorem prefixSum_succ (N A j : PTm n) : Γ ⊢[PRAAx]
    prefixSum N A (succ j) ≐ prefixSum N A j+prefixProduct N A j := by
  have h : Γ ⊢[PRAAx] prefixSum N A (succ j) ≐ prefixSum N A j+inst2 prefixBody j (pairT N A) :=
    sum_succ prefixBody j (pairT N A)
  simpa only [prefixBody_at] using h

theorem prefixSum_bound (N A j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] le (prefixSum N A j) (j*L N A) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      le (prefixSum (Syn.shift N) (Syn.shift A) (var 0)) (var 0*L (Syn.shift N) (Syn.shift A))) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_le, subst_prefixSum, subst_L]
    · exact .impI (le_congr (prefixSum_zero N A).eqSymm (zero_mul _).eqSymm (le_refl _))
    · refine .impI ?_
      let IH := le (var 0) (Syn.shift N) ⟶
        le (prefixSum (Syn.shift N) (Syn.shift A) (var 0)) (var 0*L (Syn.shift N) (Syn.shift A))
      let Δ := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have bound : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      have ih : Δ ⊢[PRAAx] le (prefixSum (Syn.shift N) (Syn.shift A) (var 0))
          (var 0*L (Syn.shift N) (Syn.shift A)) := .impE Prf.hyp1 bound
      exact le_congr (prefixSum_succ _ _ _).eqSymm (by ipra_ring)
        (sum_mono ih (prefix_le_L _ _ _ bound))
  have out : Γ ⊢[PRAAx] le j N ⟶ le (prefixSum N A j) (j*L N A) := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixSum,PTm.subst_mul,subst_L,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE out hj

/-! ## The local coefficient recurrence estimate -/

def recurrence (b : PR 2) (N A Z x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ le (ap2 b (succ (var 0)) (Syn.shift x))
    (Syn.shift A+Syn.shift Z*ap2 b (var 0) (Syn.shift x)))

ipra_subst recurrence [Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift, Syn.shift_subst]

theorem recurrence_at (b : PR 2) (N A Z x k : PTm n) (h : Γ ⊢[PRAAx] recurrence b N A Z x)
    (hk : Γ ⊢[PRAAx] lt k N) : Γ ⊢[PRAAx] le (ap2 b (succ k) x) (A+Z*ap2 b k x) := by
  have all : Γ ⊢[PRAAx] lt k N ⟶ le (ap2 b (succ k) x) (A+Z*ap2 b k x) := by
    simpa only [Fm.subst_imp,subst_lt,subst_le,PTm.subst_add,PTm.subst_mul,subst_ap2,
      ConciseIPRA.PTm.subst_succ,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE k
  exact .impE all hk

theorem recurrence_step (b : PR 2) (A Z x k : PTm n)
    (ih : Γ ⊢[PRAAx] le (ap2 b k x) ((A+one)*pw (one+Z) k))
    (hs : Γ ⊢[PRAAx] le (ap2 b (succ k) x) (A+Z*ap2 b k x)) : Γ ⊢[PRAAx]
    le (ap2 b (succ k) x) ((A+one)*pw (one+Z) (succ k)) := by
  have hpow := power_positive (Γ := Γ) (one+Z) k (le_add_right one Z)
  have base : Γ ⊢[PRAAx] le A ((A+one)*pw (one+Z) k) :=
    le_trans (le_add_right A one)
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (A+one)) hpow))
  have step := sum_mono base (le_mul_mono (le_refl Z) ih)
  have eq : Γ ⊢[PRAAx] (A+one)*pw (one+Z) k+Z*((A+one)*pw (one+Z) k) ≐
      (A+one)*pw (one+Z) (succ k) := by
    have e := natEq (pw_succ (Γ := Γ) (one+Z) k)
    apply deriveNat
    ipra_simps
    rw [e]
    ring
  exact le_congr (.eqRefl _) eq (le_trans hs step)

/-- The only supplied program law is the genuine bounded local recurrence.
The QF induction derives the entire prefix bound, starting from b_0≤1. -/
theorem recurrence_prefix (b : PR 2) (N A Z x k : PTm n)
    (hzero : Γ ⊢[PRAAx] le (ap2 b zero x) one) (hrec : Γ ⊢[PRAAx] recurrence b N A Z x)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] le (ap2 b k x) ((A+one)*pw (one+Z) k) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift N) ⟶
      le (ap2 b (var 0) (Syn.shift x)) ((Syn.shift A+one)*pw (one+Syn.shift Z) (var 0))) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_le, subst_ap2]
    · have low : Γ ⊢[PRAAx] le one ((A+one)*pw (one+Z) zero) := by
        refine le_of_eq_add (d := A) ?_
        exact (congrMul (.eqRefl _) (pw_zero _)).eqTrans (by ipra_ring)
      exact .impI (le_trans hzero low).wk
    · refine .impI ?_
      let IH := le (var 0) (Syn.shift N) ⟶ le (ap2 b (var 0) (Syn.shift x))
        ((Syn.shift A+one)*pw (one+Syn.shift Z) (var 0))
      let Δ := le (succ (var 0)) (Syn.shift N) :: IH :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] le (ap2 b (var 0) (Syn.shift x)) ((Syn.shift A+one)*pw (one+Syn.shift Z) (var 0)) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)
      have contract : Γ.map Fm.shift ⊢[PRAAx] recurrence b (Syn.shift N) (Syn.shift A) (Syn.shift Z) (Syn.shift x) := by
        simpa only [Fm.shift,subst_recurrence,Syn.shift] using hrec.shift
      exact recurrence_step b _ _ _ _ ih (recurrence_at b _ _ _ _ _ contract.wk.wk Prf.hyp0)
  have inst : Γ ⊢[PRAAx] le k N ⟶ le (ap2 b k x) ((A+one)*pw (one+Z) k) := by
    simpa only [Fm.subst_imp,subst_le,subst_ap2,PTm.subst_add,PTm.subst_mul,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE inst hk

theorem power_monotone_length (a j k : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hjk : Γ ⊢[PRAAx] le j k) : Γ ⊢[PRAAx] le (pw a j) (pw a k) := by
  have eq : Γ ⊢[PRAAx] pw a k ≐ pw a j*pw a (PTm.monus k j) :=
    (congrAp2 powF (eq_add_of_le hjk) (.eqRefl _)).eqTrans (pw_add _ _ _)
  exact le_congr (by ipra_ring) eq.eqSymm
    (le_mul_mono (le_refl (pw a j)) (power_positive a _ ha))

theorem recurrence_bound (b : PR 2) (N A Z x k : PTm n)
    (hzero : Γ ⊢[PRAAx] le (ap2 b zero x) one) (hrec : Γ ⊢[PRAAx] recurrence b N A Z x)
    (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] le (ap2 b k x) ((A+one)*pw (one+Z) N) :=
  le_trans (recurrence_prefix b N A Z x k hzero hrec hk)
    (le_mul_mono (le_refl _) (power_monotone_length _ k N (le_add_right one Z) hk))

/-! ## The actual normalized rational epsilon and exact final budget -/

def cost (N A : PTm n) : PTm n := two*N*L N A
def eta (p q : PTm n) : PTm n := normalize (ZT.ofNat p) q
def epsilon (N A p q : PTm n) : PTm n := normalize (ZT.ofNat p) (cost N A*q)
def costCode (N A : PTm n) : PTm n := normalize (ZT.ofNat (cost N A)) one
def unitCode : PTm n := normalize (ZT.ofNat one) one

ipra_subst cost
ipra_subst eta
ipra_subst epsilon

theorem cost_positive (N A : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] le one (cost N A) := by
  have twoPos : Γ ⊢[PRAAx] le one (two : PTm n) := le_of_eq_add (d := one) (by ipra_ring)
  exact le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_mul_mono twoPos hN) (L_positive N A))

theorem epsilon_denominator_positive (N A q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] le one (cost N A*q) :=
  le_congr (one_mul one) (.eqRefl _) (le_mul_mono (cost_positive N A hN) hq)

theorem epsilon_represents (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (epsilon N A p q) (ZT.ofNat p) (cost N A*q) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (epsilon_denominator_positive N A q hN hq)

theorem eta_represents (p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (eta p q) (ZT.ofNat p) q :=
  RationalIntegerNormalization.normalize_preserves_value _ _ hq

theorem epsilon_le_one (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE (epsilon N A p q) unitCode := by
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _ (epsilon_represents N A p q hN hq)
    (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one))
    (epsilon_denominator_positive N A q hN hq) (le_refl one)
  have raw : Γ ⊢[PRAAx] le p (cost N A*q) := le_trans hpq
    (le_congr (one_mul q) (.eqRefl _) (le_mul_mono (cost_positive N A hN) (le_refl q)))
  apply zle_of_toZ (PTm.monus (cost N A*q) p)
  have gap := natEq (eq_add_of_le raw)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -gap

/-- Multiplying the actual normalized epsilon by the actual integer 2NL
returns the literal canonical eta code, not merely an informal fraction. -/
theorem epsilon_product (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    RationalArithmetic.multiply (epsilon N A p q) (costCode N A) ≐ eta p q := by
  have left := RationalRepresentations.represents_multiply (Γ := Γ) (epsilon N A p q) (costCode N A) _ _ _ _
    (epsilon_represents N A p q hN hq) (RationalIntegerNormalization.normalize_preserves_value _ _ (le_refl one))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.multiply_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hq) left (eta_represents p q hq)
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono (epsilon_denominator_positive N A q hN hq) (le_refl one))) hq
  ipra_lc

/-- Positive raw rational data force the actual output signed numerator to
have a positive natural positive part. Only D>0 is canceled. -/
theorem positive_numerator (c p D : PTm n) (hp : Γ ⊢[PRAAx] le one p)
    (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] RationalArithmetic.represents c (ZT.ofNat p) D) : Γ ⊢[PRAAx]
    le one (RationalIntegerNormalization.positivePart (numeratorOf c)) := by
  have value := ZT.toZ_eq h
  simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at value
  simp only [ZT.toZ] at value
  have scaled : Γ ⊢[PRAAx] le (D*(numeratorOf c).neg) (D*(numeratorOf c).pos) := by
    refine le_of_eq_add (d := p*denominatorOf c) ?_
    ipra_lc -value
  have nonnegative := RationalValueBounds.positive_cancel hD scaled
  have gap := natEq (eq_add_of_le nonnegative)
  have difference : Γ ⊢[PRAAx] p*denominatorOf c ≐ D*RationalIntegerNormalization.positivePart (numeratorOf c) := by
    apply deriveNat
    unfold RationalIntegerNormalization.positivePart
    ipra_simps
    linear_combination value+𝔞(D)*gap
  have productPos : Γ ⊢[PRAAx] le one (p*denominatorOf c) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hp (RationalArgmin.denominator_positive c))
  refine .orE (zero_or_succ (RationalIntegerNormalization.positivePart (numeratorOf c))) ?_ ?_
  · have eq : (RationalIntegerNormalization.positivePart (numeratorOf c) ≐ zero) :: Γ ⊢[PRAAx]
        p*denominatorOf c ≐ zero := difference.wk.eqTrans
      ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
    exact lt_zero_absurd _ (le_congr (.eqRefl _) eq productPos.wk)
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)

theorem epsilon_positive (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    le one (RationalIntegerNormalization.positivePart (numeratorOf (epsilon N A p q))) :=
  positive_numerator _ _ _ hp (epsilon_denominator_positive N A q hN hq) (epsilon_represents N A p q hN hq)

/-- This actual normalized fraction is 2 epsilon times the actual sum of
prefix products, the accumulated (TE) numerical error majorant. -/
def errorBudget (N A p q : PTm n) : PTm n :=
  normalize (ZT.ofNat (two*p*prefixSum N A N)) (cost N A*q)

ipra_subst errorBudget

theorem error_budget_cleared (N A p q : PTm n) : Γ ⊢[PRAAx]
    le ((two*p*prefixSum N A N)*q) (p*(cost N A*q)) := by
  have h := le_mul_mono (le_refl (two*p*q)) (prefixSum_bound (Γ := Γ) N A N (le_refl _))
  exact le_congr (by ipra_ring) (by unfold cost; ipra_ring) h

theorem error_budget_le_eta (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] RationalArgmin.rationalLE (errorBudget N A p q) (eta p q) := by
  apply RationalArithmetic.order_of_representations _ _ _ _ _ _
    (RationalIntegerNormalization.normalize_preserves_value _ _ (epsilon_denominator_positive N A q hN hq))
    (eta_represents p q hq) (epsilon_denominator_positive N A q hN hq) hq
  apply zle_of_toZ (PTm.monus (p*(cost N A*q)) ((two*p*prefixSum N A N)*q))
  have gap := natEq (eq_add_of_le (error_budget_cleared (Γ := Γ) N A p q))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination -gap

/-- The source hypotheses 0<eta≤1 produce a positive epsilon≤1, the exact
final budget identity, and the actual accumulated-prefix budget inequality. -/
theorem epsilon_parameters (N A p q : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hp : Γ ⊢[PRAAx] le one p) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    le one (RationalIntegerNormalization.positivePart (numeratorOf (epsilon N A p q))) ⋏
      (RationalArgmin.rationalLE (epsilon N A p q) unitCode ⋏
        ((RationalArithmetic.multiply (epsilon N A p q) (costCode N A) ≐ eta p q) ⋏
          RationalArgmin.rationalLE (errorBudget N A p q) (eta p q))) := by
  have hq := le_trans hp hpq
  exact .andI (epsilon_positive N A p q hN hp hq) (.andI (epsilon_le_one N A p q hN hq hpq)
    (.andI (epsilon_product N A p q hN hq) (error_budget_le_eta N A p q hN hq)))

/-! ## Actual precomputed tables and fixed output metadata -/

def boundBody : PTm 2 := ap2 boundF (var 0) (var 1)
def boundList (N A : PTm n) : PTm n := sequence boundBody (succ N) (pairT N A)
def factorList (N A : PTm n) : PTm n := sequence factorBody N (pairT N A)

ipra_subst boundList
ipra_subst factorList

theorem boundList_length (N A : PTm n) : Γ ⊢[PRAAx] length (boundList N A) ≐ succ N := sequence_length _ _ _
theorem factorList_length (N A : PTm n) : Γ ⊢[PRAAx] length (factorList N A) ≐ N := sequence_length _ _ _

theorem boundList_lookup (N A j : PTm n) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    entry (boundList N A) j ≐ bound N A j := by
  simpa only [boundList,bound,boundBody,inst2,subst_ap2,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    sequence_decode (Γ := Γ) boundBody (x := pairT N A) ((succ_monus_succ _ _).eqTrans hj)

theorem factorList_lookup (N A j : PTm n) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    entry (factorList N A) j ≐ factor N A j := by
  have h : Γ ⊢[PRAAx] entry (factorList N A) j ≐ inst2 factorBody j (pairT N A) := sequence_decode _ hj
  simpa only [factorBody_at] using h

def budgetOutput (N A p q : PTm n) : PTm n := pairT (boundList N A) (pairT (factorList N A)
  (pairT (L N A) (pairT (prefixSum N A N) (pairT (cost N A) (epsilon N A p q)))))
def budgetF : PR 4 := PTm.toPR (budgetOutput (var 0) (var 1) (var 2) (var 3))

ipra_subst budgetOutput

theorem budget_program (N A p q : PTm n) : Γ ⊢[PRAAx]
    ConciseIPRA.PTm.app budgetF ![N,A,p,q] ≐ budgetOutput N A p q := by
  simpa only [budgetF,subst_budgetOutput,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (budgetOutput (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,A,p,q]

/-! ## Universally closed source-linked numerical statements -/

theorem bound_recurrence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((bound (var 0) (var 1) zero ≐ var 1) ⋏
      (bound (var 0) (var 1) (succ (var 2)) ≐
        (bound (var 0) (var 1) (var 2)+one)*pw (factor (var 0) (var 1) (var 2)) (var 0))) :=
  closeUniv 3 (.andI (bound_zero _ _) (bound_succ _ _ _))

theorem bound_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 2) (var 3) ⟶ le (bound (var 0) (var 1) (var 2)) (bound (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (bound_monotone _ _ _ _ Prf.hyp0))

theorem bound_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (bound (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (bound_positive _ _ _ Prf.hyp0))

theorem prefix_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 0) ⟶
      (le one (L (var 0) (var 1)) ⋏
        (le (prefixProduct (var 0) (var 1) (var 2)) (L (var 0) (var 1)) ⋏
          le (prefixSum (var 0) (var 1) (var 2)) (var 2*L (var 0) (var 1))))) :=
  closeUniv 3 (.impI (.andI (L_positive _ _) (.andI (prefix_le_L _ _ _ Prf.hyp0) (prefixSum_bound _ _ _ Prf.hyp0))))

theorem recurrence_bound_closed (b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (ap2 b zero (var 3)) one ⟶ recurrence b (var 0) (var 1) (var 2) (var 3) ⟶
      le (var 4) (var 0) ⟶ le (ap2 b (var 4) (var 3)) ((var 1+one)*pw (one+var 2) (var 0))) :=
  closeUniv 5 (.impI (.impI (.impI (recurrence_bound b _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem epsilon_parameters_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ le one (var 2) ⟶ le (var 2) (var 3) ⟶
      (le one (RationalIntegerNormalization.positivePart (numeratorOf (epsilon (var 0) (var 1) (var 2) (var 3)))) ⋏
        (RationalArgmin.rationalLE (epsilon (var 0) (var 1) (var 2) (var 3)) unitCode ⋏
          ((RationalArithmetic.multiply (epsilon (var 0) (var 1) (var 2) (var 3)) (costCode (var 0) (var 1)) ≐ eta (var 2) (var 3)) ⋏
            RationalArgmin.rationalLE (errorBudget (var 0) (var 1) (var 2) (var 3)) (eta (var 2) (var 3)))))) :=
  closeUniv 4 (.impI (.impI (.impI (epsilon_parameters _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem budget_tables_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (boundList (var 0) (var 1)) ≐ succ (var 0)) ⋏
      ((length (factorList (var 0) (var 1)) ≐ var 0) ⋏
        ((le (var 2) (var 0) ⟶ entry (boundList (var 0) (var 1)) (var 2) ≐ bound (var 0) (var 1) (var 2)) ⋏
          (lt (var 2) (var 0) ⟶ entry (factorList (var 0) (var 1)) (var 2) ≐ factor (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.andI (boundList_length _ _) (.andI (factorList_length _ _)
    (.andI (.impI (boundList_lookup _ _ _ Prf.hyp0)) (.impI (factorList_lookup _ _ _ Prf.hyp0)))))

theorem budget_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ConciseIPRA.PTm.app budgetF ![var 0,var 1,var 2,var 3] ≐ budgetOutput (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (budget_program _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianFactorBudget
