import IPRADerivations.Analysis.RationalArithmetic.RationalFiniteSum
import IPRADerivations.DiophantineNumberTheory.MinkowskiCenters
import IPRADerivations.Core.LinearCombination

/-!
# Actual rational finite sums commute with scalar multiplication

The scaled summand is an actual fixed PR program, using the same canonical
rational multiplication as the slab checker. Quantifier-free induction on
the raw accumulator proves homogeneity uniformly in the numerical length.
Each independently normalized term and sum retains its own denominator.
The final statement is literal equality of canonical output codes, including
zero, negative, noncanonical input scalars and the empty sum.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalSumLinearity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArithmetic (multiply multiplyF represents)
open LeanProofs.IPRA.Analysis.RationalFiniteSum
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def scaledBody (A : PTm 2) : PTm 2 :=
  ap2 multiplyF (fstT (var 1)) (ap2 (PTm.toPR A) (var 0) (sndT (var 1)))
def scaledSum (A : PTm 2) (N c x : PTm n) : PTm n := sum (scaledBody A) N (pairT c x)

@[simp] theorem subst_scaledSum {m : ℕ} (σ : Fin n → PTm m) (A : PTm 2) (N c x : PTm n) :
    Syn.subst σ (scaledSum A N c x) = scaledSum A (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ x) := by
  simp only [scaledSum,subst_sum,subst_pairT]

theorem scaled_term (A : PTm 2) (i c x : PTm n) :
    Γ ⊢[PRAAx] term (scaledBody A) i (pairT c x) ≐ multiply c (term A i x) := by
  change Γ ⊢[PRAAx] inst2 (scaledBody A) i (pairT c x) ≐ _
  simp only [scaledBody,inst2,subst_ap2,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  have atom : Γ ⊢[PRAAx] ap2 (PTm.toPR A) i (sndT (pairT c x)) ≐ term A i x :=
    (congrAp2 (PTm.toPR A) (.eqRefl i) (snd_pair c x)).eqTrans (toPR_eq A ![i,x])
  exact (congrAp2 multiplyF (fst_pair c x) atom).eqTrans
      (RationalArithmetic.multiply_at c (term A i x))

theorem scaled_term_value (A : PTm 2) (i c x : PTm n) : Γ ⊢[PRAAx]
    represents (term (scaledBody A) i (pairT c x))
      (numeratorOf c*numeratorOf (term A i x)) (denominatorOf c*denominatorOf (term A i x)) := by
  apply ZT.derive
  have val := ZT.toZ_eq (RationalArithmetic.multiply_value (Γ := Γ) c (term A i x))
  have code := scaled_term (Γ := Γ) A i c x
  have p := natEq (congrFst (congrFst code))
  have q := natEq (congrSnd (congrFst code))
  have d := natEq (congrSucc (congrSnd code))
  simp only [represents,RationalArithmetic.productDenominator,ZT.toZ_mul,ZT.toZ_ofNat] at val ⊢
  simp only [ZT.toZ] at val ⊢
  change _ = _ at p q d
  rw [show 𝔞(denominatorOf (term (scaledBody A) i (pairT c x))) =
    𝔞(denominatorOf (multiply c (term A i x))) from d]
  simp only [numeratorOf] at p q ⊢
  rw [p,q]
  exact val

def rawScale (A : PTm 2) (N c x : PTm n) : Fm PTm n :=
  ZT.eq (numerator (scaledBody A) N (pairT c x)*ZT.ofNat (denominatorOf c*denominator A N x))
    (numeratorOf c*numerator A N x*ZT.ofNat (denominator (scaledBody A) N (pairT c x)))

@[simp] theorem subst_rawScale {m : ℕ} (σ : Fin n → PTm m) (A : PTm 2) (N c x : PTm n) :
    (rawScale A N c x).subst σ = rawScale A (Syn.subst σ N) (Syn.subst σ c) (Syn.subst σ x) := by
  simp only [rawScale,ZT.subst_eq,ZT.subst_mul,ZT.subst_ofNat,subst_numerator,
    PTm.subst_mul,RationalSupMetric.subst_denominatorOf,RationalSupMetric.subst_numeratorOf,
    subst_denominator,subst_pairT]

theorem raw_scale_zero (A : PTm 2) (c x : PTm n) : Γ ⊢[PRAAx] rawScale A zero c x := by
  apply ZT.derive
  have pa := natEq (positive_zero (Γ := Γ) A x)
  have qa := natEq (negative_zero (Γ := Γ) A x)
  have pb := natEq (positive_zero (Γ := Γ) (scaledBody A) (pairT c x))
  have qb := natEq (negative_zero (Γ := Γ) (scaledBody A) (pairT c x))
  simp only [rawScale,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  rw [pa,qa,pb,qb]
  ring

theorem raw_scale_succ (A : PTm 2) (N c x : PTm n)
    (h : Γ ⊢[PRAAx] rawScale A N c x) : Γ ⊢[PRAAx] rawScale A (succ N) c x := by
  apply ZT.derive
  have ih := ZT.toZ_eq h
  have ht := ZT.toZ_eq (scaled_term_value (Γ := Γ) A N c x)
  have sa := ZT.toZ_eq (numerator_succ (Γ := Γ) A N x)
  have sb := ZT.toZ_eq (numerator_succ (Γ := Γ) (scaledBody A) N (pairT c x))
  have da := natEq (denominator_succ (Γ := Γ) A N x)
  have db := natEq (denominator_succ (Γ := Γ) (scaledBody A) N (pairT c x))
  simp only [rawScale,represents,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at ih ht sa sb ⊢
  simp only [Q.mk_mul,map_mul] at da db ih ht ⊢
  rw [sa,sb,da,db]
  linear_combination
    𝔞(denominatorOf (term A N x))*𝔞(denominatorOf (term (scaledBody A) N (pairT c x)))*ih+
    -𝔞(denominator A N x)*𝔞(denominator (scaledBody A) N (pairT c x))*ht

theorem raw_scale (A : PTm 2) (N c x : PTm n) : Γ ⊢[PRAAx] rawScale A N c x := by
  have all : Γ ⊢[PRAAx] .all (rawScale A (var 0) (Syn.shift c) (Syn.shift x)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simp only [subst_rawScale,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact raw_scale_zero A c x
    · simp only [Fm.subst_imp,subst_rawScale,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact raw_scale_succ A _ _ _ Prf.hyp0
  simpa only [subst_rawScale,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

/-- The actual finite scalar multiple equals multiplying the actual sum.
The canceled factor is only the proved-positive raw denominator product. -/
theorem sum_homogeneous (A : PTm 2) (N c x : PTm n) : Γ ⊢[PRAAx]
    scaledSum A N c x ≐ multiply c (sum A N x) := by
  apply canonical_equal _ _ _ _ _ _ (sum_well_formed (scaledBody A) N (pairT c x))
    (RationalArithmetic.multiply_guard c (sum A N x))
    (sum_value (scaledBody A) N (pairT c x)) (RationalArithmetic.multiply_value c (sum A N x))
    (denominator_positive (scaledBody A) N (pairT c x)) (RationalArithmetic.product_denominator_positive c (sum A N x))
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (denominator A N x) _ _
    (denominator_positive A N x)
  ipra_lc [rawScale, RationalArithmetic.productDenominator] 𝔞(denominatorOf (sum A N x))*ZT.toZ_eq (raw_scale (Γ := Γ) A N c x)+ ZT.toZ Γ (numeratorOf c)*𝔞(denominator (scaledBody A) N (pairT c x))*ZT.toZ_eq (sum_value (Γ := Γ) A N x)

def scaledSumF (A : PTm 2) : PR 3 := PTm.toPR (scaledSum A (var 0) (var 1) (var 2))

theorem scaled_sum_at (A : PTm 2) (N c x : PTm n) : Γ ⊢[PRAAx]
    ap3 (scaledSumF A) N c x ≐ scaledSum A N c x := by
  simpa only [scaledSumF,ap3,subst_scaledSum,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (scaledSum A (var 0) (var 1) (var 2) : PTm 3) ![N,c,x]

theorem raw_scale_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rawScale A (var 0) (var 1) (var 2)) := closeUniv 3 (raw_scale A _ _ _)

theorem sum_homogeneous_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scaledSum A (var 0) (var 1) (var 2) ≐ multiply (var 1) (sum A (var 0) (var 2))) :=
  closeUniv 3 (sum_homogeneous A _ _ _)

theorem scaled_sum_program_closed (A : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (scaledSumF A) (var 0) (var 1) (var 2) ≐ multiply (var 1) (sum A (var 0) (var 2))) :=
  closeUniv 3 ((scaled_sum_at A _ _ _).eqTrans (sum_homogeneous A _ _ _))

end LeanProofs.IPRA.Analysis.RationalSumLinearity
