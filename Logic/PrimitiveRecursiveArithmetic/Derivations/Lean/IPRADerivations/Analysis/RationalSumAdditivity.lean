import IPRADerivations.Analysis.RationalFiniteSum
import IPRADerivations.DiophantineNumberTheory.MinkowskiCenters

/-!
# Actual rational finite sums commute with pointwise addition

The added term is an actual fixed primitive recursive program applied to
two fixed term families and independently supplied persistent data. Three
actual numerator accumulators and their independent denominator products
satisfy a quantifier-free prefix identity. Final gcd normalization gives
literal equality with addition of the two canonical sum outputs.

The numerical length and both data inputs are internal. Terms can be
signed and use arbitrary decoded positive denominators. No desired global
sum identity or common denominator is a hypothesis. This is numerical
additivity, a dependency of physical Minkowski linear transport.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalSumAdditivity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArithmetic (add addF represents)
open LeanProofs.IPRA.Analysis.RationalFiniteSum
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def addedBody (A B : PTm 2) : PTm 2 := ap2 addF
  (ap2 (PTm.toPR A) (var 0) (fstT (var 1)))
  (ap2 (PTm.toPR B) (var 0) (sndT (var 1)))
def addedSum (A B : PTm 2) (N x y : PTm n) : PTm n := sum (addedBody A B) N (pairT x y)

@[simp] theorem subst_addedSum {m : ℕ} (σ : Fin n → PTm m) (A B : PTm 2) (N x y : PTm n) :
    Syn.subst σ (addedSum A B N x y) = addedSum A B (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) := by
  simp only [addedSum,subst_sum,subst_pairT]

theorem added_term (A B : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    term (addedBody A B) i (pairT x y) ≐ add (term A i x) (term B i y) := by
  change Γ ⊢[PRAAx] inst2 (addedBody A B) i (pairT x y) ≐ _
  simp only [addedBody,inst2,subst_ap2,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have a : Γ ⊢[PRAAx] ap2 (PTm.toPR A) i (fstT (pairT x y)) ≐ term A i x :=
    (congrAp2 (PTm.toPR A) (.eqRefl i) (fst_pair x y)).eqTrans (toPR_eq A ![i,x])
  have b : Γ ⊢[PRAAx] ap2 (PTm.toPR B) i (sndT (pairT x y)) ≐ term B i y :=
    (congrAp2 (PTm.toPR B) (.eqRefl i) (snd_pair x y)).eqTrans (toPR_eq B ![i,y])
  exact (congrAp2 addF a b).eqTrans (RationalArithmetic.add_at _ _)

theorem added_term_value (A B : PTm 2) (i x y : PTm n) : Γ ⊢[PRAAx]
    represents (term (addedBody A B) i (pairT x y))
      (numeratorOf (term A i x)*ZT.ofNat (denominatorOf (term B i y))+
        numeratorOf (term B i y)*ZT.ofNat (denominatorOf (term A i x)))
      (denominatorOf (term A i x)*denominatorOf (term B i y)) := by
  apply ZT.derive
  have val := ZT.toZ_eq (RationalArithmetic.add_value (Γ := Γ) (term A i x) (term B i y))
  have code := added_term (Γ := Γ) A B i x y
  have p := natEq (congrFst (congrFst code))
  have q := natEq (congrSnd (congrFst code))
  have d := natEq (congrSucc (congrSnd code))
  simp only [represents,RationalArithmetic.productDenominator,RationalArithmetic.addNumerator,
    ZT.toZ_mul,ZT.toZ_ofNat] at val ⊢
  simp only [ZT.toZ] at val ⊢
  rw [show 𝔞(denominatorOf (term (addedBody A B) i (pairT x y))) =
    𝔞(denominatorOf (add (term A i x) (term B i y))) from d]
  simp only [numeratorOf] at p q ⊢
  rw [p,q]
  exact val

/-- Raw fractions satisfy W*DA*DB=(UA*DB+UB*DA)*DC. All three
products are the actual independently computed denominator programs. -/
def rawAdd (A B : PTm 2) (N x y : PTm n) : Fm PTm n :=
  ZT.eq (numerator (addedBody A B) N (pairT x y)*ZT.ofNat (denominator A N x*denominator B N y))
    ((numerator A N x*ZT.ofNat (denominator B N y)+numerator B N y*ZT.ofNat (denominator A N x))*
      ZT.ofNat (denominator (addedBody A B) N (pairT x y)))

@[simp] theorem subst_rawAdd {m : ℕ} (σ : Fin n → PTm m) (A B : PTm 2) (N x y : PTm n) :
    (rawAdd A B N x y).subst σ = rawAdd A B (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) := by
  simp only [rawAdd,ZT.subst_eq,ZT.subst_mul,ZT.subst_add,ZT.subst_ofNat,subst_numerator,
    PTm.subst_mul,subst_denominator,subst_pairT]

theorem raw_add_zero (A B : PTm 2) (x y : PTm n) : Γ ⊢[PRAAx] rawAdd A B zero x y := by
  apply ZT.derive
  have pa := natEq (positive_zero (Γ := Γ) A x)
  have qa := natEq (negative_zero (Γ := Γ) A x)
  have pb := natEq (positive_zero (Γ := Γ) B y)
  have qb := natEq (negative_zero (Γ := Γ) B y)
  have pc := natEq (positive_zero (Γ := Γ) (addedBody A B) (pairT x y))
  have qc := natEq (negative_zero (Γ := Γ) (addedBody A B) (pairT x y))
  simp only [rawAdd,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  rw [pa,qa,pb,qb,pc,qc]
  ring

/-- The step is qa*qb*qc times the old equality minus DA*DB*DC
 times the actual new-term addition equality. No denominators cancel. -/
theorem raw_add_succ (A B : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] rawAdd A B N x y) : Γ ⊢[PRAAx] rawAdd A B (succ N) x y := by
  apply ZT.derive
  have ih := ZT.toZ_eq h
  have ht := ZT.toZ_eq (added_term_value (Γ := Γ) A B N x y)
  have sa := ZT.toZ_eq (numerator_succ (Γ := Γ) A N x)
  have sb := ZT.toZ_eq (numerator_succ (Γ := Γ) B N y)
  have sc := ZT.toZ_eq (numerator_succ (Γ := Γ) (addedBody A B) N (pairT x y))
  have da := natEq (denominator_succ (Γ := Γ) A N x)
  have db := natEq (denominator_succ (Γ := Γ) B N y)
  have dc := natEq (denominator_succ (Γ := Γ) (addedBody A B) N (pairT x y))
  simp only [rawAdd,represents,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at ih ht sa sb sc ⊢
  simp only [Q.mk_mul,map_mul] at da db dc ih ht ⊢
  rw [sa,sb,sc,da,db,dc]
  linear_combination
    𝔞(denominatorOf (term A N x))*𝔞(denominatorOf (term B N y))*
      𝔞(denominatorOf (term (addedBody A B) N (pairT x y)))*ih-
    𝔞(denominator A N x)*𝔞(denominator B N y)*
      𝔞(denominator (addedBody A B) N (pairT x y))*ht

theorem raw_add (A B : PTm 2) (N x y : PTm n) : Γ ⊢[PRAAx] rawAdd A B N x y := by
  have all : Γ ⊢[PRAAx] .all (rawAdd A B (var 0) (Syn.shift x) (Syn.shift y)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_rawAdd,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact raw_add_zero A B x y
    · simp only [subst_rawAdd,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact raw_add_succ A B _ _ _ Prf.hyp0
  simpa only [subst_rawAdd,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

/-- Literal canonical additivity of the actual finite-sum outputs. The
only canceled factor is the proved-positive original denominator product. -/
theorem sum_additive (A B : PTm 2) (N x y : PTm n) : Γ ⊢[PRAAx]
    addedSum A B N x y ≐ add (sum A N x) (sum B N y) := by
  apply canonical_equal _ _ _ _ _ _ (sum_well_formed (addedBody A B) N (pairT x y))
    (RationalArithmetic.add_guard _ _) (sum_value (addedBody A B) N (pairT x y))
    (RationalArithmetic.add_value _ _) (denominator_positive (addedBody A B) N (pairT x y))
    (RationalArithmetic.product_denominator_positive _ _)
  have positive : Γ ⊢[PRAAx] le one (denominator A N x*denominator B N y) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (denominator_positive A N x) (denominator_positive B N y))
  apply DiophantineNumberTheory.MinkowskiCenters.integer_cancel (denominator A N x*denominator B N y) _ _ positive
  apply ZT.derive
  have ih := ZT.toZ_eq (raw_add (Γ := Γ) A B N x y)
  have va := ZT.toZ_eq (sum_value (Γ := Γ) A N x)
  have vb := ZT.toZ_eq (sum_value (Γ := Γ) B N y)
  simp only [rawAdd,RationalArithmetic.productDenominator,RationalArithmetic.addNumerator,
    ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at ih va vb ⊢
  ipra_simps
  linear_combination
    𝔞(denominatorOf (sum A N x))*𝔞(denominatorOf (sum B N y))*ih+
    𝔞(denominator (addedBody A B) N (pairT x y))*𝔞(denominator B N y)*
      𝔞(denominatorOf (sum B N y))*va+
    𝔞(denominator (addedBody A B) N (pairT x y))*𝔞(denominator A N x)*
      𝔞(denominatorOf (sum A N x))*vb

def addedSumF (A B : PTm 2) : PR 3 := PTm.toPR (addedSum A B (var 0) (var 1) (var 2))

theorem added_sum_at (A B : PTm 2) (N x y : PTm n) : Γ ⊢[PRAAx]
    ap3 (addedSumF A B) N x y ≐ addedSum A B N x y := by
  simpa only [addedSumF,ap3,subst_addedSum,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      toPR_eq (Γ := Γ) (addedSum A B (var 0) (var 1) (var 2) : PTm 3) ![N,x,y]

theorem raw_add_closed (A B : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rawAdd A B (var 0) (var 1) (var 2)) := closeUniv 3 (raw_add A B _ _ _)

theorem sum_additive_closed (A B : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (addedSum A B (var 0) (var 1) (var 2) ≐ add (sum A (var 0) (var 1)) (sum B (var 0) (var 2))) :=
  closeUniv 3 (sum_additive A B _ _ _)

theorem added_sum_program_closed (A B : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (addedSumF A B) (var 0) (var 1) (var 2) ≐ add (sum A (var 0) (var 1)) (sum B (var 0) (var 2))) :=
  closeUniv 3 ((added_sum_at A B _ _ _).eqTrans (sum_additive A B _ _ _))

end LeanProofs.IPRA.Analysis.RationalSumAdditivity
