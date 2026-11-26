import IPRADerivations.Analysis.RationalArithmetic.Covers.GaussianRationalCover
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalRadius
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalProductStability

/-!
# Finite product stability for the original Gaussian-rational lists

Finite-demand source04, lem:product-stability. The inputs are original point
lists, the runtime degree N, the original rational radius u/v ≥ 1,
coefficient tolerance A/B ≥ 0, and output radius P/Q ≥ 0. Their scalar
components may have independent reduced denominators, and repeated roots
are allowed. Every numerical input is universally quantified internally.

The actual pool includes the radius u/v, so its computed denominator clears
that radius as well as both root lists. Actual normalized product coefficient
comparisons yield the full source conclusion on the original lists, together
with an accepted original-list checker and an actual original target point.
No common denominator, cleared radius, evaluation bound, factorization law,
raw coefficient error, successful search or desired cover is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalStability

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalRadius
  (radiusQuery scaleDenominator rawRadius scale_positive radius_ge_scale sourceBudget budget_transport)
open LeanProofs.IPRA.Analysis.GaussianRationalNormalization (sourceNumerators targetNumerators)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pointsBounded (S u v : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift S)) ⟶
    GaussianRationalMetric.bounded (entry (Syn.shift S) (var 0)) (Syn.shift u) (Syn.shift v))

@[simp] theorem subst_pointsBounded {m : ℕ} (σ : Fin n → PTm m) (S u v : PTm n) :
    (pointsBounded S u v).subst σ = pointsBounded (Syn.subst σ S) (Syn.subst σ u) (Syn.subst σ v) := by
  simp [pointsBounded,Syn.subst_shift,Syn.shift_subst]

theorem point_bound_at (S u v i : PTm n) (h : Γ ⊢[PRAAx] pointsBounded S u v)
    (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (entry S i) u v := by
  have rule : Γ ⊢[PRAAx] lt i (length S) ⟶ GaussianRationalMetric.bounded (entry S i) u v := by
    simpa only [pointsBounded,Fm.subst_imp,subst_lt,subst_length,GaussianRationalMetric.subst_bounded,
      subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE i h
  exact .impE rule hi

def coefficientBounds (S T N u v A B : PTm n) : Fm PTm n :=
  GaussianRationalProductStability.coefficientBounds
    (sourceNumerators S T (radiusQuery u v)) (targetNumerators S T (radiusQuery u v))
    N (scaleDenominator S T u v) A B

def basicInput (S T N u v A B P Q : PTm n) : Fm PTm n :=
  le one N ⋏ (le one v ⋏ (le v u ⋏ (le one B ⋏ (le one Q ⋏
    (length S ≐ N ⋏ (length T ≐ N ⋏ sourceBudget N u v A B P Q))))))
def stabilityInput (S T N u v A B P Q : PTm n) : Fm PTm n := basicInput S T N u v A B P Q ⋏
  (pointsBounded S u v ⋏ (pointsBounded T u v ⋏ coefficientBounds S T N u v A B))

@[simp] theorem subst_coefficientBounds {m : ℕ} (σ : Fin n → PTm m) (S T N u v A B : PTm n) :
    (coefficientBounds S T N u v A B).subst σ = coefficientBounds (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ B) := by simp [coefficientBounds]
@[simp] theorem subst_basicInput {m : ℕ} (σ : Fin n → PTm m) (S T N u v A B P Q : PTm n) :
    (basicInput S T N u v A B P Q).subst σ = basicInput (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ P) (Syn.subst σ Q) := by simp [basicInput]
@[simp] theorem subst_stabilityInput {m : ℕ} (σ : Fin n → PTm m) (S T N u v A B P Q : PTm n) :
    (stabilityInput S T N u v A B P Q).subst σ = stabilityInput (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ N) (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ P) (Syn.subst σ Q) := by simp [stabilityInput]

/-- Original rational point bounds give the actual integer radius bound.
The clearing equations and the commensurate radius are both derived. -/
theorem points_transport (s : GaussianRationalCover.Side) (S T N u v : PTm n)
    (hv : Γ ⊢[PRAAx] le one v)
    (hlen : Γ ⊢[PRAAx] length (GaussianRationalCover.original s S T) ≐ N)
    (h : Γ ⊢[PRAAx] pointsBounded (GaussianRationalCover.original s S T) u v) :
    Γ ⊢[PRAAx] GaussianProductStability.pointsBounded
      (GaussianRationalCover.numerators s S T (radiusQuery u v)) N (rawRadius S T u v) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have vpos : Δ ⊢[PRAAx] le one (Syn.shift v) := by
    simpa only [Δ,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hv.shift.wk
  have shape : Δ ⊢[PRAAx] length (GaussianRationalCover.original s (Syn.shift S) (Syn.shift T)) ≐ Syn.shift N := by
    simpa only [Δ,Fm.shift,Fm.subst_eq,subst_length,GaussianRationalCover.subst_original,Syn.shift] using hlen.shift.wk
  have points : Δ ⊢[PRAAx] pointsBounded (GaussianRationalCover.original s (Syn.shift S) (Syn.shift T)) (Syn.shift u) (Syn.shift v) := by
    simpa only [Δ,Fm.shift,subst_pointsBounded,GaussianRationalCover.subst_original,Syn.shift] using h.shift.wk
  have index : Δ ⊢[PRAAx] lt (var 0) (length (GaussianRationalCover.original s (Syn.shift S) (Syn.shift T))) :=
    lt_congr (.eqRefl _) shape.eqSymm Prf.hyp0
  have rep := GaussianRationalCover.entry_represents s (Syn.shift S) (Syn.shift T)
    (radiusQuery (Syn.shift u) (Syn.shift v)) (var 0) index
  have bound := GaussianRationalRadius.bound_of_representation _ _ (Syn.shift S) (Syn.shift T)
    (Syn.shift u) (Syn.shift v) vpos rep (point_bound_at _ _ _ _ points index)
  simpa only [Δ,ComplexLogarithmRemainder.bounded,Syn.shift,GaussianRationalCover.subst_numerators,
    GaussianRationalRadius.subst_radiusQuery,GaussianRationalRadius.subst_rawRadius] using bound

/-- The source hypotheses construct every input to the common-D theorem.
In particular the error and radius budgets retain their original fractions. -/
theorem cleared_input (S T N u v A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N u v A B P Q) : Γ ⊢[PRAAx]
    GaussianRationalProductStability.stabilityInput
      (sourceNumerators S T (radiusQuery u v)) (targetNumerators S T (radiusQuery u v))
      N (scaleDenominator S T u v) (rawRadius S T u v) A B P Q := by
  have basic := Prf.andE₁ h
  have a := Prf.andE₂ basic; have hv := Prf.andE₁ a
  have b := Prf.andE₂ a; have huv := Prf.andE₁ b
  have c := Prf.andE₂ b; have hB := Prf.andE₁ c
  have d := Prf.andE₂ c; have hQ := Prf.andE₁ d
  have e := Prf.andE₂ d; have hS := Prf.andE₁ e
  have f := Prf.andE₂ e; have hT := Prf.andE₁ f
  have hBudget := Prf.andE₂ f
  have budget : Γ ⊢[PRAAx] GaussianRationalProductStability.sourceCondition N
      (scaleDenominator S T u v) (rawRadius S T u v) A B P Q :=
    le_congr (by ipra_ring) (.eqRefl _) (budget_transport N S T u v A B P Q hv hBudget)
  have rawBasic : Γ ⊢[PRAAx] GaussianRationalProductStability.basicInput
      (sourceNumerators S T (radiusQuery u v)) (targetNumerators S T (radiusQuery u v))
      N (scaleDenominator S T u v) (rawRadius S T u v) A B P Q :=
    .andI (Prf.andE₁ basic) (.andI (scale_positive S T u v) (.andI hB (.andI hQ
      (.andI (radius_ge_scale S T u v hv huv)
        (.andI ((GaussianRationalNormalization.source_length S T _).eqTrans hS)
          (.andI ((GaussianRationalNormalization.target_length S T _).eqTrans hT)
            budget))))))
  exact .andI rawBasic (.andI
    (points_transport .source S T N u v hv hS (Prf.andE₁ (Prf.andE₂ h)))
    (.andI (points_transport .target S T N u v hv hT (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))))
      (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))

theorem raw_close (S T N u v A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N u v A B P Q) : Γ ⊢[PRAAx]
    GaussianRationalCover.rawClose S T (radiusQuery u v) P Q :=
  GaussianRationalProductStability.product_stability _ _ _ _ _ _ _ _ _
    (cleared_input S T N u v A B P Q h)

/-- Full finite product stability on the original independently denominated
point lists, with the exact n R^(n-1) δ ≤ r^n source budget. -/
theorem product_stability (S T N u v A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N u v A B P Q) : Γ ⊢[PRAAx]
    GaussianRationalCover.close S T P Q := by
  have basic := Prf.andE₁ h
  have hN := Prf.andE₁ basic
  have a := Prf.andE₂ basic; have b := Prf.andE₂ a; have c := Prf.andE₂ b
  have d := Prf.andE₂ c; have q := Prf.andE₁ d
  have e := Prf.andE₂ d; have s := Prf.andE₁ e
  have t := Prf.andE₁ (Prf.andE₂ e)
  exact GaussianRationalCover.close_transport S T (radiusQuery u v) P Q
    (le_congr (.eqRefl _) s.eqSymm hN) (le_congr (.eqRefl _) t.eqSymm hN) q
    (raw_close S T N u v A B P Q h)

theorem checker_accepts (S T N u v A B P Q : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N u v A B P Q) : Γ ⊢[PRAAx]
    GaussianRationalCover.check S T P Q ≐ one :=
  (GaussianRationalCover.checker_reflection S T P Q).iffMpr (product_stability S T N u v A B P Q h)

/-! One actual PR6 program returns an original target-list index and point. -/

def witnessTerm (S T u v i Q : PTm n) : PTm n :=
  GaussianRationalCover.run .source S T (radiusQuery u v) i Q
def witnessF : PR 6 := PTm.toPR (witnessTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def witness (S T u v i Q : PTm n) : PTm n := PTm.app witnessF ![S,T,u,v,i,Q]

@[simp] theorem subst_witnessTerm {m : ℕ} (σ : Fin n → PTm m) (S T u v i Q : PTm n) :
    Syn.subst σ (witnessTerm S T u v i Q) = witnessTerm (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ i) (Syn.subst σ Q) := by simp [witnessTerm]

theorem witness_program_at (S T u v i Q : PTm n) : Γ ⊢[PRAAx]
    witness S T u v i Q ≐ witnessTerm S T u v i Q := by
  simpa [witness,witnessF] using toPR_eq (Γ := Γ)
    (witnessTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![S,T,u,v,i,Q]

theorem original_witness (S T N u v A B P Q i : PTm n)
    (h : Γ ⊢[PRAAx] stabilityInput S T N u v A B P Q) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] lt (fstT (witness S T u v i Q)) (length T) ⋏
      (sndT (witness S T u v i Q) ≐ entry T (fstT (witness S T u v i Q)) ⋏
        GaussianRationalMetric.distanceBounded (entry S i) (sndT (witness S T u v i Q)) P Q) := by
  have basic := Prf.andE₁ h
  have hN := Prf.andE₁ basic
  have a := Prf.andE₂ basic; have b := Prf.andE₂ a; have c := Prf.andE₂ b
  have d := Prf.andE₂ c; have q := Prf.andE₁ d
  have e := Prf.andE₂ d; have f := Prf.andE₂ e; have t := Prf.andE₁ f
  have out := GaussianRationalCover.output_certificate .source S T (radiusQuery u v) P Q i
    (le_congr (.eqRefl _) t.eqSymm hN) q (Prf.andE₁ (raw_close S T N u v A B P Q h)) hi
  have program := witness_program_at (Γ := Γ) S T u v i Q
  exact .andI (lt_congr (congrFst program).eqSymm (.eqRefl _) (Prf.andE₁ out))
    (.andI ((congrSnd program).eqTrans ((Prf.andE₁ (Prf.andE₂ out)).eqTrans
      (Foundations.SequenceComposition.entry_congr (.eqRefl _) (congrFst program).eqSymm)))
      (GaussianRationalCover.distance_congr (.eqRefl _) (congrSnd program).eqSymm
        (.eqRefl _) (.eqRefl _) (Prf.andE₂ (Prf.andE₂ out))))

/-! Closed original-coordinate source endpoints. -/

theorem original_product_stability_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianRationalCover.close (var 0) (var 1) (var 7) (var 8)) :=
  closeUniv 9 (.impI (product_stability _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_product_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianRationalCover.check (var 0) (var 1) (var 7) (var 8) ≐ one) :=
  closeUniv 9 (.impI (checker_accepts _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem original_product_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (stabilityInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      lt (var 9) (length (var 0)) ⟶
      (lt (fstT (witness (var 0) (var 1) (var 3) (var 4) (var 9) (var 8))) (length (var 1)) ⋏
        (sndT (witness (var 0) (var 1) (var 3) (var 4) (var 9) (var 8)) ≐
          entry (var 1) (fstT (witness (var 0) (var 1) (var 3) (var 4) (var 9) (var 8))) ⋏
          GaussianRationalMetric.distanceBounded (entry (var 0) (var 9))
            (sndT (witness (var 0) (var 1) (var 3) (var 4) (var 9) (var 8))) (var 7) (var 8)))) :=
  closeUniv 10 (.impI (.impI (original_witness _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_witness_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (witness (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐
      GaussianRationalCover.run .source (var 0) (var 1) (radiusQuery (var 2) (var 3)) (var 4) (var 5)) :=
  closeUniv 6 (witness_program_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalStability
