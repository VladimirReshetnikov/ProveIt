/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Compat.Core
import OAI.Compat.Measurable
import Mathlib.MeasureTheory.Group.Prod
import OAI.Combinatorics.Progressions.Estimates.AllocatedTailProfileIdentity
import OAI.Combinatorics.Progressions.Polynomial.SlicedProfilePolynomial
import OAI.Combinatorics.Progressions.Probability.SiteDensityRestriction

namespace OAI

section

namespace Erdos3

open MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

variable {D G E : Type*} [Fintype D] [Fintype G] [Fintype E]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (axis : E → D)

local notation "Input" => (Σ e, B (axis e) × Fin (h (axis e)))
local notation "Output" => (Σ _e : E, Unit)

noncomputable def jointSlicedProfileValue
    (ρ γ ε : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (t : ℝ) (x : Input → ℝ) (o : Output) : ℝ :=
  MvPolynomial.eval (fun k => MvPolynomial.eval x (ξ o.1 k))
    (monomialArrayPolynomial Subtype.val (fun j : SamplerCoefficientSlot G B h (axis o.1) =>
      coefficientProfileCenter (principalCoefficientSlots h (axis o.1)) (γ (axis o.1)) j +
        coefficientProfileWidth (principalCoefficientSlots h (axis o.1)) (constantCoefficientSlot _ _)
          (ρ (axis o.1)) (γ (axis o.1)) (t * ε (axis o.1)) j * r o.1 j))

noncomputable def jointSlicedProfilePrincipal
    (γ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (e : E) (b : B (axis e)) : ℝ :=
  3 * γ (axis e) / 2 + γ (axis e) / 2 * r e (principalCoefficientSlot h (axis e) b)

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_mul
    (R ρ γ ε : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ) (t : ℝ) (x : Input → ℝ) :
    jointSlicedProfileValue h axis (fun d => R d * ρ d) (fun d => R d * γ d)
        (fun d => R d * ε d) r ξ t x =
      fun o => R (axis o.1) * jointSlicedProfileValue h axis ρ γ ε r ξ t x o := by
  classical
  funext o
  have hs : t * (R (axis o.1) * ε (axis o.1)) = R (axis o.1) * (t * ε (axis o.1)) := by ring
  unfold jointSlicedProfileValue
  simp_rw [hs, coefficientProfileCenter_mul, coefficientProfileWidth_mul, monomialArrayPolynomial_eval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_unit_scale
    (R : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ) (t : ℝ) (x : Input → ℝ) :
    jointSlicedProfileValue h axis (fun d => R d / 4)
        (fun d => principalProfileSize (R d) (Fintype.card (B d)))
        (fun d => tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d))) r ξ t x =
      fun o => R (axis o.1) * jointSlicedProfileValue h axis (fun _ => 1 / 4)
        (unitProfilePrincipalSize (B := B)) (unitProfileTailSize (G := G) (B := B) h) r ξ t x o := by
  have hp (d : D) : principalProfileSize (R d) (Fintype.card (B d)) =
      R d * unitProfilePrincipalSize (B := B) d := by
    simpa only [unitProfilePrincipalSize, mul_one] using principalProfileSize_mul (R d) 1 (Fintype.card (B d))
  have ht (d : D) : tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d)) =
      R d * unitProfileTailSize (G := G) (B := B) h d := by
    simpa only [unitProfileTailSize, mul_one] using tailProfileSize_mul (R d) 1 1
      (Fintype.card (SamplerCoefficientSlot G B h d))
  simp_rw [hp, ht, div_eq_mul_inv, one_mul]
  exact jointSlicedProfileValue_mul h axis R (fun _ => 4⁻¹) _ _ r ξ t x

noncomputable def jointSlicedProfileShift
    (ρ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (o : Output) : ℝ :=
  ρ (axis o.1) * r o.1 (constantCoefficientSlot _ _)

noncomputable def jointSlicedProfileTail
    (ε : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ) (o : Output) : MvPolynomial Input ℝ :=
  slicedProfileTailPolynomial h (axis o.1) (ε (axis o.1)) (r o.1) (ξ o.1)

omit [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfileValue_split
    (hh : ∀ e, 0 < h (axis e)) (ρ γ ε : D → ℝ)
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (t : ℝ) :
    jointSlicedProfileValue h axis ρ γ ε r ξ t = fun x =>
      jointSlicedProfileShift h axis ρ r +
        jointSlicedPrincipal (jointSlicedProfilePrincipal h axis γ r) lower width x +
        t • polynomialVectorMap (jointSlicedProfileTail h axis ε r ξ) x := by
  funext x o
  rw [jointSlicedProfileValue, slicedProfile_eval_split h (axis o.1) (hh o.1)]
  simp only [hξ, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rfl

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_bounds
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) (b : B (axis e)) :
    unitProfilePrincipalSize (B := B) (axis e) ≤
      |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ∧
    |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b| ≤
      2 * unitProfilePrincipalSize (B := B) (axis e) := by
  have hγ := unitProfilePrincipalSize_pos (B := B) (axis e)
  obtain ⟨hl, hu⟩ := abs_le.mp (hr e (principalCoefficientSlot h (axis e) b))
  have hlo : unitProfilePrincipalSize (B := B) (axis e) ≤
      jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b := by
    unfold jointSlicedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold jointSlicedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype E] [∀ index, DecidableEq (B index)] in
theorem jointSlicedProfilePrincipal_unit_mass
    (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ) (hr : ∀ e j, |r e j| ≤ 1)
    (e : E) :
    (∑ b, |jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r e b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl
    (Fintype.card (B (axis e))) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B (axis e), 2 * unitProfilePrincipalSize (B := B) (axis e) :=
      Finset.sum_le_sum (fun b _ => (jointSlicedProfilePrincipal_unit_bounds h axis r hr e b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B (axis e))) * Fintype.card (B (axis e)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

theorem jointSlicedProfileValue_unit_comparison
    {m : ℕ} (hh : ∀ e, 0 < h (axis e)) (hm : ∀ e, h (axis e) ≤ m)
    (ρ : D → ℝ) (r : ∀ e, SamplerCoefficientSlot G B h (axis e) → ℝ)
    (hr : ∀ e j, |r e j| ≤ 1)
    (ξ : E → SamplerTupleIndex G B h → MvPolynomial Input ℝ)
    (hξdegree : ∀ e k, (ξ e k).totalDegree ≤ 1)
    (hξmass : ∀ e k, realPolynomialMass (ξ e k) ≤ 1)
    (lower width : ∀ e, B (axis e) × Fin (h (axis e)) → ℝ)
    (hξ : ∀ e b i, ξ e (.inr ⟨axis e, b, i⟩) =
      MvPolynomial.C (lower e (b, i)) + MvPolynomial.C (width e (b, i)) * MvPolynomial.X ⟨e, b, i⟩)
    (hwidth : ∀ e p, |lower e p| + |width e p| ≤ 1)
    (b : ∀ e, B (axis e)) (i : ∀ e, Fin (h (axis e)))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ e, a ≤ unitProfilePrincipalSize (B := B) (axis e))
    (hw : ∀ e j, δ ≤ width e (b e, j))
    (hlower : ∀ e j, j ≠ i e → 0 ≤ lower e (b e, j))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (t : ℝ)
    (ht : |t| * polynomialMassC2Budget (Fintype.card Input) m 1 ≤
      slicedPrincipalC2Tolerance (Fintype.card Input) (Fintype.card E) m 1 a δ A η)
    (φ : (Output → ℝ) → ℝ) (hφ : Measurable φ) (hφone : ∀ y, ‖φ y‖ ≤ 1) :
    |mappedTest (unitBoxMeasure Input)
        (fun x => jointSlicedProfileShift h axis ρ r +
          jointSlicedPrincipal (jointSlicedProfilePrincipal h axis (unitProfilePrincipalSize (B := B)) r)
            lower width x) φ -
      mappedTest (unitBoxMeasure Input)
        (jointSlicedProfileValue h axis ρ (unitProfilePrincipalSize (B := B))
          (unitProfileTailSize (G := G) (B := B) h) r ξ t) φ| ≤ η := by
  classical
  rw [jointSlicedProfileValue_split h axis hh ρ _ _ r ξ lower width hξ t]
  apply jointSlicedPrincipal_polynomial_tail_comparison _ lower width b i
    (by simpa only [Fintype.card_fin] using hm) zero_le_one zero_le_one ha hδ hδone hη A hA hwidth
    (jointSlicedProfilePrincipal_unit_mass h axis r hr)
    (fun e => (hprincipal e).trans (jointSlicedProfilePrincipal_unit_bounds h axis r hr e (b e)).1)
    hw hlower _ _ _ t ht _ φ hφ hφone
  · intro o v
    exact (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      ((slicedProfileTailPolynomial_degree h (axis o.1) _ (r o.1) (ξ o.1) (hξdegree o.1)).trans (hm o.1))
  · intro o
    exact slicedProfileTailPolynomial_unit_mass h (axis o.1) (r o.1) (hr o.1) (ξ o.1) (hξmass o.1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G : Type*} {B : D → Type*} (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P]

abbrev OneCubeActiveRow := Bool × {d // ¬P d}
abbrev OneCubeActiveEndpoint := Σ e : OneCubeActiveRow P, B e.2.val × Fin (h e.2.val)

variable (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)

noncomputable def oneCubeProfileSubstitution
    (frozen : Bool → SamplerTupleIndex G B h → ℝ)
    (e : OneCubeActiveRow P) : SamplerTupleIndex G B h → MvPolynomial (OneCubeActiveEndpoint (B := B) h P) ℝ
  | .inl g => MvPolynomial.C (frozen e.1 (.inl g))
  | .inr ⟨d, b, i⟩ =>
      if hd : P d then MvPolynomial.C (frozen e.1 (.inr ⟨d, b, i⟩)) else
        MvPolynomial.C (lower ⟨d, hd⟩ (b, i)) + MvPolynomial.C (width ⟨d, hd⟩ (b, i)) *
          MvPolynomial.X ⟨(e.1, ⟨d, hd⟩), b, i⟩

theorem oneCubeProfileSubstitution_principal
    (frozen : Bool → SamplerTupleIndex G B h → ℝ)
    (e : OneCubeActiveRow P) (b : B e.2.val) (i : Fin (h e.2.val)) :
    oneCubeProfileSubstitution h P lower width frozen e (.inr ⟨e.2.val, b, i⟩) =
      MvPolynomial.C (lower e.2 (b, i)) + MvPolynomial.C (width e.2 (b, i)) * MvPolynomial.X ⟨e, b, i⟩ := by
  simp only [oneCubeProfileSubstitution, e.2.property, ↓reduceDIte]

theorem oneCubeProfileSubstitution_degree
    (frozen : Bool → SamplerTupleIndex G B h → ℝ)
    (e : OneCubeActiveRow P) (k : SamplerTupleIndex G B h) :
    (oneCubeProfileSubstitution h P lower width frozen e k).totalDegree ≤ 1 := by
  rcases k with g | ⟨d, b, i⟩
  · simp [oneCubeProfileSubstitution]
  · by_cases hd : P d
    · simp [oneCubeProfileSubstitution, hd]
    · simp only [oneCubeProfileSubstitution, hd, ↓reduceDIte]
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem oneCubeProfileSubstitution_mass
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    (frozen : Bool → SamplerTupleIndex G B h → ℝ) (hfrozen : ∀ e k, |frozen e k| ≤ 1)
    (e : OneCubeActiveRow P) (k : SamplerTupleIndex G B h) :
    realPolynomialMass (oneCubeProfileSubstitution h P lower width frozen e k) ≤ 1 := by
  rcases k with g | ⟨d, b, i⟩
  · simpa only [oneCubeProfileSubstitution, realPolynomialMass_C] using hfrozen e.1 (.inl g)
  · by_cases hd : P d
    · simpa only [oneCubeProfileSubstitution, hd, ↓reduceDIte, realPolynomialMass_C]
        using hfrozen e.1 (.inr ⟨d, b, i⟩)
    · simp only [oneCubeProfileSubstitution, hd, ↓reduceDIte]
      apply (realPolynomialMass_add_le _ _).trans
      apply le_trans _ (hwidth ⟨d, hd⟩ (b, i))
      rw [realPolynomialMass_C]
      apply add_le_add le_rfl
      simpa only [realPolynomialMass_X, mul_one] using
        realPolynomialMass_C_mul_le (width ⟨d, hd⟩ (b, i))
          (MvPolynomial.X (⟨(e.1, ⟨d, hd⟩), b, i⟩ : OneCubeActiveEndpoint (B := B) h P))

def oneCubeSlicedParameter (x : OneCubeActiveEndpoint (B := B) h P → ℝ)
    (j : PrincipalAxisParameter (B := B) (h := h) (α := Fin 1) (fun d => ¬P d)) : ℝ :=
  match j.2.2.2 with
  | none => lower j.1 (j.2.1, j.2.2.1) + width j.1 (j.2.1, j.2.2.1) *
      x ⟨(false, j.1), j.2.1, j.2.2.1⟩
  | some _ => width j.1 (j.2.1, j.2.2.1) *
      (x ⟨(true, j.1), j.2.1, j.2.2.1⟩ - x ⟨(false, j.1), j.2.1, j.2.2.1⟩)

def oneCubeVertex (e : Bool) : Finset (Fin 1) := if e then {0} else ∅

theorem oneCubeProfileSubstitution_eval
    {Z : Type*} (extra : G → Option (Fin 1) → Z)
    (z : Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := Fin 1) P → ℝ)
    (x : OneCubeActiveEndpoint (B := B) h P → ℝ)
    (e : OneCubeActiveRow P) (k : SamplerTupleIndex G B h) :
    MvPolynomial.eval x (oneCubeProfileSubstitution h P lower width
      (fun β k => normalizedCubeTuple (partitionedPrincipalInput P extra) z (fun _ => 0)
        (oneCubeVertex β) k) e k) =
      normalizedCubeTuple (partitionedPrincipalInput P extra) z
        (oneCubeSlicedParameter h P lower width x) (oneCubeVertex e.1) k := by
  rcases k with g | ⟨d, b, i⟩
  · simp only [oneCubeProfileSubstitution, MvPolynomial.eval_C, normalizedCubeTuple,
      partitionedPrincipalInput, Sum.elim_inl]
  · by_cases hd : P d
    · simp only [oneCubeProfileSubstitution, hd, ↓reduceDIte, MvPolynomial.eval_C,
        normalizedCubeTuple, partitionedPrincipalInput, Sum.elim_inl]
    · rcases e with ⟨β, e⟩
      cases β <;>
        simp [oneCubeProfileSubstitution, hd, normalizedCubeTuple, partitionedPrincipalInput,
          oneCubeSlicedParameter, oneCubeVertex, booleanFeature, Fintype.sum_option]
      ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_oneCube_reconstruct (f : Finset (Fin 1) → ℝ) (β : Bool) :
    (if β then booleanCoefficient f ∅ + booleanCoefficient f {0}
      else booleanCoefficient f ∅) = f (oneCubeVertex β) := by
  have hpow : ({0} : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  cases β <;> simp [oneCubeVertex, booleanCoefficient, hpow]

variable {D G Z : Type*} [Fintype D] [Fintype G]
variable {B : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (P : D → Prop) [DecidablePred P]
variable (extra : G → Option (Fin 1) → Z)

def oneCubeJointJetEndpoints
    (v : (Σ _d : {d // ¬P d}, Finset (Fin 1)) → ℝ)
    (o : Σ _e : OneCubeActiveRow P, Unit) : ℝ :=
  if o.1.1 then v ⟨o.1.2, ∅⟩ + v ⟨o.1.2, {0}⟩ else v ⟨o.1.2, ∅⟩

omit [Fintype D] [DecidablePred P] in
theorem oneCubeJointJetEndpoints_measurable : Measurable (oneCubeJointJetEndpoints P) := by
  apply Measurable.of_eval
  intro o
  unfold oneCubeJointJetEndpoints
  split <;> fun_prop

noncomputable def oneCubeProfileFrozenEndpoints
    (y : PartitionedProfileNoiseIndex G Z (Fin 1) B h P → ℝ)
    (β : Bool) (k : SamplerTupleIndex G B h) : ℝ :=
  normalizedCubeTuple (partitionedPrincipalInput P extra) (fun j => y (.inl j))
    (fun _ => 0) (oneCubeVertex β) k

noncomputable def oneCubeProfileEndpointNoise
    (y : PartitionedProfileNoiseIndex G Z (Fin 1) B h P → ℝ)
    (e : OneCubeActiveRow P) (j : SamplerCoefficientSlot G B h e.2.val) : ℝ :=
  y (.inr ⟨e.2.val, j⟩)

omit [∀ index, DecidableEq (B index)] in
theorem oneCubeProfileSubstitution_jet_identity
    (ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z (Fin 1) B h P → ℝ)
    (lower width : ∀ d : {d // ¬P d}, B d.val × Fin (h d.val) → ℝ)
    (x : OneCubeActiveEndpoint (B := B) h P → ℝ) :
    jointSlicedProfileValue h (fun e : OneCubeActiveRow P => e.2.val) ρ γ ε
        (oneCubeProfileEndpointNoise h P y)
        (oneCubeProfileSubstitution h P lower width (oneCubeProfileFrozenEndpoints h P extra y)) t x =
      oneCubeJointJetEndpoints P
        (partitionedProfileJet h P extra (fun _ => id) ρ γ ε t y
          (oneCubeSlicedParameter h P lower width x)) := by
  funext o
  change MvPolynomial.eval _ _ =
    (if o.1.1 then booleanCoefficient _ ∅ + booleanCoefficient _ {0} else booleanCoefficient _ ∅)
  rw [booleanCoefficient_oneCube_reconstruct]
  unfold oneCubeProfileEndpointNoise
  congr 1
  apply congrArg MvPolynomial.eval
  funext k
  rw [partitionedProfileInput_source]
  exact oneCubeProfileSubstitution_eval h P lower width extra (fun j => y (.inl j)) x o.1 k

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable (A : Type*) [Fintype A]

def oneCubeJetIndexEquiv : (Σ _ : A, Finset (Fin 1)) ≃ Fin 2 × A where
  toFun j := (if j.2 = ∅ then 0 else 1, j.1)
  invFun j := ⟨j.2, if j.1 = 0 then ∅ else {0}⟩
  left_inv j := by
    rcases j with ⟨a, t⟩
    fin_cases t <;> rfl
  right_inv j := by
    rcases j with ⟨i, a⟩
    fin_cases i <;> rfl

def oneCubeEndpointIndexEquiv : (Σ _ : Bool × A, Unit) ≃ Fin 2 × A where
  toFun j := (finTwoEquiv.symm j.1.1, j.1.2)
  invFun j := ⟨(finTwoEquiv j.1, j.2), ()⟩
  left_inv j := by rcases j with ⟨⟨β,a⟩,u⟩; cases u; simp
  right_inv j := by rcases j with ⟨i,a⟩; simp

def oneCubeArrayPairEquiv : (Fin 2 × A → ℝ) ≃ᵐ ((A → ℝ) × (A → ℝ)) :=
  (MeasurableEquiv.curry (Fin 2) A ℝ).trans MeasurableEquiv.finTwoArrow

theorem oneCubeArrayPairEquiv_volume : MeasurePreserving (oneCubeArrayPairEquiv A) volume volume := by
  have hc := (finiteArray_uncurry_measurePreserving (fun (_ : Fin 2) (_ : A) => (volume : Measure ℝ))).symm
    (MeasurableEquiv.curry (Fin 2) A ℝ).symm
  exact (volume_preserving_finTwoArrow (A → ℝ)).comp hc

def oneCubePairShear : ((A → ℝ) × (A → ℝ)) ≃ᵐ ((A → ℝ) × (A → ℝ)) where
  toFun p := (p.1, p.1 + p.2)
  invFun p := (p.1, p.2 - p.1)
  left_inv p := by ext a <;> simp
  right_inv p := by ext a <;> simp
  measurable_toFun := measurable_fst.prodMk (measurable_fst.add measurable_snd)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub measurable_fst)

def oneCubeJetEndpointEquiv : ((Σ _ : A, Finset (Fin 1)) → ℝ) ≃ᵐ
    ((Σ _ : Bool × A, Unit) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × A => ℝ) (oneCubeJetIndexEquiv A)).trans
    ((oneCubeArrayPairEquiv A).trans ((oneCubePairShear A).trans
      ((oneCubeArrayPairEquiv A).symm.trans
        (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × A => ℝ) (oneCubeEndpointIndexEquiv A)).symm)))

theorem oneCubeJetEndpointEquiv_volume : MeasurePreserving (oneCubeJetEndpointEquiv A) volume volume := by
  have h₁ := volume_measurePreserving_piCongrLeft (fun _ : Fin 2 × A => ℝ) (oneCubeJetIndexEquiv A)
  have h₂ := oneCubeArrayPairEquiv_volume A
  have h₃ : MeasurePreserving (oneCubePairShear A) volume volume := measurePreserving_prod_add volume volume
  have h₄ := h₂.symm (oneCubeArrayPairEquiv A)
  have h₅ := (volume_measurePreserving_piCongrLeft (fun _ : Fin 2 × A => ℝ)
    (oneCubeEndpointIndexEquiv A)).symm
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 × A => ℝ) (oneCubeEndpointIndexEquiv A))
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

omit [Fintype A] in
theorem oneCubeJetEndpointEquiv_apply (z : (Σ _ : A, Finset (Fin 1)) → ℝ)
    (β : Bool) (a : A) :
    oneCubeJetEndpointEquiv A z ⟨(β,a),()⟩ =
      if β then z ⟨a,∅⟩ + z ⟨a,{0}⟩ else z ⟨a,∅⟩ := by
  cases β <;> rfl

theorem oneCubeJointJetEndpoints_equiv {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P] :
    oneCubeJointJetEndpoints P = oneCubeJetEndpointEquiv {d // ¬P d} := by
  funext z o
  rcases o with ⟨⟨β,a⟩,u⟩
  cases u
  exact (oneCubeJetEndpointEquiv_apply _ z β a).symm

theorem oneCubeJointJetEndpoints_volume {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P] :
    MeasurePreserving (oneCubeJointJetEndpoints P) volume volume := by
  rw [oneCubeJointJetEndpoints_equiv]
  exact oneCubeJetEndpointEquiv_volume _

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P]

def oneCubeSiteRestriction (x : Finset (Fin 1) → D → ℝ) :
    (Σ _ : OneCubeActiveRow P, Unit) → ℝ :=
  fun o => x (oneCubeVertex o.1.1) o.1.2.val

theorem oneCubeSiteRestriction_lipschitz : LipschitzWith 1 (oneCubeSiteRestriction P) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro o
  exact (dist_le_pi_dist (x (oneCubeVertex o.1.1)) (y (oneCubeVertex o.1.1)) o.1.2.val).trans
    (dist_le_pi_dist x y (oneCubeVertex o.1.1))

theorem oneCubeSiteRestriction_complex_lipschitz
    (f : ((Σ _ : OneCubeActiveRow P, Unit) → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x => (f (oneCubeSiteRestriction P x) : ℂ)) := by
  have he := Complex.isometry_ofReal.lipschitzWith.comp (hf.comp (oneCubeSiteRestriction_lipschitz P))
  simpa only [one_mul, mul_one, Function.comp_def] using he

omit [Fintype D] [DecidablePred P] in
theorem oneCubeJointJetEndpoints_booleanSiteJets (x : Finset (Fin 1) → D → ℝ) :
    oneCubeJointJetEndpoints P (booleanSiteJets (fun _ : {d // ¬P d} => id)
      (fun t d => x t d.val)) = oneCubeSiteRestriction P x := by
  funext o
  rcases o with ⟨⟨β, d⟩, u⟩
  have hps : ({0} : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  cases β <;> simp [oneCubeJointJetEndpoints, booleanSiteJets, booleanCoefficient,
    oneCubeSiteRestriction, oneCubeVertex, hps]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable (A : Type*) [Fintype A]

theorem oneCubeJetEndpointEquiv_lipschitz : LipschitzWith 2 (oneCubeJetEndpointEquiv A) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (by norm_num) dist_nonneg)).mpr
  intro o
  rcases o with ⟨⟨β,a⟩,u⟩
  cases u
  simp only [oneCubeJetEndpointEquiv_apply, NNReal.coe_ofNat]
  cases β with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have he := dist_le_pi_dist x y (⟨a,∅⟩ : Σ _ : A, Finset (Fin 1))
    linarith [dist_nonneg (x := x) (y := y)]
  | true =>
    simp only [↓reduceIte]
    exact (dist_add_add_le _ _ _ _).trans (by
      have he₀ := dist_le_pi_dist x y (⟨a,∅⟩ : Σ _ : A, Finset (Fin 1))
      have he₁ := dist_le_pi_dist x y (⟨a,{0}⟩ : Σ _ : A, Finset (Fin 1))
      linarith)

theorem oneCubeJet_norm_le (z : (Σ _ : A, Finset (Fin 1)) → ℝ) :
    ‖z‖ ≤ 2 * ‖oneCubeJetEndpointEquiv A z‖ := by
  have h₀ (a : A) : |z ⟨a,∅⟩| ≤ ‖oneCubeJetEndpointEquiv A z‖ := by
    simpa only [oneCubeJetEndpointEquiv_apply, Bool.false_eq_true, ↓reduceIte, Real.norm_eq_abs]
      using norm_le_pi_norm (oneCubeJetEndpointEquiv A z) ⟨(false,a),()⟩
  have h₁ (a : A) : |z ⟨a,∅⟩ + z ⟨a,{0}⟩| ≤ ‖oneCubeJetEndpointEquiv A z‖ := by
    simpa only [oneCubeJetEndpointEquiv_apply, ↓reduceIte, Real.norm_eq_abs]
      using norm_le_pi_norm (oneCubeJetEndpointEquiv A z) ⟨(true,a),()⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  rintro ⟨a,t⟩
  fin_cases t
  · change |z ⟨a,∅⟩| ≤ _
    linarith [h₀ a, norm_nonneg (oneCubeJetEndpointEquiv A z)]
  · change |z ⟨a,{0}⟩| ≤ _
    have he : |z ⟨a,{0}⟩| ≤ |z ⟨a,∅⟩ + z ⟨a,{0}⟩| + |z ⟨a,∅⟩| := by
      have h := abs_sub_le (z ⟨a,∅⟩ + z ⟨a,{0}⟩) 0 (z ⟨a,∅⟩)
      simpa only [add_sub_cancel_left, sub_zero, zero_sub, abs_neg] using h
    linarith [h₀ a, h₁ a]

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

variable {D : Type*} [Fintype D] (P : D → Prop) [DecidablePred P] (R : D → ℝ)

noncomputable def oneCubeNormalizedSites
    (z : (Σ _d : {d // ¬P d}, Finset (Fin 1)) → ℝ) (t : Finset (Fin 1)) (d : D) : ℝ :=
  if hd : ¬P d then
    (if (0 : Fin 1) ∈ t then z ⟨⟨d,hd⟩, ∅⟩ + z ⟨⟨d,hd⟩, {0}⟩ else z ⟨⟨d,hd⟩, ∅⟩) / R d
  else 0

omit [Fintype D] in
theorem oneCubeNormalizedSites_restriction
    (z : (Σ _d : {d // ¬P d}, Finset (Fin 1)) → ℝ) :
    oneCubeSiteRestriction P (oneCubeNormalizedSites P R z) =
      fun o => oneCubeJointJetEndpoints P z o / R o.1.2.val := by
  funext o
  rcases o with ⟨⟨β,d⟩,u⟩
  cases β <;> simp [oneCubeSiteRestriction, oneCubeNormalizedSites, oneCubeVertex,
    oneCubeJointJetEndpoints, d.property]

theorem oneCubeNormalizedSites_bound
    (z : (Σ _d : {d // ¬P d}, Finset (Fin 1)) → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hz : ‖fun o : (Σ _e : OneCubeActiveRow P, Unit) =>
      oneCubeJointJetEndpoints P z o / R o.1.2.val‖ ≤ r) :
    ∀ t d, |oneCubeNormalizedSites P R z t d| ≤ r := by
  intro t d
  by_cases hd : ¬P d
  · by_cases ht : (0 : Fin 1) ∈ t
    · have he := (norm_le_pi_norm (fun o : (Σ _e : OneCubeActiveRow P, Unit) =>
        oneCubeJointJetEndpoints P z o / R o.1.2.val) ⟨(true, ⟨d,hd⟩), ()⟩).trans hz
      change |(z ⟨⟨d,hd⟩, ∅⟩ + z ⟨⟨d,hd⟩, {0}⟩) / R d| ≤ r at he
      rw [oneCubeNormalizedSites, dite_eq_left hd, ite_eq_left ht]
      exact he
    · have he := (norm_le_pi_norm (fun o : (Σ _e : OneCubeActiveRow P, Unit) =>
        oneCubeJointJetEndpoints P z o / R o.1.2.val) ⟨(false, ⟨d,hd⟩), ()⟩).trans hz
      change |z ⟨⟨d,hd⟩, ∅⟩ / R d| ≤ r at he
      rw [oneCubeNormalizedSites, dite_eq_left hd, ite_eq_right ht]
      exact he
  · simpa only [oneCubeNormalizedSites, hd, dite_false, abs_zero] using hr

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

def oneCubeBoundedJetEquiv (h : ℕ) (hh : 1 ≤ h) : Finset (Fin 1) ≃ BoundedBooleanJet (Fin 1) h where
  toFun t := ⟨t, (Finset.card_le_univ t).trans (by simpa using hh)⟩
  invFun t := t.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem boundedBooleanJetRows_oneCube (h : ℕ) (hh : 1 ≤ h) :
    boundedBooleanJetRows (Fin 1) h = Finset.univ := by
  ext t
  simp only [mem_boundedBooleanJetRows, Finset.mem_univ, iff_true]
  exact (oneCubeBoundedJetEquiv h hh t).property

theorem realBoundedSiteReconstruction_oneCube (h : ℕ) (hh : 1 ≤ h)
    (v : BoundedBooleanJet (Fin 1) h → ℝ) (t : Finset (Fin 1)) :
    realBoundedSiteReconstruction h v t =
      v (oneCubeBoundedJetEquiv h hh ∅) +
        if (0 : Fin 1) ∈ t then v (oneCubeBoundedJetEquiv h hh {0}) else 0 := by
  unfold realBoundedSiteReconstruction
  rw [← Fintype.sum_equiv (oneCubeBoundedJetEquiv h hh)
    (fun s => v (oneCubeBoundedJetEquiv h hh s) * (if s ⊆ t then 1 else 0))
    (fun s => v s * (if s.val ⊆ t then 1 else 0)) (fun _ => rfl)]
  have huniv : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [huniv]
  by_cases ht : (0 : Fin 1) ∈ t <;> simp [ht]

theorem oneCubeNormalizedSites_bounded_coordinates {D : Type*} [Fintype D]
    (P : D → Prop) [DecidablePred P] (R : D → ℝ) (h : D → ℕ) (hh : ∀ d, 1 ≤ h d)
    (v : (Σ d : {d // ¬P d}, BoundedBooleanJet (Fin 1) (h d.val)) → ℝ) :
    oneCubeNormalizedSites P R (fun q => v ⟨q.1, oneCubeBoundedJetEquiv (h q.1.val) (hh q.1.val) q.2⟩) =
      realSitesFromBoundedJets h (fun q => if hd : ¬P q.1 then v ⟨⟨q.1,hd⟩, q.2⟩ / R q.1 else 0) := by
  funext t d
  change oneCubeNormalizedSites P R _ t d = realBoundedSiteReconstruction (h d) _ t
  rw [realBoundedSiteReconstruction_oneCube (h d) (hh d)]
  by_cases hd : ¬P d
  · rw [oneCubeNormalizedSites, dite_eq_left hd]
    by_cases ht : (0 : Fin 1) ∈ t
    · simp only [dite_eq_left hd, ite_eq_left ht, add_div]
    · simp only [dite_eq_left hd, ite_eq_right ht, add_zero]
  · simp only [oneCubeNormalizedSites, dite_eq_right hd, ite_self, zero_add]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

 theorem oneCube_endpoint_scale_product {D : Type*} [Fintype D] (R : D → ℝ) :
    (∏ o : (Σ _e : Bool × D, Unit), R o.1.2) = ∏ d, (R d)^2 := by
  simp only [Fintype.prod_sigma, Fintype.prod_prod_type,
    Finset.prod_const, Finset.card_univ, Fintype.card_bool, Fintype.card_unit, pow_one, ← Finset.prod_pow]

 theorem oneCube_bounded_scale_product {D : Type*} [Fintype D] (R : D → ℝ)
    (h : D → ℕ) (hh : ∀ d, 1 ≤ h d) :
    (∏ o : (Σ d, BoundedBooleanJet (Fin 1) (h d)), R o.1) = ∏ d, (R d)^2 := by
  have hc (d) : Fintype.card (BoundedBooleanJet (Fin 1) (h d)) = 2 := by
    rw [← Fintype.card_congr (oneCubeBoundedJetEquiv (h d) (hh d))]
    simp
  simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, hc]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "extra" => (fun g a => (g, a) : G → Option (Fin 1) → G × Option (Fin 1))

noncomputable def allocatedSlicedOneCubeEndpointMap
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) (y : Endpoint → ℝ) : (Σ _e : OneCubeActiveRow grid, Unit) → ℝ :=
  oneCubeJointJetEndpoints grid
    (allocatedNormalizedLongJetMap B U basis S x u (fun _ => id)
      (oneCubeSlicedParameter degree grid lower width y) r)

noncomputable def allocatedSlicedEndpointNoise (t : ℝ) (r : Coeff → ℝ) :
    PartitionedProfileNoiseIndex G (G × Option (Fin 1)) (Fin 1) B degree grid → ℝ :=
  profileNoiseWithActive degree grid (allocatedProfileFrozenNoise B U basis S x u)
    (activeTailRescale degree grid (fun a => σ a.1 / t) r)

omit [∀ index, DecidableEq (B index)] in
theorem allocatedSlicedOneCubeEndpointMap_eq
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (r : Coeff → ℝ) {t : ℝ} (ht : t ≠ 0) :
    allocatedSlicedOneCubeEndpointMap B U basis S x u lower width r =
      jointSlicedProfileValue degree (fun e : OneCubeActiveRow grid => e.2.val)
        (fun a => R a.1 / 4)
        (fun a => principalProfileSize (R a.1) (Fintype.card (B a)))
        (fun a => tailProfileSize (R a.1) 1 (Fintype.card (SamplerCoefficientSlot G B degree a)))
        (oneCubeProfileEndpointNoise degree grid (allocatedSlicedEndpointNoise B U basis S x u t r))
        (oneCubeProfileSubstitution degree grid lower width
          (oneCubeProfileFrozenEndpoints degree grid extra (allocatedSlicedEndpointNoise B U basis S x u t r))) t := by
  funext y
  rw [oneCubeProfileSubstitution_jet_identity]
  unfold allocatedSlicedOneCubeEndpointMap
  apply congrArg (oneCubeJointJetEndpoints grid)
  exact (allocatedTailProfileJet_eq B U basis S x u (fun _ => id) ht r
    (oneCubeSlicedParameter degree grid lower width y)).symm

end Erdos3.VectorPolynomial

end

end OAI
