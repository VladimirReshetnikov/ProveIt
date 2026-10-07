/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Polynomial.SmallAffinePolynomial

namespace OAI

section

namespace Erdos3

theorem coefficientProfileCenter_mul {J : Type*} (P : Finset J) (R γ : ℝ) (j : J) :
    coefficientProfileCenter P (R * γ) j = R * coefficientProfileCenter P γ j := by
  classical
  unfold coefficientProfileCenter
  split_ifs <;> ring

theorem coefficientProfileWidth_mul {J : Type*} (P : Finset J) (j₀ : J)
    (R ρ γ ε : ℝ) (j : J) :
    coefficientProfileWidth P j₀ (R * ρ) (R * γ) (R * ε) j =
      R * coefficientProfileWidth P j₀ ρ γ ε j := by
  classical
  unfold coefficientProfileWidth
  split_ifs <;> ring

theorem principalProfileSize_mul (R S : ℝ) (b : ℕ) :
    principalProfileSize (R * S) b = R * principalProfileSize S b := by
  unfold principalProfileSize
  ring

theorem tailProfileSize_mul (R S σ : ℝ) (b : ℕ) :
    tailProfileSize (R * S) σ b = R * tailProfileSize S σ b := by
  unfold tailProfileSize
  ring

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {D G : Type*} [Fintype D] [Fintype G] {B : D → Type*}
variable [∀ d, Fintype (B d)] (h : D → ℕ) (d : D)

theorem bounded_mem_nonprincipalCoefficientSlots
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    e ∈ nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d) ↔
      e ≠ constantCoefficientSlot _ _ ∧ e ∉ principalCoefficientSlots h d := by
  classical
  rw [mem_nonprincipalCoefficientSlots, mem_fixedNonprincipalExponents]
  have hz : e.val = 0 ↔ e = constantCoefficientSlot _ _ := by
    constructor
    · intro he
      exact Subtype.ext he
    · intro he
      exact congrArg Subtype.val he
  have hp : (∃ b, canonicalPrincipalExponent h d b = e.val) ↔
      e ∈ principalCoefficientSlots h d := by
    rw [mem_principalCoefficientSlots]
    constructor <;> rintro ⟨b, hb⟩
    · exact ⟨b, Subtype.ext hb⟩
    · exact ⟨b, congrArg Subtype.val hb⟩
  have hm : e.val ∈ monomialExponentSet
      (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _) :=
    (mem_monomialExponentSet _ _).mpr ⟨e, rfl⟩
  simp only [hm, true_and, ← not_exists, hp]
  exact and_congr (not_congr hz) Iff.rfl

theorem boundedProfileCenter_dilation (γ t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileCenter (principalCoefficientSlots h d) γ e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileCenter (principalCoefficientSlots h d) γ e := by
  classical
  by_cases hp : e ∈ principalCoefficientSlots h d
  · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
    rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
      t e b (congrArg Subtype.val hb.symm), one_mul]
  · simp only [coefficientProfileCenter, hp, ite_false, mul_zero]

theorem boundedProfileWidth_dilation (ρ γ ε t : ℝ)
    (e : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)) :
    coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
        ρ γ (t * ε) e =
      nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e *
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ ε e := by
  classical
  by_cases hz : e = constantCoefficientSlot _ _
  · rw [nonprincipalDilation_zero Subtype.val (canonicalPrincipalExponent h d)
      t e (congrArg Subtype.val hz)]
    simp only [coefficientProfileWidth, hz, ite_true, one_mul]
  · by_cases hp : e ∈ principalCoefficientSlots h d
    · obtain ⟨b, hb⟩ := (mem_principalCoefficientSlots h d e).mp hp
      rw [nonprincipalDilation_principal Subtype.val (canonicalPrincipalExponent h d)
        t e b (congrArg Subtype.val hb.symm), one_mul]
      simp only [coefficientProfileWidth, hz, hp, ite_false, ite_true]
    · rw [nonprincipalDilation_mem Subtype.val (canonicalPrincipalExponent h d) t e
        ((bounded_mem_nonprincipalCoefficientSlots h d e).mpr ⟨hz, hp⟩)]
      simp only [coefficientProfileWidth, hz, hp, ite_false]

theorem boundedProfile_polynomial_split (hd : 0 < h d) (ρ γ ε t : ℝ)
    (r : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → ℝ) :
    monomialArrayPolynomial Subtype.val (fun e =>
      coefficientProfileCenter (principalCoefficientSlots h d) γ e +
        coefficientProfileWidth (principalCoefficientSlots h d) (constantCoefficientSlot _ _)
          ρ γ (t * ε) e * r e) =
      MvPolynomial.C (ρ * r (constantCoefficientSlot _ _)) +
      (∑ b, MvPolynomial.monomial (canonicalPrincipalExponent h d b)
        (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot h d b))) +
      ∑ e ∈ nonprincipalCoefficientSlots
          (Subtype.val : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → _)
          (canonicalPrincipalExponent h d),
        MvPolynomial.monomial e.val (t * (ε * r e)) := by
  classical
  let c := coefficientProfileCenter (principalCoefficientSlots (G := G) (B := B) h d) γ
  let w := coefficientProfileWidth (principalCoefficientSlots (G := G) (B := B) h d)
    (constantCoefficientSlot _ _) ρ γ ε
  have heq : (fun e => c e + coefficientProfileWidth (principalCoefficientSlots h d)
      (constantCoefficientSlot _ _) ρ γ (t * ε) e * r e) =
      (fun e => nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * c e +
        (nonprincipalDilation Subtype.val (canonicalPrincipalExponent h d) t e * w e) * r e) := by
    funext e
    rw [boundedProfileWidth_dilation]
    congr 1
    exact boundedProfileCenter_dilation h d γ t e
  rw [heq, monomialArrayPolynomial_affine_dilated_split Subtype.val Subtype.val_injective
    (canonicalPrincipalExponent h d) (canonicalPrincipalExponent_injective h d hd)
    (canonicalPrincipalExponent_ne_zero h d hd) (principalCoefficientSlot h d) (fun _ => rfl)]
  have hc : (monomialArrayPolynomial Subtype.val (fun e => c e + w e * r e)).coeff 0 =
      ρ * r (constantCoefficientSlot _ _) := by
    rw [show (0 : SamplerTupleIndex G B h →₀ ℕ) =
      (constantCoefficientSlot (SamplerTupleIndex G B h) (h d)).val from rfl,
      monomialArrayPolynomial_coeff Subtype.val Subtype.val_injective]
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth,
      constantCoefficientSlot_not_principal h d hd, ite_false, ite_true, zero_add]
  rw [hc]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro b _
    have hp : principalCoefficientSlot h d b ∈ principalCoefficientSlots (G := G) h d :=
      (mem_principalCoefficientSlots h d _).mpr ⟨b, rfl⟩
    have hz : principalCoefficientSlot (G := G) h d b ≠ constantCoefficientSlot _ _ := by
      intro hz
      exact constantCoefficientSlot_not_principal h d hd (hz ▸ hp)
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hp, hz, ite_true, ite_false]
  · apply Finset.sum_congr rfl
    intro e he
    obtain ⟨hz, hp⟩ := (bounded_mem_nonprincipalCoefficientSlots h d e).mp he
    simp only [c, w, coefficientProfileCenter, coefficientProfileWidth, hz, hp, ite_false, zero_add]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

abbrev SamplerCoefficientSlot {D : Type*} (G : Type*) (B : D → Type*)
    (h : D → ℕ) (d : D) := BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)

abbrev PartitionedProfileNoiseIndex {D : Type*} (G Z α : Type*) (B : D → Type*)
    (h : D → ℕ) (P : D → Prop) :=
  (Z ⊕ PrincipalAxisParameter (B := B) (h := h) (α := α) P) ⊕
    (Σ d, SamplerCoefficientSlot G B h d)

def partitionedProfileInput {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    (k : SamplerTupleIndex G B h) (a : Option α) :
    PartitionedProfileNoiseIndex G Z α B h P ⊕
      PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) :=
  Sum.map Sum.inl id (partitionedPrincipalInput P extra k a)

theorem partitionedProfileInput_principal {D G Z α : Type*} {B : D → Type*} {h : D → ℕ}
    (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
    (d : {d // ¬P d}) (b : B d.val) (v : Fin (h d.val)) (a : Option α) :
    partitionedProfileInput (B := B) (h := h) P extra (.inr ⟨d.val, b, v⟩) a =
      .inr ⟨d, b, v, a⟩ := by
  simp [partitionedProfileInput, partitionedPrincipalInput, d.property]

theorem partitionedProfileInput_source {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} {h : D → ℕ} (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z) (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (s : Finset α) (k : SamplerTupleIndex G B h) :
    normalizedCubeTuple (partitionedProfileInput P extra) y x s k =
      normalizedCubeTuple (partitionedPrincipalInput P extra) (fun j => y (.inl j)) x s k := by
  unfold normalizedCubeTuple
  apply Finset.sum_congr rfl
  intro a _
  unfold partitionedProfileInput
  cases partitionedPrincipalInput P extra k a <;> rfl

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def partitionedProfilePrincipal (γ : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (d : {d // ¬P d}) (b : B d.val) : ℝ :=
  3 * γ d.val / 2 + γ d.val / 2 * y (.inr ⟨d.val, principalCoefficientSlot h d.val b⟩)

noncomputable def partitionedProfileConstant (ρ : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (d : {d // ¬P d}) : ℝ :=
  ρ d.val * y (.inr ⟨d.val, constantCoefficientSlot _ _⟩)

noncomputable def partitionedProfileTerms (d : {d // ¬P d}) :
    Finset (SamplerCoefficientSlot G B h d.val) :=
  nonprincipalCoefficientSlots Subtype.val (canonicalPrincipalExponent h d.val)

noncomputable def partitionedProfileJet (ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (o : Σ d, O d) : ℝ :=
  booleanCoefficient (fun s => MvPolynomial.eval
    (normalizedCubeTuple (partitionedProfileInput P extra) y x s)
    (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h o.1.val =>
      coefficientProfileCenter (principalCoefficientSlots h o.1.val) (γ o.1.val) e +
        coefficientProfileWidth (principalCoefficientSlots h o.1.val) (constantCoefficientSlot _ _)
          (ρ o.1.val) (γ o.1.val) (t * ε o.1.val) e * y (.inr ⟨o.1.val, e⟩)))) (sets o.1 o.2)

theorem partitionedProfileJet_eq (hh : ∀ d, 0 < h d) (ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedProfileJet h P extra sets ρ γ ε t y x =
      booleanConstantJet sets (partitionedProfileConstant h P ρ y) +
      coefficientArraySampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P γ y) sets (partitionedProfileTerms (G := G) h P)
        (fun d _ => ε d.val) (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩)
        (partitionedProfileInput P extra) t y x := by
  classical
  funext o
  let V := normalizedCubeTuple (partitionedProfileInput P extra) y x
  have hv (s : Finset α) : MvPolynomial.eval (V s)
      (monomialArrayPolynomial Subtype.val (fun e : SamplerCoefficientSlot G B h o.1.val =>
        coefficientProfileCenter (principalCoefficientSlots h o.1.val) (γ o.1.val) e +
          coefficientProfileWidth (principalCoefficientSlots h o.1.val) (constantCoefficientSlot _ _)
            (ρ o.1.val) (γ o.1.val) (t * ε o.1.val) e * y (.inr ⟨o.1.val, e⟩))) =
      partitionedProfileConstant h P ρ y o.1 +
      (∑ b, partitionedProfilePrincipal h P γ y o.1 b *
        ∏ v, V s (.inr ⟨o.1.val, b, v⟩)) +
      t * ∑ e ∈ partitionedProfileTerms (G := G) h P o.1,
        (ε o.1.val * y (.inr ⟨o.1.val, e⟩)) * ∏ k ∈ e.val.support, V s k ^ e.val k := by
    rw [boundedProfile_polynomial_split h o.1.val (hh o.1.val)]
    simp only [map_add, map_sum, MvPolynomial.eval_C]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro b _
      simp only [canonicalPrincipalExponent, productBlockExponent_monomial,
        map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X,
        partitionedProfilePrincipal]
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      simp only [MvPolynomial.eval_monomial, Finsupp.prod]
      ring
  have he : partitionedProfileJet h P extra sets ρ γ ε t y x o = _ :=
    congrArg (fun f : Finset α → ℝ => booleanCoefficient f (sets o.1 o.2)) (funext hv)
  rw [he]
  rw [booleanCoefficient_add, booleanCoefficient_add, booleanCoefficient_const,
    booleanCoefficient_const_mul]
  have hp : booleanCoefficient (fun s => ∑ b, partitionedProfilePrincipal h P γ y o.1 b *
      ∏ v, V s (.inr ⟨o.1.val, b, v⟩)) (sets o.1 o.2) =
      jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
        (partitionedProfilePrincipal h P γ y) sets x o := by
    rw [jointBooleanSampler_formula]
    simp only [V, normalizedCubeTuple, partitionedProfileInput_principal, Sum.elim_inr]
  rw [hp]
  change _ + _ + t * normalizedCoefficientTailValue _ _ _ _ _ y x _ = _
  simp only [Pi.add_apply, booleanConstantJet, coefficientArraySampler, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype α] [DecidableEq α]
variable {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
variable (P : D → Prop) [DecidablePred P] (extra : G → Option α → Z)
variable {O : {d // ¬P d} → Type*} (sets : ∀ d, O d → Finset α)

noncomputable def unitProfilePrincipalSize (d : D) : ℝ :=
  principalProfileSize 1 (Fintype.card (B d))

noncomputable def unitProfileTailSize (d : D) : ℝ :=
  tailProfileSize 1 1 (Fintype.card (SamplerCoefficientSlot G B h d))

noncomputable def partitionedAllocatedProfileJet (R : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (Σ d, O d) → ℝ :=
  partitionedProfileJet h P extra sets (fun d => R d / 4)
    (fun d => principalProfileSize (R d) (Fintype.card (B d)))
    (fun d => tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d))) t y x

theorem partitionedProfileJet_mul (R ρ γ ε : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedProfileJet h P extra sets (fun d => R d * ρ d) (fun d => R d * γ d)
        (fun d => R d * ε d) t y x =
      fun o => R o.1.val * partitionedProfileJet h P extra sets ρ γ ε t y x o := by
  classical
  funext o
  unfold partitionedProfileJet
  have hscale : t * (R o.1.val * ε o.1.val) = R o.1.val * (t * ε o.1.val) := by ring
  simp_rw [hscale, coefficientProfileCenter_mul, coefficientProfileWidth_mul,
    monomialArrayPolynomial_eval]
  rw [← booleanCoefficient_const_mul]
  congr 1
  funext s
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem partitionedAllocatedProfileJet_scale (R : D → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedAllocatedProfileJet h P extra sets R t y x =
      fun o => R o.1.val * partitionedAllocatedProfileJet h P extra sets (fun _ => 1) t y x o := by
  have hp (d : D) : principalProfileSize (R d) (Fintype.card (B d)) =
      R d * principalProfileSize 1 (Fintype.card (B d)) := by
    simpa only [mul_one] using principalProfileSize_mul (R d) 1 (Fintype.card (B d))
  have ht (d : D) : tailProfileSize (R d) 1 (Fintype.card (SamplerCoefficientSlot G B h d)) =
      R d * tailProfileSize 1 1 (Fintype.card (SamplerCoefficientSlot G B h d)) := by
    simpa only [mul_one] using tailProfileSize_mul (R d) 1 1 (Fintype.card (SamplerCoefficientSlot G B h d))
  unfold partitionedAllocatedProfileJet
  simp_rw [hp, ht, div_eq_mul_inv, one_mul]
  exact partitionedProfileJet_mul h P extra sets R (fun _ => 4⁻¹) _ _ t y x

omit [Fintype D] in
theorem unitProfilePrincipalSize_pos (d : D) : 0 < unitProfilePrincipalSize (B := B) d :=
  principalProfileSize_pos zero_lt_one _

theorem unitProfileTailSize_pos (d : D) : 0 < unitProfileTailSize (G := G) (B := B) h d :=
  tailProfileSize_pos zero_lt_one zero_lt_one _

omit [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [DecidablePred P] in
theorem partitionedProfilePrincipal_unit_bounds
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) (b : B d.val) :
    unitProfilePrincipalSize (B := B) d.val ≤
        |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| ∧
      |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| ≤
        2 * unitProfilePrincipalSize (B := B) d.val := by
  have hγ := unitProfilePrincipalSize_pos (B := B) d.val
  obtain ⟨hl, hu⟩ := abs_le.mp (hy (.inr ⟨d.val, principalCoefficientSlot h d.val b⟩))
  have hlo : unitProfilePrincipalSize (B := B) d.val ≤
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b := by
    unfold partitionedProfilePrincipal
    nlinarith
  rw [abs_of_nonneg (hγ.le.trans hlo)]
  refine ⟨hlo, ?_⟩
  unfold partitionedProfilePrincipal
  nlinarith

omit [Fintype D] [Fintype G] [Fintype α] [DecidableEq α] [DecidablePred P] in
theorem partitionedProfilePrincipal_unit_sum
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) :
    (∑ b, |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b|) ≤ 1 := by
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl (Fintype.card (B d.val)) 0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  calc
    _ ≤ ∑ _b : B d.val, 2 * unitProfilePrincipalSize (B := B) d.val :=
      Finset.sum_le_sum (fun b _ => (partitionedProfilePrincipal_unit_bounds h P y hy d b).2)
    _ = 2 * principalProfileSize 1 (Fintype.card (B d.val)) * Fintype.card (B d.val) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, unitProfilePrincipalSize]
      ring
    _ ≤ 1 := by linarith

omit [DecidablePred P] in
theorem partitionedProfileTail_unit_sum (d : {d // ¬P d}) :
    (∑ _e ∈ partitionedProfileTerms (G := G) (B := B) h P d,
      |unitProfileTailSize (G := G) (B := B) h d.val|) ≤ 1 := by
  have he := unitProfileTailSize_pos (G := G) (B := B) h d.val
  have hb := allocatedProfile_budget (R := 1) (σ := 1) zero_le_one le_rfl 0
    (Fintype.card (SamplerCoefficientSlot G B h d.val))
  simp only [Nat.cast_zero, mul_zero, add_zero] at hb
  rw [abs_of_pos he, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (Fintype.card (SamplerCoefficientSlot G B h d.val) : ℝ) *
        unitProfileTailSize (G := G) (B := B) h d.val :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ _) he.le
    _ ≤ 1 := by unfold unitProfileTailSize; nlinarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {D : Type*} [Fintype D] (B : D → Type*) [∀ d, Fintype (B d)]

noncomputable def unitProfilePrincipalLowerBound : ℝ :=
  1 / (8 * (((∑ d, Fintype.card (B d) : ℕ) : ℝ) + 1))

theorem unitProfilePrincipalLowerBound_pos : 0 < unitProfilePrincipalLowerBound B := by
  unfold unitProfilePrincipalLowerBound
  positivity

theorem unitProfilePrincipalLowerBound_le (d : D) :
    unitProfilePrincipalLowerBound B ≤ unitProfilePrincipalSize (B := B) d := by
  classical
  have hcard : Fintype.card (B d) ≤ ∑ a, Fintype.card (B a) :=
    Finset.single_le_sum (f := fun a : D => Fintype.card (B a))
      (fun a _ => Nat.zero_le _) (Finset.mem_univ d)
  unfold unitProfilePrincipalLowerBound unitProfilePrincipalSize principalProfileSize
  apply one_div_le_one_div_of_le (by positivity)
  have hcardR : (Fintype.card (B d) : ℝ) ≤ ((∑ a, Fintype.card (B a) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  linarith

theorem partitionedProfilePrincipal_uniform_lower_bound
    {G Z α : Type*} [Fintype G] [Fintype α] [DecidableEq α]
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (d : {d // ¬P d}) (b : B d.val) :
    unitProfilePrincipalLowerBound B ≤
      |partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y d b| :=
  (unitProfilePrincipalLowerBound_le B d.val).trans
    (partitionedProfilePrincipal_unit_bounds h P y hy d b).1

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem partitioned_profile_comparison
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) {ε : ℝ} (hε : 0 < ε) :
    let t := booleanPerturbationScale (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
      (PartitionedProfileNoiseIndex G Z α B h P) (fun d : {d // ¬P d} => h d.val)
      (fun d => unitProfilePrincipalSize (B := B) d.val)
      (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T degree 1 1 ε
    0 < t ∧ t ≤ 1 ∧
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : Ω × ((Σ d, O d) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R 0 (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))) -
        ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R t (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a => c a d b) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  obtain ⟨t, ht, ht1, hteq, hcomp⟩ := exists_random_coefficient_array_tolerance_with_scale
    (Y := Ω × ((Σ d, O d) → ℝ)) c hc z hz sets hsets (fun d : {d // ¬P d} => h d.val)
    (fun d => hh d.val) hcard block hblock
    (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    (fun d => unitProfilePrincipalSize_pos (B := B) d.val)
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d.val).le)
    ψ hψ hrange hzero hone A T hLip hTransition
    (partitionedProfileTerms (G := G) (B := B) h P)
    (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
    (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra)
    (fun d => hdegree d.val) (fun d e _ => e.property.trans (hdegree d.val))
    (Csum := 1) (Wsum := 1) zero_le_one zero_le_one (partitionedProfileTail_unit_sum h P) hε
  dsimp only
  rw [← hteq]
  refine ⟨ht, ht1, ?_⟩
  intro μ hμ hbox R f hf hfb
  have hclow : ∀ᵐ a ∂μ, ∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)| := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).1
  have hcup : ∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).2
  have hcsum : ∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ 1 := by
    filter_upwards [hbox] with a ha
    exact partitionedProfilePrincipal_unit_sum h P (z a) ha
  let F : Ω × ((Σ d, O d) → ℝ) → Ω × ((Σ d, O d) → ℝ) := fun p =>
    (p.1, fun o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z p.1)) o + p.2 o))
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    have hzj := (hz (.inr ⟨o.1.val, constantCoefficientSlot _ _⟩)).comp
      (measurable_fst : Measurable (Prod.fst : Ω × ((Σ d, O d) → ℝ) → Ω))
    dsimp [F, booleanConstantJet, partitionedProfileConstant]
    split_ifs <;> fun_prop
  have hFactual (s : ℝ) (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, coefficientArraySampler (fun d : {d // ¬P d} => h d.val) (c a) sets
        (partitionedProfileTerms (G := G) (B := B) h P)
        (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
        (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra) s (z a) x) =
      (a, partitionedAllocatedProfileJet h P extra sets R s (z a) x) := by
    apply Prod.ext
    · rfl
    dsimp only [F]
    rw [partitionedAllocatedProfileJet_scale]
    unfold partitionedAllocatedProfileJet
    rw [partitionedProfileJet_eq h P extra sets hh]
    rfl
  have hFzero (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c a) sets x) =
        (a, partitionedAllocatedProfileJet h P extra sets R 0 (z a) x) := by
    simpa only [coefficientArraySampler_zero] using hFactual 0 a x
  simpa only [hFzero, hFactual] using hcomp μ hμ hbox hclow hcup hcsum F hF f hf hfb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {D G Z α : Type*} [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
  (P : D → Prop) [DecidablePred P]
  {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
  (sets : ∀ d, O d → Finset α)

noncomputable def partitionedIdealMap
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    (Σ d, O d) → ℝ :=
  booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) +
    jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x

omit [Fintype D] [Fintype G] [Fintype Z] [DecidablePred P] [∀ d, Fintype (O d)] in
theorem partitionedIdealMap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) :
    Measurable (fun p : Ω ×
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) =>
      partitionedIdealMap h P sets (z p.1) p.2) := by
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a =>
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a) d b) := by
    dsimp [partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  have hb : Measurable (fun a => booleanConstantJet sets
      (partitionedProfileConstant h P (fun _ => 1 / 4) (z a))) := by
    apply booleanConstantJet_measurable_comp sets
      (fun a => partitionedProfileConstant h P (fun _ => 1 / 4) (z a))
    intro d
    dsimp [partitionedProfileConstant]
    exact measurable_const.mul (hz _)
  unfold partitionedIdealMap
  exact (hb.comp measurable_fst).add
    (jointBooleanSampler_measurable_frozen (fun d : {d // ¬P d} => h d.val) sets
      (fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)) hc)

omit [Fintype Z] [∀ d, Fintype (O d)] in
theorem partitionedAllocatedProfileJet_zero (hh : ∀ d, 0 < h d)
    (extra : G → Option α → Z) (R : D → ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
    partitionedAllocatedProfileJet h P extra sets R 0 y x =
      fun o => R o.1.val * partitionedIdealMap h P sets y x o := by
  rw [partitionedAllocatedProfileJet_scale]
  unfold partitionedAllocatedProfileJet
  rw [partitionedProfileJet_eq h P extra sets hh, coefficientArraySampler_zero]
  rfl

noncomputable def partitionedRegularizedIdeal (δ : ℝ≥0)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  regularizedImageDensity (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (partitionedIdealMap h P sets y) δ

omit [Fintype G] [Fintype Z] in
theorem partitionedRegularizedIdeal_measurable {Ω : Type*} [MeasurableSpace Ω]
    (δ : ℝ≥0) (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) :
    Measurable (fun p : Ω × ((Σ d, O d) → ℝ) =>
      partitionedRegularizedIdeal h P sets δ (z p.1) p.2) :=
  conditionalRegularizedDensity_measurable _ _ (partitionedIdealMap_measurable h P sets z hz) δ

omit [Fintype G] [Fintype Z] in
theorem partitionedRegularizedIdeal_probability (δ : ℝ≥0) (hδ : 0 < δ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    (∀ x, 0 ≤ partitionedRegularizedIdeal h P sets δ y x) ∧
      Integrable (partitionedRegularizedIdeal h P sets δ y) ∧
      (∫ x, partitionedRegularizedIdeal h P sets δ y x) = 1 := by
  apply regularizedImageDensity_probability _ _ _ δ hδ
  exact measurable_const.add
    (jointBooleanSampler_contDiff (fun d : {d // ¬P d} => h d.val) _ sets).continuous.measurable

omit [Fintype G] [Fintype Z] in
theorem partitionedRegularizedIdeal_bounds (δ : ℝ≥0) (hδ : 0 < δ)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) :
    (∀ x, partitionedRegularizedIdeal h P sets δ y x ∈
      Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip (Σ d, O d) δ)
        (partitionedRegularizedIdeal h P sets δ y) := by
  apply regularizedImageDensity_bounds _ _ _ δ hδ
  exact measurable_const.add
    (jointBooleanSampler_contDiff (fun d : {d // ¬P d} => h d.val) _ sets).continuous.measurable

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff NNReal

theorem partitioned_profile_comparison_below
    {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (P : D → Prop) [DecidablePred P]
    (extra : G → Option α → Z)
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] [∀ d, Nonempty (O d)]
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d.val)
    (block : ∀ d, O d → B d.val) (hblock : ∀ d, Function.Injective (block d))
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) {ε : ℝ} (hε : 0 < ε) :
    let t := booleanPerturbationScale (B := fun d : {d // ¬P d} => B d.val) (O := O) (α := α)
      (PartitionedProfileNoiseIndex G Z α B h P) (fun d : {d // ¬P d} => h d.val)
      (fun d => unitProfilePrincipalSize (B := B) d.val)
      (fun d => 2 * unitProfilePrincipalSize (B := B) d.val) A T degree 1 1 ε
    0 < t ∧ t ≤ 1 ∧
      ∀ s : ℝ, |s| ≤ t →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      ∀ R : D → ℝ, ∀ f : Ω × ((Σ d, O d) → ℝ) → ℝ,
      Measurable f → (∀ p, ‖f p‖ ≤ 1) →
      |(∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R 0 (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))) -
        ∫ p, f (p.1, partitionedAllocatedProfileJet h P extra sets R s (z p.1) p.2)
          ∂μ.prod (jointBooleanSource (fun d : {d // ¬P d} => h d.val))| ≤ ε := by
  classical
  let c := fun a => partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) (z a)
  have hc (d : {d // ¬P d}) (b : B d.val) : Measurable (fun a => c a d b) := by
    dsimp [c, partitionedProfilePrincipal]
    exact measurable_const.add (measurable_const.mul (hz _))
  obtain ⟨t, ht, ht1, hteq, hcomp⟩ := exists_random_coefficient_smaller_tolerance_with_scale
    (Y := Ω × ((Σ d, O d) → ℝ)) c hc z hz sets hsets (fun d : {d // ¬P d} => h d.val)
    (fun d => hh d.val) hcard block hblock
    (fun d => unitProfilePrincipalSize (B := B) d.val)
    (fun d => 2 * unitProfilePrincipalSize (B := B) d.val)
    (fun d => unitProfilePrincipalSize_pos (B := B) d.val)
    (fun d => mul_nonneg (by norm_num) (unitProfilePrincipalSize_pos (B := B) d.val).le)
    ψ hψ hrange hzero hone A T hLip hTransition
    (partitionedProfileTerms (G := G) (B := B) h P)
    (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
    (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra)
    (fun d => hdegree d.val) (fun d e _ => e.property.trans (hdegree d.val))
    (Csum := 1) (Wsum := 1) zero_le_one zero_le_one (partitionedProfileTail_unit_sum h P) hε
  dsimp only
  rw [← hteq]
  refine ⟨ht, ht1, ?_⟩
  intro s hs μ hμ hbox R f hf hfb
  have hclow : ∀ᵐ a ∂μ, ∀ d o, unitProfilePrincipalSize (B := B) d.val ≤ |c a d (block d o)| := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).1
  have hcup : ∀ᵐ a ∂μ, ∀ d o, |c a d (block d o)| ≤ 2 * unitProfilePrincipalSize (B := B) d.val := by
    filter_upwards [hbox] with a ha
    intro d o
    exact (partitionedProfilePrincipal_unit_bounds h P (z a) ha d (block d o)).2
  have hcsum : ∀ᵐ a ∂μ, ∀ d, (∑ b, |c a d b|) ≤ 1 := by
    filter_upwards [hbox] with a ha
    exact partitionedProfilePrincipal_unit_sum h P (z a) ha
  let F : Ω × ((Σ d, O d) → ℝ) → Ω × ((Σ d, O d) → ℝ) := fun p =>
    (p.1, fun o => R o.1.val *
      (booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) (z p.1)) o + p.2 o))
  have hF : Measurable F := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro o
    have hzj := (hz (.inr ⟨o.1.val, constantCoefficientSlot _ _⟩)).comp
      (measurable_fst : Measurable (Prod.fst : Ω × ((Σ d, O d) → ℝ) → Ω))
    dsimp [F, booleanConstantJet, partitionedProfileConstant]
    split_ifs <;> fun_prop
  have hFactual (s : ℝ) (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, coefficientArraySampler (fun d : {d // ¬P d} => h d.val) (c a) sets
        (partitionedProfileTerms (G := G) (B := B) h P)
        (fun d _ => unitProfileTailSize (G := G) (B := B) h d.val)
        (fun _ e => e.val) (fun d e => .inr ⟨d.val, e⟩) (partitionedProfileInput P extra) s (z a) x) =
      (a, partitionedAllocatedProfileJet h P extra sets R s (z a) x) := by
    apply Prod.ext
    · rfl
    dsimp only [F]
    rw [partitionedAllocatedProfileJet_scale]
    unfold partitionedAllocatedProfileJet
    rw [partitionedProfileJet_eq h P extra sets hh]
    rfl
  have hFzero (a : Ω)
      (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ) :
      F (a, jointBooleanSampler (fun d : {d // ¬P d} => h d.val) (c a) sets x) =
        (a, partitionedAllocatedProfileJet h P extra sets R 0 (z a) x) := by
    simpa only [coefficientArraySampler_zero] using hFactual 0 a x
  simpa only [hFzero, hFactual] using hcomp s hs μ hμ hbox hclow hcup hcsum F hF f hf hfb

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

abbrev ActiveProfileCoefficientIndex {D : Type*} (G : Type*) (B : D → Type*)
    (h : D → ℕ) (P : D → Prop) := Σ d : {d // ¬P d}, SamplerCoefficientSlot G B h d.val

def profileNoiseWithActive {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    PartitionedProfileNoiseIndex G Z α B h P → ℝ
  | .inl j => z (.inl j)
  | .inr ⟨d, e⟩ => if hp : P d then z (.inr ⟨d, e⟩) else r ⟨⟨d, hp⟩, e⟩

theorem profileNoiseWithActive_active {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ)
    (d : {d // ¬P d}) (e : SamplerCoefficientSlot G B h d.val) :
    profileNoiseWithActive h P z r (.inr ⟨d.val, e⟩) = r ⟨d, e⟩ := by
  simp only [profileNoiseWithActive, dite_eq_right d.property]

theorem profileNoiseWithActive_abs_le {D G Z α : Type*} {B : D → Type*}
    (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ)
    (hz : ∀ j, |z j| ≤ 1) (hr : ∀ j, |r j| ≤ 1)
    (j : PartitionedProfileNoiseIndex G Z α B h P) :
    |profileNoiseWithActive h P z r j| ≤ 1 := by
  rcases j with j | ⟨d, e⟩
  · exact hz _
  · dsimp only [profileNoiseWithActive]
    split_ifs with hp
    · exact hz _
    · exact hr _

theorem profileNoiseWithActive_measurable {Ω D G Z α : Type*} [MeasurableSpace Ω]
    {B : D → Type*} (h : D → ℕ) (P : D → Prop) [DecidablePred P]
    (z : Ω → PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : Ω → ActiveProfileCoefficientIndex G B h P → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j)) (hr : ∀ j, Measurable (fun a => r a j))
    (j : PartitionedProfileNoiseIndex G Z α B h P) :
    Measurable (fun a => profileNoiseWithActive h P (z a) (r a) j) := by
  rcases j with j | ⟨d, e⟩
  · exact hz _
  · by_cases hp : P d
    · simpa only [profileNoiseWithActive, dite_eq_left hp] using hz (.inr ⟨d, e⟩)
    · simpa only [profileNoiseWithActive, dite_eq_right hp] using hr ⟨⟨d, hp⟩, e⟩

theorem partitionedIdealMap_withActive_eq {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] {O : {d // ¬P d} → Type*}
    (sets : ∀ d, O d → Finset α)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedIdealMap h P sets (profileNoiseWithActive h P z r) =
      partitionedIdealMap h P sets (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
  have hc : partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
      (profileNoiseWithActive h P z r) =
      partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B))
        (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
    funext d b
    simp only [partitionedProfilePrincipal, profileNoiseWithActive_active]
  have hb : partitionedProfileConstant h P (fun _ => 1 / 4) (profileNoiseWithActive h P z r) =
      partitionedProfileConstant h P (fun _ => 1 / 4) (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
    funext d
    simp only [partitionedProfileConstant, profileNoiseWithActive_active]
  unfold partitionedIdealMap
  rw [hc, hb]

theorem partitionedRegularizedIdeal_withActive_eq {D G Z α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)]
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0)
    (z : PartitionedProfileNoiseIndex G Z α B h P → ℝ)
    (r : ActiveProfileCoefficientIndex G B h P → ℝ) :
    partitionedRegularizedIdeal h P sets δ (profileNoiseWithActive h P z r) =
      partitionedRegularizedIdeal h P sets δ (profileNoiseWithActive (Z := Z) (α := α) h P (fun _ => 0) r) := by
  unfold partitionedRegularizedIdeal
  rw [partitionedIdealMap_withActive_eq]

end Erdos3

end

end OAI
