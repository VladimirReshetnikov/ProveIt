/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal

namespace OAI

section

namespace Erdos3

def finiteSplitPoint_linearPart {K : Type*} (keep : K → Prop) [DecidablePred keep] :
    ({k // keep k} → ℤ) →+ (K → ℤ) where
  toFun x := finiteSplitPoint keep x 0
  map_zero' := by
    funext k
    by_cases hk : keep k <;> simp [finiteSplitPoint, hk]
  map_add' x y := by
    funext k
    by_cases hk : keep k <;> simp [finiteSplitPoint, hk]

theorem finiteSplitPoint_affine {K : Type*} (keep : K → Prop) [DecidablePred keep]
    (fixed : {k // ¬keep k} → ℤ) (x : {k // keep k} → ℤ) :
    finiteSplitPoint keep 0 fixed + finiteSplitPoint_linearPart keep x =
      finiteSplitPoint keep x fixed := by
  funext k
  by_cases hk : keep k <;> simp [finiteSplitPoint_linearPart, finiteSplitPoint, hk]

theorem finiteSplitPoint_injective {K : Type*} (keep : K → Prop) [DecidablePred keep]
    (fixed : {k // ¬keep k} → ℤ) :
    Function.Injective (fun x => finiteSplitPoint keep x fixed) := by
  intro x y hxy
  funext k
  simpa only [finiteSplitPoint_fixed] using congrFun hxy k

theorem IntegerVectorAPFree.coordinateFiber_preimage {K : Type*} {k : ℕ}
    {A : Set (K → ℤ)} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (keep : K → Prop) [DecidablePred keep] (fixed : {i // ¬keep i} → ℤ)
    (domain : Set ({i // keep i} → ℤ)) :
    IntegerVectorAPFree (domain ∩ (fun x => finiteSplitPoint keep x fixed) ⁻¹' A) k := by
  have h := hA.affine_preimage hk (finiteSplitPoint_linearPart keep)
    (finiteSplitPoint keep 0 fixed) domain (by
      simpa only [finiteSplitPoint_affine] using (finiteSplitPoint_injective keep fixed).injOn (s := domain))
  simpa only [finiteSplitPoint_affine] using h

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem allocatedSampler_shortAxis_retained_card_pos [Nonempty G]
    (H : ℕ) (hH : H ≤ S.value) :
    0 < Fintype.card {k : Vars // H ≤ sides k} := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨Sum.inl (Classical.arbitrary G), hH⟩⟩

omit [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem allocatedSampler_shortAxis_fixed_log_cost (H : ℕ) :
    (∑ k : {k : Vars // ¬H ≤ sides k}, Real.log (sides k : ℝ)) ≤
      (Fintype.card Vars : ℝ) * Real.log ((max H 1 : ℕ) : ℝ) := by
  have hlog : 0 ≤ Real.log ((max H 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast le_max_right H 1)
  have hpoint (k : {k : Vars // ¬H ≤ sides k}) :
      Real.log (sides k : ℝ) ≤ Real.log ((max H 1 : ℕ) : ℝ) := by
    have hpos : 0 < sides k := by
      rcases k.val with g | a
      · exact S.positive
      · exact allocatedPrincipalSides_pos B U b S a
    apply Real.log_le_log (Nat.cast_pos.mpr hpos)
    exact_mod_cast (Nat.lt_of_not_ge k.property).le.trans (le_max_left H 1)
  calc
    _ ≤ ∑ _k : {k : Vars // ¬H ≤ sides k}, Real.log ((max H 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (Fintype.card {k : Vars // ¬H ≤ sides k} : ℝ) * Real.log ((max H 1 : ℕ) : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Fintype.card_subtype_le _)) hlog

theorem allocatedSampler_shortAxis_split_mem (H : ℕ)
    (fixed : {k : Vars // ¬H ≤ sides k} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < sides k)
    (x : {k : Vars // H ≤ sides k} → ℤ)
    (hx : x ∈ integerBox (fun k : {k : Vars // H ≤ sides k} => sides k)) :
    finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed ∈ integerBox sides := by
  apply (mem_integerBox sides _).mpr
  intro k
  by_cases hk : H ≤ sides k
  · simpa only [finiteSplitPoint, dite_eq_left hk] using
      (mem_integerBox _ x).mp hx ⟨k, hk⟩
  · simpa only [finiteSplitPoint, dite_eq_right hk] using hfixed ⟨k, hk⟩

theorem exists_allocatedSampler_shortAxis_fiber [Nonempty G]
    {s d : ℕ} (A : PolynomialPatch Vars s d) (H : ℕ) (hH : H ≤ S.value)
    (score : (Vars → ℤ) → ℝ) {a : ℝ}
    (hscore : a ≤ 𝔼 x ∈ integerBox sides, score x * A.value (fun k => (x k : ℝ))) :
    0 < Fintype.card {k : Vars // H ≤ sides k} ∧
      (∀ k : {k : Vars // H ≤ sides k}, H ≤ sides k) ∧
      ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
        (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
        (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).kernel.lip = A.kernel.lip ∧
        (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).weight = A.weight ∧
        (∀ x : {k : Vars // H ≤ sides k} → ℤ,
          (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).value (fun k => (x k : ℝ)) =
            A.value (fun k => ((finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed k : ℤ) : ℝ))) ∧
        a ≤ 𝔼 x ∈ integerBox (fun k : {k : Vars // H ≤ sides k} => sides k),
          score (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed) *
            (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed).value (fun k => (x k : ℝ)) := by
  refine ⟨allocatedSampler_shortAxis_retained_card_pos B U b S H hH, fun k => k.property, ?_⟩
  have hpos (k : Vars) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr k => exact allocatedPrincipalSides_pos B U b S k
  obtain ⟨fixed, hfixed, hmean⟩ := A.exists_coordinate_fiber_score sides hpos
    (fun k : Vars => H ≤ sides k) score hscore
  refine ⟨fixed, hfixed, rfl, rfl, ?_, ?_⟩
  · intro x
    rw [A.coordinateFiber_value]
    congr 1
    funext k
    by_cases hk : H ≤ sides k <;> simp only [finiteSplitPoint, hk, dite_true, dite_false]
  · convert hmean using 1
    apply Finset.expect_congr
    · ext x
      simp only [mem_integerBox]
    · intro x _
      congr 1
      apply congrArg score
      funext k
      by_cases hk : H ≤ sides k <;> simp only [finiteSplitPoint, hk, dite_true, dite_false]

theorem allocatedSampler_shortAxis_support_progression_free {k : ℕ}
    (f : (Vars → ℤ) → ℝ)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} k)
    (hk : 2 ≤ k) (H : ℕ) (fixed : {i : Vars // ¬H ≤ sides i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i) :
    IntegerVectorAPFree
      {x | x ∈ integerBox (fun i : {i : Vars // H ≤ sides i} => sides i) ∧
        f (finiteSplitPoint (fun i : Vars => H ≤ sides i) x fixed) ≠ 0} k := by
  have hfiber := hfree.coordinateFiber_preimage hk (fun i : Vars => H ≤ sides i) fixed
    (integerBox (fun i : {i : Vars // H ≤ sides i} => sides i) : Set _)
  apply hfiber.mono
  intro x hx
  exact ⟨hx.1, allocatedSampler_shortAxis_split_mem B U b S H fixed hfixed x hx.1, hx.2⟩

theorem allocatedSampler_shortAxis_progression_free {X : Type*} {k : ℕ}
    {A : Set (X → ℤ)} (hA : IntegerVectorAPFree A k) (hk : 2 ≤ k)
    (z : (X → ℤ) × (Option Vars × X → ℤ))
    (hinj : Set.InjOn (fun x => BooleanCubeKernel.jointIntegerPhysicalSite x z)
      (integerBox sides : Set (Vars → ℤ)))
    (H : ℕ) (fixed : {i : Vars // ¬H ≤ sides i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < sides i) :
    IntegerVectorAPFree
      ((integerBox (fun i : {i : Vars // H ≤ sides i} => sides i) : Set _) ∩
        (fun x => BooleanCubeKernel.jointIntegerPhysicalSite
          (finiteSplitPoint (fun i : Vars => H ≤ sides i) x fixed) z) ⁻¹' A) k := by
  have hfull := BooleanCubeKernel.joint_sample_progression_free hA hk z
    (integerBox sides : Set (Vars → ℤ)) hinj
  have hfiber := hfull.coordinateFiber_preimage hk (fun i : Vars => H ≤ sides i) fixed
    (integerBox (fun i : {i : Vars // H ≤ sides i} => sides i) : Set _)
  apply hfiber.mono
  intro x hx
  exact ⟨hx.1, allocatedSampler_shortAxis_split_mem B U b S H fixed hfixed x hx.1, hx.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G] [Nonempty G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem exists_allocatedSampler_relative_induction
    {s n₀ stage d₀ d : ℕ} {τ : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage τ cutoff cost)
    {p pchild a Λ : ℝ} (hp : 2 ≤ p) (hpp : p ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (A : PolynomialPatch Vars s d)
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage)
    (hscore : Real.exp (-pchild) ≤ relativePatchBoxScore sides f a A) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-τ) ^ (stage+1) * Λ) (d₀+s*d) (cost pchild) := by
  obtain ⟨hpos, _, fixed, hfixed, _, _, _, hmean⟩ :=
    exists_allocatedSampler_shortAxis_fiber B U b S A H hH (fun x => f x-a) hscore
  let : Nonempty {k : Vars // H ≤ sides k} := Fintype.card_pos_iff.mp hpos
  have hcard : (Fintype.card {k : Vars // H ≤ sides k} : ℝ) ≤ pchild :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hDim
  refine ⟨fixed, hfixed, ?_⟩
  apply ih pchild a Λ d₀ (hp.trans hpp)
    ((Real.exp_le_exp.mpr (neg_le_neg hpp)).trans ha) haΛ hΛ
    (habsolute.mono hpp) {k : Vars // H ≤ sides k} hcard
    (fun k => sides k) (fun k => hHcut.trans (Nat.cast_le.mpr k.property))
    (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
    (fun x hx => hf _ (allocatedSampler_shortAxis_split_mem B U b S H fixed hfixed x hx))
    (allocatedSampler_shortAxis_support_progression_free B U b S f hfree (by omega) H fixed hfixed)
    d (A.coordinateFiber (fun k : Vars => H ≤ sides k) fixed)
  · simpa only [relativePatchComplexity_coordinateFiber] using hA
  · simpa only [relativePatchDistinctWeights_coordinateFiber] using hstage
  · exact hmean

end Erdos3.VectorPolynomial

end

end OAI
