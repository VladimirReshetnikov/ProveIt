/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

namespace BooleanCubeKernel

theorem exists_unconditioned_rootBudget_productive_family
    {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (P : K → ℕ) [∀ k, NeZero (P k)]
    (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive, a + σ / 2 ≤ 𝔼 u : ∀ k, ZMod (P k),
        f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := K) B τ N
  let R := spatialTrimMargin τ N
  have hB : 0 ≤ B :=
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _) :
      0 ≤ unconditionedResidueSiteBound P).trans hBP
  obtain ⟨_, _, hW, hscale, hwidth, hR, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := K) hB hσ hσ1 N hN
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1).1
  have hsite : Function.Injective (residueBoxIntegerPoint P) := by
    intro u v he
    funext k
    apply ZMod.val_injective
    have hk := congrFun he k
    change ((u k).val : ℤ) = ((v k).val : ℤ) at hk
    exact_mod_cast hk
  have hfit (u : ∀ k, ZMod (P k)) (j : X) : physicalSiteWidth (residueBoxIntegerPoint P u) W j ≤ (R j : ℝ) :=
    spatialTrimMargin_fits hB hτ.le (residueBoxIntegerPoint P u)
      ((residueBoxIntegerPoint_sum_abs_le P u).trans hBP) N j
  obtain ⟨hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_productive_family N R hR (residueBoxIntegerPoint P) hsite i
      (fun _ : X => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _) W hW hscale
      (unconditionedCollisionWidth_pos P hσ) (fun k => hwidth (some k, i)) hfit ha hσ hboundary
      (by simpa only [Nat.cast_one, mul_one] using (unconditionedCollisionWidth_collision P hσ).le)
      f hf hmean
  exact ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩

theorem exists_unconditioned_rootBudget_productive_family_equiv
    {K J X : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
    [Fintype X] [DecidableEq X]
    (P : J → ℕ) [∀ k, NeZero (P k)] (e : K ≃ J)
    (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {a σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive, a + σ / 2 ≤ 𝔼 u : ∀ k, ZMod (P k),
        f (jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val) ∈ integerBox N := by
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := K) B τ N
  let R := spatialTrimMargin τ N
  have hB : 0 ≤ B :=
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _) :
      0 ≤ unconditionedResidueSiteBound P).trans hBP
  obtain ⟨_, _, hW, hscale, hwidth, hR, hboundary⟩ :=
    unconditionedSpatialWidthBudget (K := K) hB hσ hσ1 N hN
  have hτ : 0 < τ := (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1).1
  have hsite : Function.Injective (fun (u : ∀ j, ZMod (P j)) (k : K) =>
      residueBoxIntegerPoint P u (e k)) := by
    intro u v he
    funext j
    apply ZMod.val_injective
    have hj := congrFun he (e.symm j)
    simp only [Equiv.apply_symm_apply] at hj
    change ((u j).val : ℤ) = ((v j).val : ℤ) at hj
    exact_mod_cast hj
  have hroot (u : ∀ j, ZMod (P j)) :
      (∑ k : K, |(residueBoxIntegerPoint P u (e k) : ℝ)|) ≤ B := by
    rw [e.sum_comp (fun j => |(residueBoxIntegerPoint P u j : ℝ)|)]
    exact (residueBoxIntegerPoint_sum_abs_le P u).trans hBP
  have hfit (u : ∀ j, ZMod (P j)) (j : X) :
      physicalSiteWidth (fun k => residueBoxIntegerPoint P u (e k)) W j ≤ (R j : ℝ) :=
    spatialTrimMargin_fits hB hτ.le (fun k => residueBoxIntegerPoint P u (e k))
      (hroot u) N j
  obtain ⟨hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_productive_family N R hR (fun u k => residueBoxIntegerPoint P u (e k)) hsite i
      (fun _ : X => 1) (fun _ => by decide) {0} (Finset.singleton_nonempty _) W hW hscale
      (unconditionedCollisionWidth_pos P hσ) (fun k => hwidth (some k, i)) hfit ha hσ hboundary
      (by simpa only [Nat.cast_one, mul_one] using (unconditionedCollisionWidth_collision P hσ).le)
      f hf hmean
  exact ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

theorem jointIntegerPhysicalSite_comp_equiv
    {K J X : Type*} [Fintype K] [Fintype J]
    (e : K ≃ J) (x : J → ℤ)
    (z : (X → ℤ) × (Option K × X → ℤ)) :
    jointIntegerPhysicalSite (fun k => x (e k)) z =
      jointIntegerPhysicalSite x
        (z.1, fun w => z.2 (Option.map e.symm w.1, w.2)) := by
  funext i
  simp only [jointIntegerPhysicalSite, integerPhysicalSite, Pi.add_apply,
    Option.map_none, Option.map_some]
  congr 2
  apply Fintype.sum_equiv e
  intro k
  simp only [Equiv.symm_apply_apply]

theorem exists_unconditioned_rootBudget_absolute_family
    (s n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)]
    (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  let f₀ := fun x => if x ∈ integerBox N then f x else 0
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ integerBox N
    · simpa only [f₀, ite_eq_left hx] using hf x hx
    · simp only [f₀, ite_eq_right hx, Set.mem_Icc, le_refl, zero_le_one, and_self]
  have hmean₀ : a + σ ≤ 𝔼 x ∈ integerBox N, f₀ x := by
    have he : (𝔼 x ∈ integerBox N, f₀ x) = 𝔼 x ∈ integerBox N, f x :=
      Finset.expect_congr rfl (fun x hx => ite_eq_left hx)
    rwa [he]
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_rootBudget_productive_family P B hBP i ha hσ hσ1 N hN f₀ hf₀ hmean₀
  refine ⟨hW, hR, hZ, productive, hmass, hinj, ?_, hinside⟩
  intro z hz
  have hlocal' : a ≤ 𝔼 u : ∀ k, ZMod (P k),
      f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val)) := by
    have h := hlocal z hz
    simp only [f₀, ite_eq_left (hinside z _)] at h
    linarith
  obtain ⟨hbound, hAP, hmean⟩ := unconditionedAbsoluteSample_input
    s N P (z.1.val,z.2.val) f hf hfree (hinj z hz) (hinside z) hlocal'
  exact habsolute P hprime hdistinct hcomparable hcutoff
    (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) hbound hAP hmean

theorem exists_unconditioned_rootBudget_absolute_family_of_zero_score
    (s n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)]
    (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (A : PolynomialPatch X s 0)
    (hscore : σ ≤ relativePatchBoxScore N f a A) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  have hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x :=
    zero_slot_score_mean_lower_bound A N hbox f hσ hscore
  have hσ1 : σ ≤ 1 := by
    have hcap : (𝔼 x ∈ integerBox N, f x) ≤ 1 :=
      Finset.expect_le hbox (fun x hx => (hf x hx).2)
    linarith
  exact exists_unconditioned_rootBudget_absolute_family s n₀ P B hBP i ha hσ hσ1 d₀ habsolute
    hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean

theorem exists_unconditioned_rootBudget_absolute_family_equiv
    (s n₀ : ℕ) {K X : Type*} [Fintype K] [DecidableEq K]
    [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)]
    (e : K ≃ Fin n₀) (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite (fun k => x (e k)) (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val) ∈ integerBox N := by
  let f₀ := fun x => if x ∈ integerBox N then f x else 0
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ integerBox N
    · simpa only [f₀, ite_eq_left hx] using hf x hx
    · simp only [f₀, ite_eq_right hx, Set.mem_Icc, le_refl, zero_le_one, and_self]
  have hmean₀ : a + σ ≤ 𝔼 x ∈ integerBox N, f₀ x := by
    have he : (𝔼 x ∈ integerBox N, f₀ x) = 𝔼 x ∈ integerBox N, f x :=
      Finset.expect_congr rfl (fun x hx => ite_eq_left hx)
    rwa [he]
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_unconditioned_rootBudget_productive_family_equiv P e B hBP i ha hσ hσ1 N hN f₀ hf₀ hmean₀
  refine ⟨hW, hR, hZ, productive, hmass, hinj, ?_, hinside⟩
  intro z hz
  have hlocal' : a ≤ 𝔼 u : ∀ k, ZMod (P k),
      f (jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val)) := by
    have h := hlocal z hz
    simp only [f₀, ite_eq_left (hinside z _)] at h
    linarith
  let zP : (X → ℤ) × (Option (Fin n₀) × X → ℤ) :=
    (z.1.val, fun w => z.2.val (Option.map e.symm w.1, w.2))
  have hphysical (x : Fin n₀ → ℤ) :
      jointIntegerPhysicalSite (fun k => x (e k)) (z.1.val,z.2.val) =
        jointIntegerPhysicalSite x zP :=
    jointIntegerPhysicalSite_comp_equiv e x (z.1.val,z.2.val)
  obtain ⟨hbound, hAP, hmean⟩ := unconditionedAbsoluteSample_input
    s N P zP f hf hfree
      (by simpa only [hphysical] using hinj z hz)
      (by simpa only [hphysical] using hinside z)
      (by simpa only [hphysical] using hlocal')
  simpa only [hphysical] using habsolute P hprime hdistinct hcomparable hcutoff
    (fun x => f (jointIntegerPhysicalSite x zP)) hbound hAP hmean

theorem exists_unconditioned_rootBudget_absolute_family_equiv_of_zero_score
    (s n₀ : ℕ) {K X : Type*} [Fintype K] [DecidableEq K]
    [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)]
    (e : K ≃ Fin n₀) (B : ℝ) (hBP : unconditionedResidueSiteBound P ≤ B) (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (hN : ∀ j, unconditionedSpatialWidthCutoff B
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (A : PolynomialPatch X s 0)
    (hscore : σ ≤ relativePatchBoxScore N f a A) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := K) B τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite (fun k => x (e k)) (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k)) (z.1.val,z.2.val) ∈ integerBox N := by
  have hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x :=
    zero_slot_score_mean_lower_bound A N hbox f hσ hscore
  have hσ1 : σ ≤ 1 := by
    have hcap : (𝔼 x ∈ integerBox N, f x) ≤ 1 :=
      Finset.expect_le hbox (fun x hx => (hf x hx).2)
    linarith
  exact exists_unconditioned_rootBudget_absolute_family_equiv s n₀ P e B hBP i ha hσ hσ1 d₀ habsolute
    hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean

end BooleanCubeKernel
end Erdos3

end

end OAI
