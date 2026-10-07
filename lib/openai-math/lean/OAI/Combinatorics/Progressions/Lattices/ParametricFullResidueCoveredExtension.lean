import OAI.Combinatorics.Progressions.Estimates.LayeredCoverSiteExtension

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped Classical NNReal Matrix

theorem exists_normalized_full_residue_map
    {D E : Type*} [Fintype D] [Fintype E] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D))
    (bW : Basis E ℤ (latticeSection (standardEuclideanLattice D) W))
    (b : Basis (Fin n) ℝ Wᗮ)
    (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (q : ℕ) [NeZero q] :
    ∃ r : (D → ZMod q) → (Fin n ⊕ E → ZMod q),
      ∀ (z : Fin n → ℤ) (w : E → ℤ),
        r (fun i => (latticeDeckInteger W bW b hb z w i : ZMod q)) =
          Sum.elim (fun i => (z i : ZMod q)) (fun i => (w i : ZMod q)) := by
  obtain ⟨A, _hA, hres⟩ := standardLatticeCoordinates_residue W bW b hb q
  refine ⟨fun a => integerResidueMatrix A q *ᵥ a, ?_⟩
  intro z w
  change integerResidueMatrix A q *ᵥ
    integerResidueMap D q (latticeDeckInteger W bW b hb z w) = _
  rw [← hres, latticeDeckInteger_coordinates]
  funext i
  cases i <;> rfl

theorem exists_layered_full_residue_extension
    {M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q : ℕ) [NeZero q]
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (x : ∀ j, W j × (Fin (n j) → ℤ)) (w : ∀ j, E j → ℤ),
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (fun a => (((normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
          ((bW a.1).equivFun.symm (w a.1)).val).val a.2 / q : ℝ) : UnitAddCircle)) =
        f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)))
          (fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  choose r hr using (fun j => exists_normalized_full_residue_map (W j) (bW j) (b j) (hb j) q)
  let label : ((Σ j, D j) → ZMod q) → (∀ j, Fin (n j) ⊕ E j → ZMod q) :=
    fun a j => r j (fun i => a ⟨j, i⟩)
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_integer_quarter_cover_extension q
    (fun a v => f (label a) v) L B (fun a => hf (label a)) (fun a v => hbound (label a) v)
  refine ⟨g, hg, hgb, ?_⟩
  intro x w hx
  let β : (Σ j, D j) → ℤ := fun a =>
    latticeDeckInteger (W a.1) (bW a.1) (b a.1) (hb a.1) (x a.1).2 (w a.1) a.2
  let v : (Σ j, D j) → ℝ := fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2
  have hlabel : label (fun a => (β a : ZMod q)) =
      fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)) := by
    funext j
    exact hr j (x j).2 (w j)
  have h := hvalue β v (fun a => hx a.1 a.2)
  rw [hlabel] at h
  have hpoint : (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
      fun a => (((normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
        ((bW a.1).equivFun.symm (w a.1)).val).val a.2 / q : ℝ) : UnitAddCircle) := by
    funext a
    have he := congrArg (fun z : EuclideanSpace ℝ (D a.1) => z a.2)
      (normalizedDeckPoint_identity (W a.1) (bW a.1) (b a.1) (hb a.1) (x a.1) (w a.1))
    change (normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
      ((bW a.1).equivFun.symm (w a.1)).val).val a.2 = v a + (β a : ℝ) at he
    rw [he, add_comm (β a : ℝ)]
  simpa only [hpoint] using h

end Erdos3

end

section

namespace Erdos3
open Module Submodule
open scoped Classical NNReal

theorem intCast_eq_residue_val_of_dvd {q d : ℕ} [NeZero d]
    (hqd : q ∣ d) (z : ℤ) (r : ZMod d) (hz : (z : ZMod d) = r) :
    (z : ZMod q) = (r.val : ZMod q) := by
  rw [← Int.cast_natCast]
  apply (ZMod.intCast_eq_intCast_iff z (r.val : ℤ) q).mpr
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hqd)
  apply (ZMod.intCast_eq_intCast_iff z (r.val : ℤ) d).mp
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hz

theorem exists_layered_full_residue_covered_extension
    {M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q d : ℕ) [NeZero q] [NeZero d] (hqd : q ∣ d)
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * q) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (u : ∀ j, W j) (x : ∀ j, W j × (Fin (n j) → ℤ)) (r : ∀ j, E j → ZMod d),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedCoveredChart (W j) (b j) (hb j) (bW j) d (x j, r j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (fun a => (((u a.1).val a.2 / q : ℝ) : UnitAddCircle)) =
          f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => ((r j i).val : ZMod q)))
            (fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_layered_full_residue_extension W bW b hb q f L B hf hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro u x r hu hx
  choose w hw hr using (fun j =>
    exists_covered_representative_offset (W j) (bW j) (b j) (hb j) d
      ((d : ℝ)⁻¹ • u j) (x j) (r j) (hu j))
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at hw
  have he : (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q))) =
      (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => ((r j i).val : ZMod q))) := by
    funext j i
    cases i with
    | inl i => rfl
    | inr i => exact intCast_eq_residue_val_of_dvd hqd (w j i) (r j i) (congrFun (hr j) i)
  simpa only [hw, he] using hvalue x w hx

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Classical NNReal Matrix

theorem exists_parametric_layered_full_residue_extension
    {Y : Type*} [PseudoMetricSpace Y]
    {M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q : ℕ) [NeZero q]
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → Y × ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : Y × ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (y : Y) (x : ∀ j, W j × (Fin (n j) → ℤ)) (w : ∀ j, E j → ℤ),
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (y, fun a => (((normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
          ((bW a.1).equivFun.symm (w a.1)).val).val a.2 / q : ℝ) : UnitAddCircle)) =
        f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)))
          (y, fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  choose r hr using (fun j => exists_normalized_full_residue_map (W j) (bW j) (b j) (hb j) q)
  let label : ((Σ j, D j) → ZMod q) → (∀ j, Fin (n j) ⊕ E j → ZMod q) :=
    fun a j => r j (fun i => a ⟨j, i⟩)
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_parametric_integer_quarter_cover_extension q
    (fun a v => f (label a) v) L B (fun a => hf (label a)) (fun a v => hbound (label a) v)
  refine ⟨g, hg, hgb, ?_⟩
  intro y x w hx
  let β : (Σ j, D j) → ℤ := fun a =>
    latticeDeckInteger (W a.1) (bW a.1) (b a.1) (hb a.1) (x a.1).2 (w a.1) a.2
  let v : (Σ j, D j) → ℝ := fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2
  have hlabel : label (fun a => (β a : ZMod q)) =
      fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q)) := by
    funext j
    exact hr j (x j).2 (w j)
  have h := hvalue β y v (fun a => hx a.1 a.2)
  rw [hlabel] at h
  have hpoint : (fun a => ((((β a : ℝ) + v a) / q : ℝ) : UnitAddCircle)) =
      fun a => (((normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
        ((bW a.1).equivFun.symm (w a.1)).val).val a.2 / q : ℝ) : UnitAddCircle) := by
    funext a
    have he := congrArg (fun z : EuclideanSpace ℝ (D a.1) => z a.2)
      (normalizedDeckPoint_identity (W a.1) (bW a.1) (b a.1) (hb a.1) (x a.1) (w a.1))
    change (normalizedLatticeRepresentative (W a.1) (b a.1) (hb a.1) (x a.1) +
      ((bW a.1).equivFun.symm (w a.1)).val).val a.2 = v a + (β a : ℝ) at he
    rw [he, add_comm (β a : ℝ)]
  simpa only [hpoint] using h

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Classical NNReal

theorem exists_parametric_layered_full_residue_covered_extension
    {Y : Type*} [PseudoMetricSpace Y]
    {M : Type*} [Fintype M] {D E : M → Type*}
    [∀ j, Fintype (D j)] [∀ j, DecidableEq (D j)] [∀ j, Fintype (E j)] {n : M → ℕ}
    (W : ∀ j, Submodule ℝ (EuclideanSpace ℝ (D j)))
    (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (D j)) (W j)))
    (b : ∀ j, Basis (Fin (n j)) ℝ (W j)ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (W j))
    (q d : ℕ) [NeZero q] [NeZero d] (hqd : q ∣ d)
    (f : (∀ j, Fin (n j) ⊕ E j → ZMod q) → Y × ((Σ j, D j) → ℝ) → ℂ)
    (L B : ℝ≥0) (hf : ∀ a, LipschitzWith L (f a)) (hbound : ∀ a v, ‖f a v‖ ≤ B) :
    ∃ g : Y × ((Σ j, D j) → UnitAddCircle) → ℂ,
      LipschitzWith (2 * max (L * max 1 (q : ℝ≥0)) (4 * B * q)) g ∧ (∀ y, ‖g y‖ ≤ 2 * B) ∧
      ∀ (y : Y) (u : ∀ j, W j) (x : ∀ j, W j × (Fin (n j) → ℤ)) (r : ∀ j, E j → ZMod d),
        (∀ j, (QuotientAddGroup.mk ((d : ℝ)⁻¹ • u j) : W j ⧸
          (latticeSection (standardEuclideanLattice (D j)) (W j)).toAddSubgroup) =
            normalizedCoveredChart (W j) (b j) (hb j) (bW j) d (x j, r j)) →
        (∀ j i, |normalizedLatticePoint (W j) (b j) (x j) i| ≤ 1 / 4) →
        g (y, fun a => (((u a.1).val a.2 / q : ℝ) : UnitAddCircle)) =
          f (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => ((r j i).val : ZMod q)))
            (y, fun a => normalizedLatticePoint (W a.1) (b a.1) (x a.1) a.2) := by
  obtain ⟨g, hg, hgb, hvalue⟩ := exists_parametric_layered_full_residue_extension W bW b hb q f L B hf hbound
  refine ⟨g, hg, hgb, ?_⟩
  intro y u x r hu hx
  choose w hw hr using (fun j =>
    exists_covered_representative_offset (W j) (bW j) (b j) (hb j) d
      ((d : ℝ)⁻¹ • u j) (x j) (r j) (hu j))
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  simp only [smul_smul, mul_inv_cancel₀ hd, one_smul] at hw
  have he : (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => (w j i : ZMod q))) =
      (fun j => Sum.elim (fun i => ((x j).2 i : ZMod q)) (fun i => ((r j i).val : ZMod q))) := by
    funext j i
    cases i with
    | inl i => rfl
    | inr i => exact intCast_eq_residue_val_of_dvd hqd (w j i) (r j i) (congrFun (hr j) i)
  simpa only [hw, he] using hvalue y x w hx

end Erdos3

end

end OAI
