import OAI.Combinatorics.Progressions.Geometry.NativeMixedCoordinateSlices
import OAI.Combinatorics.Progressions.Geometry.QuarticCoordinateSlices

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeIntegerExpansion.boxCornerPullback {n s : ℕ} {p : ℝ}
    {F : (Fin n → ℤ) → ℂ} (E : NativeIntegerExpansion (fun _ : Fin n => 1) s p F)
    (a : Fin n → ℤ) (ω : Fin n → Bool) :
    NativeIntegerExpansion (fun _ : Fin n => 1) s p (fun x => F (boxCorner x a ω)) := by
  let A : Fin n → Fin n → ℤ := fun i j => if ω i then 0 else if j = i then 1 else 0
  let b : Fin n → ℤ := fun i => if ω i then a i else 0
  have hmap (x : Fin n → ℤ) : integerAffineMap A b x = boxCorner x a ω := by
    funext i
    cases h : ω i <;> simp [integerAffineMap, A, b, boxCorner, h, ite_mul]
  simpa only [hmap] using E.affinePullback A b

noncomputable def NativeIntegerExpansion.conjugationPower {σ : Type*} {w : σ → ℕ}
    {s : ℕ} {p : ℝ} {F : (σ → ℤ) → ℂ} (E : NativeIntegerExpansion w s p F) (n : ℕ) :
    NativeIntegerExpansion w s p (fun x => Erdos3.conjugationPower n (F x)) := by
  by_cases h : n % 2 = 0
  · simpa only [conjugationPower_eq_if_mod, h, ite_true] using E
  · simpa only [conjugationPower_eq_if_mod, h, ite_false] using E.conjugate

theorem NativeMultidegreeNilcharacter.exists_quartic_corner_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (i j : Fin W.outputDim) (a : Fin 4 → ℤ) (ω : Fin 4 → Bool),
      ω ≠ (fun _ => false) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
        (fun x => W.quarticAntisymmetric i j (boxCorner x a ω))) := by
  obtain ⟨C, hC, hslice⟩ := NativeMultidegreeNilcharacter.exists_quartic_kernel_coordinate_slice
  refine ⟨C, hC, ?_⟩
  intro p W i j a ω hω
  obtain ⟨k, hk⟩ := exists_true_of_ne_false hω
  obtain ⟨E⟩ := hslice W i j k (a k)
  have hupdate (x : Fin 4 → ℤ) :
      Function.update (boxCorner x a ω) k (a k) = boxCorner x a ω := by
    funext l
    by_cases h : l = k
    · subst l
      simp [boxCorner, hk]
    · simp [h]
  exact ⟨by simpa only [hupdate] using E.boxCornerPullback a ω⟩

theorem NativeMultidegreeNilcharacter.exists_quartic_anchor_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
      (i j : Fin W.outputDim) (a : Fin 4 → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 ((p + C) ^ C)
        (boxCornerAnchor (W.quarticAntisymmetric i j) a)) := by
  obtain ⟨A, _, hcorner⟩ := NativeMultidegreeNilcharacter.exists_quartic_corner_expansion
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget 15
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let S : Finset (Fin 4 → Bool) := Finset.univ.erase (fun _ => false)
  have hS : Fintype.card S = 15 := by norm_num [S, Fintype.card_fun]
  let e : Fin 15 ≃ S := (Fintype.equivFinOfCardEq hS).symm
  let f : Fin 15 → (Fin 4 → ℤ) → ℂ := fun l x =>
    conjugationPower (booleanWeight (e l).val)
      (W.quarticAntisymmetric i j (boxCorner x a (e l).val))
  have hf (l : Fin 15) : Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3 q (f l)) := by
    have hne : (e l).val ≠ (fun _ => false) := (Finset.mem_erase.mp (e l).property).1
    obtain ⟨E⟩ := hcorner W i j a (e l).val hne
    exact ⟨E.conjugationPower (booleanWeight (e l).val)⟩
  obtain ⟨E⟩ := hprod f hq hf
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have heq (x : Fin 4 → ℤ) : (∏ l, f l x) = boxCornerAnchor (W.quarticAntisymmetric i j) a x := by
    exact boxCornerAnchor_prod_equiv e (W.quarticAntisymmetric i j) a x
  exact ⟨by simpa only [heq] using E.mono hcost⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem NativeMultidegreeNilcharacter.exists_mixed_corner_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (a : Fin (n + 2) → ℤ) (ω : Fin (n + 2) → Bool),
      ω ≠ (fun _ => false) →
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (fun x => W.mixedAntisymmetric i j (boxCorner x a ω))) := by
  obtain ⟨C, hC, hslice⟩ := NativeMultidegreeNilcharacter.exists_mixed_kernel_coordinate_slice n
  refine ⟨C, hC, ?_⟩
  intro p W i j a ω hω
  obtain ⟨k, hk⟩ := exists_true_of_ne_false hω
  obtain ⟨E⟩ := hslice W i j k (a k)
  have hupdate (x : Fin (n + 2) → ℤ) :
      Function.update (boxCorner x a ω) k (a k) = boxCorner x a ω := by
    funext l
    by_cases h : l = k
    · subst l
      simp [boxCorner, hk]
    · simp [h]
  exact ⟨by simpa only [hupdate] using E.boxCornerPullback a ω⟩

theorem NativeMultidegreeNilcharacter.exists_mixed_anchor_expansion (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      (i j : Fin W.outputDim) (a : Fin (n + 2) → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) ((p + C) ^ C)
        (boxCornerAnchor (W.mixedAntisymmetric i j) a)) := by
  obtain ⟨A, _, hcorner⟩ := NativeMultidegreeNilcharacter.exists_mixed_corner_expansion n
  obtain ⟨B, _, hprod⟩ := NativeIntegerExpansion.exists_fin_prod_budget (2 ^ (n + 2) - 1)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W i j a
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  let S : Finset (Fin (n + 2) → Bool) := Finset.univ.erase (fun _ => false)
  have hS : Fintype.card S = 2 ^ (n + 2) - 1 := by simp [S]
  let e : Fin (2 ^ (n + 2) - 1) ≃ S := (Fintype.equivFinOfCardEq hS).symm
  let f : Fin (2 ^ (n + 2) - 1) → (Fin (n + 2) → ℤ) → ℂ := fun l x =>
    conjugationPower (booleanWeight (e l).val)
      (W.mixedAntisymmetric i j (boxCorner x a (e l).val))
  have hf (l : Fin (2 ^ (n + 2) - 1)) : Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1) q (f l)) := by
    have hne : (e l).val ≠ (fun _ => false) := (Finset.mem_erase.mp (e l).property).1
    obtain ⟨E⟩ := hcorner W i j a (e l).val hne
    exact ⟨E.conjugationPower (booleanWeight (e l).val)⟩
  obtain ⟨E⟩ := hprod f hq hf
  have hcost : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have heq (x : Fin (n + 2) → ℤ) : (∏ l, f l x) = boxCornerAnchor (W.mixedAntisymmetric i j) a x := by
    exact boxCornerAnchor_prod_equiv e (W.mixedAntisymmetric i j) a x
  exact ⟨by simpa only [heq] using E.mono hcost⟩

end Erdos3

end

end OAI
