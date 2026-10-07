import OAI.Combinatorics.Progressions.Geometry.CubicCoordinateSlices
import OAI.Combinatorics.Progressions.Geometry.TripleBoxAnchorApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeIntegerExpansion.fixCoordinate {σ : Type*} [Fintype σ] [DecidableEq σ]
    {s : ℕ} {p : ℝ} {f : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion (fun _ : σ => 1) s p f) (d : σ) (c : ℤ) :
    NativeIntegerExpansion (fun _ : σ => 1) s p (fun x => f (Function.update x d c)) := by
  let A : σ → σ → ℤ := fun i j => if i = d then 0 else if j = i then 1 else 0
  let b : σ → ℤ := fun i => if i = d then c else 0
  have heq (x : σ → ℤ) : integerAffineMap A b x = Function.update x d c := by
    funext i
    by_cases hi : i = d
    · subst i
      simp [integerAffineMap, A, b]
    · simp [integerAffineMap, A, b, hi, ite_mul]
  simpa only [heq] using E.affinePullback A b

theorem NativeMultidegreeNilcharacter.exists_cubic_anchor_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (i j : Fin V.outputDim × Fin V.outputDim) (shift : ℤ) (a : Fin 3 → ℤ),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 ((p + C) ^ C)
        (tripleBoxAnchorFactor (fun k h y => V.cubicAntisymmetricPair i j h y (k + shift)) a)) := by
  obtain ⟨A, _, hslice⟩ := NativeMultidegreeNilcharacter.exists_cubic_kernel_coordinate_slice
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := Q + (Q + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((R + Polynomial.C B) ^ B + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p V i j shift a
  have hp : 0 ≤ p := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let K := fun k h y => V.cubicAntisymmetricPair i j h y (k + shift)
  let q := (p + A) ^ A
  let r := q + (q + B) ^ B
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hqr : q ≤ r := le_add_of_nonneg_right (by positivity)
  have hbr : (q + B) ^ B ≤ r := le_add_of_nonneg_left hq
  obtain ⟨E₀⟩ := hslice V i j 0 (a 0) shift
  obtain ⟨E₁⟩ := hslice V i j 1 (a 1) shift
  obtain ⟨E₂⟩ := hslice V i j 2 (a 2) shift
  have E₀' : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun z => K (a 0) (z 1) (z 2)) := by simpa [K] using E₀
  have E₁' : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun z => K (z 0) (a 1) (z 2)) := by simpa [K] using E₁
  have E₂' : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun z => K (z 0) (z 1) (a 2)) := by simpa [K] using E₂
  have E₀₁ : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun z => K (a 0) (a 1) (z 2)) := by simpa using E₀'.fixCoordinate 1 (a 1)
  have E₀₂ : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun z => K (a 0) (z 1) (a 2)) := by simpa using E₀'.fixCoordinate 2 (a 2)
  have E₁₂ : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun z => K (z 0) (a 1) (a 2)) := by simpa using E₁'.fixCoordinate 2 (a 2)
  have E₀₁₂ : NativeIntegerExpansion (fun _ : Fin 3 => 1) 2 q
      (fun _ => K (a 0) (a 1) (a 2)) := by simpa using E₀₁.fixCoordinate 2 (a 2)
  obtain ⟨F₁⟩ := hmul hq E₀'.conjugate E₁'.conjugate
  obtain ⟨F₂⟩ := hmul hq E₀₁ E₂'.conjugate
  obtain ⟨F₃⟩ := hmul hq E₀₂ E₁₂
  obtain ⟨G₁⟩ := hmul hr (F₁.mono hbr) (F₂.mono hbr)
  obtain ⟨G₂⟩ := hmul hr (F₃.mono hbr) (E₀₁₂.conjugate.mono hqr)
  obtain ⟨H⟩ := hmul (by positivity : 0 ≤ (r + B) ^ B) G₁ G₂
  have hcost : ((r + B) ^ B + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨H.mono hcost⟩

end Erdos3

end

end OAI
