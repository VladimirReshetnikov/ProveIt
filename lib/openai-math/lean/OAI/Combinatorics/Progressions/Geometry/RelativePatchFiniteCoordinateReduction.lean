import OAI.Combinatorics.Progressions.Lattices.IntegerBoxCoordinateEquiv

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ}

noncomputable def coordinateEquiv (A : PolynomialPatch X s d) (e : X ≃ Y) :
    PolynomialPatch Y s d :=
  A.reparam (fun i => MvPolynomial.X (e i)) (fun i => weightedSupportLE_X _ (e i))

@[simp] theorem coordinateEquiv_kernel (A : PolynomialPatch X s d) (e : X ≃ Y) :
    (A.coordinateEquiv e).kernel = A.kernel := rfl

@[simp] theorem coordinateEquiv_weight (A : PolynomialPatch X s d) (e : X ≃ Y) :
    (A.coordinateEquiv e).weight = A.weight := rfl

@[simp] theorem coordinateEquiv_complexity (A : PolynomialPatch X s d) (e : X ≃ Y) :
    relativePatchComplexity (A.coordinateEquiv e) = relativePatchComplexity A := rfl

@[simp] theorem coordinateEquiv_distinctWeights (A : PolynomialPatch X s d) (e : X ≃ Y) :
    relativePatchDistinctWeights (A.coordinateEquiv e) = relativePatchDistinctWeights A := rfl

theorem coordinateEquiv_value (A : PolynomialPatch X s d) (e : X ≃ Y) (y : Y → ℝ) :
    (A.coordinateEquiv e).value y = A.value (fun i => y (e i)) := by
  rw [coordinateEquiv, reparam_value]
  simp only [MvPolynomial.aeval_X]

end PolynomialPatch

theorem relativePatchBoxScore_coordinateEquiv
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s d : ℕ} (e : X ≃ Y) (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore (coordinateReindexedSides e N) (coordinateReindexedFunction e f)
      target (A.coordinateEquiv e) = relativePatchBoxScore N f target A := by
  unfold relativePatchBoxScore
  simp only [PolynomialPatch.coordinateEquiv_value]
  exact coordinateReindexedFunction_expect e N
    (fun x => (f x - target) * A.value (fun i => (x i : ℝ)))

namespace ResidueBoxSlice

variable {X Y : Type*} {N : X → ℕ} {q : ℕ}

def coordinateReturn (e : X ≃ Y) (S : ResidueBoxSlice (coordinateReindexedSides e N) q) :
    ResidueBoxSlice N q where
  start i := S.start (e i)
  length i := S.length (e i)
  inside i j hj := by
    simpa only [coordinateReindexedSides, Equiv.symm_apply_apply] using S.inside (e i) j hj

theorem coordinateReturn_score [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s d : ℕ} (e : X ≃ Y) (S : ResidueBoxSlice (coordinateReindexedSides e N) q)
    (f : (X → ℤ) → ℝ) (target : ℝ) (A : PolynomialPatch Y s d) :
    relativePatchSliceScore (S.coordinateReturn e) f target (A.coordinateEquiv e.symm) =
      relativePatchSliceScore S (coordinateReindexedFunction e f) target A := by
  rw [← relativePatchBoxScore_pullback, ← relativePatchBoxScore_pullback]
  have h := relativePatchBoxScore_coordinateEquiv e.symm S.length
    (S.integerPullback (coordinateReindexedFunction e f)) target A
  convert h using 1
  congr 1
  funext x
  simp only [coordinateReindexedFunction, integerPullback, integerAffine,
    coordinateReturn, Equiv.symm_apply_apply]
  rfl

end ResidueBoxSlice

theorem RelativePatchSliceConclusion.coordinateReturn
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {s rankBound : ℕ} {N : X → ℕ} {f : (X → ℤ) → ℝ} {target cost : ℝ}
    (e : X ≃ Y)
    (h : RelativePatchSliceConclusion s (coordinateReindexedSides e N)
      (coordinateReindexedFunction e f) target rankBound cost) :
    RelativePatchSliceConclusion s N f target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hd, hcomplexity, hscore⟩ := h
  refine ⟨q, hq, S.coordinateReturn e, d, A.coordinateEquiv e.symm, ?_,
    hd, hcomplexity, ?_⟩
  · intro i
    simpa only [coordinateReindexedSides, ResidueBoxSlice.coordinateReturn,
      Equiv.symm_apply_apply] using hlength (e i)
  · rwa [ResidueBoxSlice.coordinateReturn_score]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def RelativePatchFinInductionRule (s n₀ stage : ℕ) (τ : ℝ)
    (cutoff cost : ℝ → ℝ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (n : ℕ), 0 < n → (n : ℝ) ≤ p →
      ∀ (N : Fin n → ℕ), (∀ i, Real.exp (cutoff p) ≤ (N i : ℝ)) →
      ∀ (f : (Fin n → ℤ) → ℝ),
        (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (d : ℕ) (A : PolynomialPatch (Fin n) s d),
          relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage →
          Real.exp (-p) ≤ relativePatchBoxScore N f a A →
          RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ)
            (d₀ + s * d) (cost p)

theorem RelativePatchFinInductionRule.to_general
    {s n₀ stage : ℕ} {τ : ℝ} {cutoff cost : ℝ → ℝ}
    (hfin : RelativePatchFinInductionRule s n₀ stage τ cutoff cost) :
    RelativePatchInductionRule s n₀ stage τ cutoff cost := by
  intro p a Λ d₀ hp ha haΛ hΛ habsolute X _ _ _ hX N hN f hf hfree d A hA hstage hscore
  let e : X ≃ Fin (Fintype.card X) := Fintype.equivFin X
  have hN' : ∀ i, Real.exp (cutoff p) ≤ (coordinateReindexedSides e N i : ℝ) :=
    fun i => hN (e.symm i)
  have hscore' : Real.exp (-p) ≤ relativePatchBoxScore (coordinateReindexedSides e N)
      (coordinateReindexedFunction e f) a (A.coordinateEquiv e) := by
    rwa [relativePatchBoxScore_coordinateEquiv]
  exact (hfin p a Λ d₀ hp ha haΛ hΛ habsolute (Fintype.card X) Fintype.card_pos hX
    (coordinateReindexedSides e N) hN' (coordinateReindexedFunction e f)
    (coordinateReindexedFunction_bounds e N f hf)
    (coordinateReindexedFunction_apFree e N f hfree)
    d (A.coordinateEquiv e) hA hstage hscore').coordinateReturn e

theorem RelativePatchInductionRule.to_fin
    {s n₀ stage : ℕ} {τ : ℝ} {cutoff cost : ℝ → ℝ}
    (h : RelativePatchInductionRule s n₀ stage τ cutoff cost) :
    RelativePatchFinInductionRule s n₀ stage τ cutoff cost := by
  intro p a Λ d₀ hp ha haΛ hΛ habsolute n hn hnp N hN f hf hfree d A hA hstage hscore
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact h p a Λ d₀ hp ha haΛ hΛ habsolute (Fin n) (by simpa using hnp)
    N hN f hf hfree d A hA hstage hscore

theorem relativePatchInductionRule_iff_fin
    (s n₀ stage : ℕ) (τ : ℝ) (cutoff cost : ℝ → ℝ) :
    RelativePatchInductionRule s n₀ stage τ cutoff cost ↔
      RelativePatchFinInductionRule s n₀ stage τ cutoff cost :=
  ⟨RelativePatchInductionRule.to_fin, RelativePatchFinInductionRule.to_general⟩

end Erdos3

end

end OAI
