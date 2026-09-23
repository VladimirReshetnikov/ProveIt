import Surreal.Algebra.WickSemigroup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# The mixed quartic Wick model: exact Hilbert basis and irredundant tests

This file proves `wick:prop:quarticH` of
`docs/surcomplex/wick-summability-certificates/article.tex`, together with the incidence
parametrization stated just before it and the numerical model `wick:eq:mixedmodel` stated
just after it.

For `P = g₁ x⁴ + g₂ y⁴` with `C₁₁, C₁₂, C₂₂` all nonzero, use the coordinates
`(m₁, m₂; k₁₁, k₁₂, k₂₂)`, stored as `Fin 5 → ℕ` in this order. The count map
`(m, k) ↦ Am - Dk` is `quarticIncidence`, built from the columns `α¹ = (4, 0)`, `α² = (0, 4)`
of `A` and `D₁₁ = (2, 0)`, `D₁₂ = (1, 1)`, `D₂₂ = (0, 2)` of `D`. Its nonnegative kernel is
`S`, and the Hilbert basis of `S` (in the sense of `Surreal.Wick.hilbertBasis`, the minimal
nonzero elements of `S`) is exactly
`{h₁, h₂, h₃, h₄} = {(1,0;2,0,0), (0,1;0,0,2), (1,1;1,2,1), (1,1;0,4,0)}`.
Every element of `S` is `a h₁ + b h₂ + c h₃ + d h₄` with `c ≤ 1`, as in the source proof.

For weight data `(λ₁, λ₂; c₁₁, c₁₂, c₂₂)` in any additive commutative monoid `Γ`, the weight
`L` of `wick:eq:weight` satisfies `2 w₃ = w₁ + w₂ + w₄`, stated with `2 •` so that no
divisibility of `Γ` is needed. Hence, for `Γ` a linearly ordered cancellative commutative
monoid, positivity on the Hilbert basis (criterion (iii) of `wick:thm:main`), and equally
positivity on all of `S ∖ {0}` (criterion (ii)), is equivalent to `w₁ > 0`, `w₂ > 0`,
`w₄ > 0`. Over any nontrivial linearly ordered abelian group `Γ` (the report's standing
assumption is `Γ ≠ {0}`), none of these three tests follows from the other two. The
equivalence of (ii) and (iii) is proved for the kernel of an arbitrary count map; this is only
that clause of `wick:thm:main`.

For the model `C = [[t², 1], [1, t²]]`, `g₁ = g₂ = t⁻¹`, with `t` a monomial of valuation `ε`
in the Hahn field `R((t^Γ))`, the entries have valuations `-ε`, `2ε` and `0`
(`mixedModel_valuations`), and the weight at the data `(-ε, -ε; 2ε, 0, 2ε)` gives
`w₁ = w₂ = 3ε`, `w₃ = 2ε` and `w₄ = -2ε` (`mixedModel_weights`). For general `ε` these two
facts are proved separately; they are composed into one statement, feeding the actual orders
into `quarticWeight`, only over `ℂ((t^ℚ))` with `ε = 1`, where the weights are exactly
`3, 3, 2, -2` (`mixedModel_weights_rat`). For `ε > 0`, `h₄` is the only Hilbert basis element
of nonpositive weight.

Pending: the link between the Hilbert-basis criterion and actual strong summability of the
Wick atom family is `wick:thm:main`, which is not formalized here; the proposition is proved
as a statement about the criteria (ii) and (iii) of that theorem.
-/

namespace Surreal.Wick

section Generic

variable {ι Γ : Type*}

/-- The linear count functional `q ↦ ∑ᵢ qᵢ • bᵢ` on `ℕ^ι`. With `b = (λ, c)` it is the
weight `L(m, k)` of `wick:eq:weight`; with vertex columns `αᵃ` and negated edge columns
`-Dₑ` it is the incidence map `(m, k) ↦ Am - Dk` of `wick:eq:incidence`. -/
def countWeight [Fintype ι] [AddCommMonoid Γ] (b : ι → Γ) : (ι → ℕ) →+ Γ where
  toFun q := ∑ i, q i • b i
  map_zero' := by simp
  map_add' x y := by simp [add_nsmul, Finset.sum_add_distrib]

/-- Unfolding of `countWeight`: its value at `q` is `∑ᵢ qᵢ • bᵢ`. -/
theorem countWeight_apply [Fintype ι] [AddCommMonoid Γ] (b : ι → Γ) (q : ι → ℕ) :
    countWeight b q = ∑ i, q i • b i := rfl

/-- `wick:thm:main`, only the clause (ii) ⟺ (iii), for an arbitrary count map on `ℕ^ι` with
`ι` finite and a weight into an ordered cancellative commutative monoid: an additive weight is
positive on every nonzero element of the nonnegative kernel of the count map iff it is positive
on the finite Hilbert basis. -/
theorem forall_kernel_pos_iff_forall_hilbertBasis_pos [Finite ι] {G : Type*} [AddCommGroup G]
    [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
    (f : (ι → ℕ) →+ G) (L : (ι → ℕ) →+ Γ) :
    (∀ x, f x = 0 → x ≠ 0 → 0 < L x) ↔ ∀ h ∈ hilbertBasis f, 0 < L h := by
  constructor
  · intro H h hh
    exact H h hh.1.1 hh.1.2
  · intro H x hx hx0
    have key : ∀ y ∈ AddSubmonoid.closure (hilbertBasis f), y = 0 ∨ 0 < L y := by
      intro y hy
      induction hy using AddSubmonoid.closure_induction with
      | mem y hy => exact Or.inr (H y hy)
      | zero => exact Or.inl rfl
      | add a b _ _ ha hb =>
        rcases ha with rfl | ha
        · simpa using hb
        rcases hb with rfl | hb
        · simpa using Or.inr ha
        exact Or.inr (by rw [map_add]; exact add_pos ha hb)
    exact (key x (mem_closure_hilbertBasis f hx)).resolve_left hx0

end Generic

section Coordinates

private theorem le_iff_five {x y : Fin 5 → ℕ} :
    x ≤ y ↔ x 0 ≤ y 0 ∧ x 1 ≤ y 1 ∧ x 2 ≤ y 2 ∧ x 3 ≤ y 3 ∧ x 4 ≤ y 4 := by
  refine ⟨fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩, fun ⟨h0, h1, h2, h3, h4⟩ i => ?_⟩
  fin_cases i <;> assumption

private theorem eq_iff_five {x y : Fin 5 → ℕ} :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 ∧ x 3 = y 3 ∧ x 4 = y 4 := by
  refine ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl, rfl⟩, fun ⟨h0, h1, h2, h3, h4⟩ => ?_⟩
  funext i
  fin_cases i <;> assumption

end Coordinates

section Quartic

/-- The incidence map `(m, k) ↦ Am - Dk` of the mixed quartic model `P = g₁ x⁴ + g₂ y⁴` with
`C₁₁, C₁₂, C₂₂ ≠ 0`, in the coordinates `(m₁, m₂; k₁₁, k₁₂, k₂₂)`. The vertex columns are
`α¹ = (4, 0)`, `α² = (0, 4)` and the edge columns are `D₁₁ = (2, 0)`, `D₁₂ = (1, 1)`,
`D₂₂ = (0, 2)`. -/
def quarticIncidence : (Fin 5 → ℕ) →+ (Fin 2 → ℤ) :=
  countWeight ![![4, 0], ![0, 4], -![2, 0], -![1, 1], -![0, 2]]

/-- The incidence relations `4m₁ = 2k₁₁ + k₁₂` and `4m₂ = 2k₂₂ + k₁₂` define `S`. -/
theorem quarticIncidence_eq_zero_iff {x : Fin 5 → ℕ} :
    quarticIncidence x = 0 ↔ 4 * x 0 = 2 * x 2 + x 3 ∧ 4 * x 1 = 2 * x 4 + x 3 := by
  simp only [quarticIncidence, countWeight_apply, funext_iff, Fin.forall_fin_two,
    Fin.sum_univ_five, Pi.zero_apply]
  simp
  omega

/-- The parametrization before `wick:prop:quarticH`: `k₁₂ = 2s` and
`(m₁, m₂; k₁₁, k₁₂, k₂₂) = (m₁, m₂; 2m₁ - s, 2s, 2m₂ - s)` with `0 ≤ s ≤ 2 min(m₁, m₂)`,
the truncated subtractions being encoded additively. -/
theorem quarticIncidence_eq_zero_iff_exists {x : Fin 5 → ℕ} :
    quarticIncidence x = 0 ↔
      ∃ s, x 3 = 2 * s ∧ x 2 + s = 2 * x 0 ∧ x 4 + s = 2 * x 1 := by
  rw [quarticIncidence_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x 3 / 2, by omega, by omega, by omega⟩
  · rintro ⟨s, h1, h2, h3⟩
    omega

/-- The Hilbert basis element `h₁ = (1, 0; 2, 0, 0)`. -/
def quarticH₁ : Fin 5 → ℕ := ![1, 0, 2, 0, 0]

/-- The Hilbert basis element `h₂ = (0, 1; 0, 0, 2)`. -/
def quarticH₂ : Fin 5 → ℕ := ![0, 1, 0, 0, 2]

/-- The Hilbert basis element `h₃ = (1, 1; 1, 2, 1)`. -/
def quarticH₃ : Fin 5 → ℕ := ![1, 1, 1, 2, 1]

/-- The Hilbert basis element `h₄ = (1, 1; 0, 4, 0)`. -/
def quarticH₄ : Fin 5 → ℕ := ![1, 1, 0, 4, 0]

/-- `wick:prop:quarticH`, generation, as in the source proof: every element of `S` is
`a h₁ + b h₂ + c h₃ + d h₄` with `c ≤ 1`. -/
theorem exists_eq_quarticH_combination {x : Fin 5 → ℕ} (hx : quarticIncidence x = 0) :
    ∃ a b c d : ℕ, c ≤ 1 ∧
      x = a • quarticH₁ + b • quarticH₂ + c • quarticH₃ + d • quarticH₄ := by
  rw [quarticIncidence_eq_zero_iff] at hx
  refine ⟨x 0 - x 3 / 4 - x 3 / 2 % 2, x 1 - x 3 / 4 - x 3 / 2 % 2, x 3 / 2 % 2, x 3 / 4,
    by omega, ?_⟩
  rw [eq_iff_five]
  simp [quarticH₁, quarticH₂, quarticH₃, quarticH₄]
  omega

/-- Every nonzero element of `S` lies above one of `h₁, h₂, h₃, h₄`. -/
theorem exists_quarticH_le {x : Fin 5 → ℕ} (hx : quarticIncidence x = 0) (h0 : x ≠ 0) :
    quarticH₁ ≤ x ∨ quarticH₂ ≤ x ∨ quarticH₃ ≤ x ∨ quarticH₄ ≤ x := by
  rw [quarticIncidence_eq_zero_iff] at hx
  rw [Ne, eq_iff_five] at h0
  simp only [le_iff_five, quarticH₁, quarticH₂, quarticH₃, quarticH₄]
  simp only [Pi.zero_apply] at h0
  simp
  omega

/-- `h₁` lies in `S`. -/
theorem quarticIncidence_quarticH₁ : quarticIncidence quarticH₁ = 0 := by
  rw [quarticIncidence_eq_zero_iff]; simp [quarticH₁]

/-- `h₂` lies in `S`. -/
theorem quarticIncidence_quarticH₂ : quarticIncidence quarticH₂ = 0 := by
  rw [quarticIncidence_eq_zero_iff]; simp [quarticH₂]

/-- `h₃` lies in `S`. -/
theorem quarticIncidence_quarticH₃ : quarticIncidence quarticH₃ = 0 := by
  rw [quarticIncidence_eq_zero_iff]; simp [quarticH₃]

/-- `h₄` lies in `S`. -/
theorem quarticIncidence_quarticH₄ : quarticIncidence quarticH₄ = 0 := by
  rw [quarticIncidence_eq_zero_iff]; simp [quarticH₄]

/-- Each of `h₁, h₂, h₃, h₄` is a minimal nonzero element of `S`. -/
theorem eq_quarticH_of_le {y h : Fin 5 → ℕ}
    (hh : h = quarticH₁ ∨ h = quarticH₂ ∨ h = quarticH₃ ∨ h = quarticH₄)
    (hy : quarticIncidence y = 0) (h0 : y ≠ 0) (hle : y ≤ h) : y = h := by
  rw [quarticIncidence_eq_zero_iff] at hy
  rw [Ne, eq_iff_five] at h0
  simp only [Pi.zero_apply] at h0
  rw [le_iff_five] at hle
  rw [eq_iff_five]
  rcases hh with rfl | rfl | rfl | rfl <;>
    simp only [quarticH₁, quarticH₂, quarticH₃, quarticH₄] at hle ⊢ <;> simp at hle ⊢ <;> omega

/-- `wick:prop:quarticH`: the Hilbert basis of the mixed quartic semigroup `S` is exactly
`{h₁, h₂, h₃, h₄}`. -/
theorem hilbertBasis_quarticIncidence :
    hilbertBasis quarticIncidence = {quarticH₁, quarticH₂, quarticH₃, quarticH₄} := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hf, h0⟩, hmin⟩
    have hmem : ∀ h, (h = quarticH₁ ∨ h = quarticH₂ ∨ h = quarticH₃ ∨ h = quarticH₄) →
        h ≤ x → x = h := by
      rintro h hh hle
      have hker : quarticIncidence h = 0 ∧ h ≠ 0 := by
        rcases hh with rfl | rfl | rfl | rfl
        · exact ⟨quarticIncidence_quarticH₁, fun e => by simpa [quarticH₁] using congrFun e 0⟩
        · exact ⟨quarticIncidence_quarticH₂, fun e => by simpa [quarticH₂] using congrFun e 1⟩
        · exact ⟨quarticIncidence_quarticH₃, fun e => by simpa [quarticH₃] using congrFun e 0⟩
        · exact ⟨quarticIncidence_quarticH₄, fun e => by simpa [quarticH₄] using congrFun e 0⟩
      exact le_antisymm (hmin hker hle) hle
    rcases exists_quarticH_le hf h0 with h | h | h | h
    · exact Or.inl (hmem _ (Or.inl rfl) h)
    · exact Or.inr (Or.inl (hmem _ (Or.inr (Or.inl rfl)) h))
    · exact Or.inr (Or.inr (Or.inl (hmem _ (Or.inr (Or.inr (Or.inl rfl))) h)))
    · exact Or.inr (Or.inr (Or.inr (hmem _ (Or.inr (Or.inr (Or.inr rfl))) h)))
  · intro hx
    have hker : quarticIncidence x = 0 ∧ x ≠ 0 := by
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨quarticIncidence_quarticH₁, fun e => by simpa [quarticH₁] using congrFun e 0⟩
      · exact ⟨quarticIncidence_quarticH₂, fun e => by simpa [quarticH₂] using congrFun e 1⟩
      · exact ⟨quarticIncidence_quarticH₃, fun e => by simpa [quarticH₃] using congrFun e 0⟩
      · exact ⟨quarticIncidence_quarticH₄, fun e => by simpa [quarticH₄] using congrFun e 0⟩
    exact ⟨hker, fun y ⟨hy, hy0⟩ hle => (eq_quarticH_of_le hx hy hy0 hle).ge⟩

end Quartic

section Weights

variable {Γ : Type*}

/-- The weight `L` of `wick:eq:weight` for the mixed quartic model, with data
`(λ₁, λ₂; c₁₁, c₁₂, c₂₂)` in the coordinate order of `quarticIncidence`. -/
def quarticWeight [AddCommMonoid Γ] (l₁ l₂ c₁₁ c₁₂ c₂₂ : Γ) : (Fin 5 → ℕ) →+ Γ :=
  countWeight ![l₁, l₂, c₁₁, c₁₂, c₂₂]

section Monoid

variable [AddCommMonoid Γ] (l₁ l₂ c₁₁ c₁₂ c₂₂ : Γ)

/-- `w₁ = λ₁ + 2c₁₁`. -/
theorem quarticWeight_quarticH₁ :
    quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₁ = l₁ + 2 • c₁₁ := by
  simp [quarticWeight, countWeight_apply, Fin.sum_univ_five, quarticH₁]

/-- `w₂ = λ₂ + 2c₂₂`. -/
theorem quarticWeight_quarticH₂ :
    quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₂ = l₂ + 2 • c₂₂ := by
  simp [quarticWeight, countWeight_apply, Fin.sum_univ_five, quarticH₂]

/-- `w₃ = λ₁ + λ₂ + c₁₁ + 2c₁₂ + c₂₂`. -/
theorem quarticWeight_quarticH₃ :
    quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₃ = l₁ + l₂ + c₁₁ + 2 • c₁₂ + c₂₂ := by
  simp [quarticWeight, countWeight_apply, Fin.sum_univ_five, quarticH₃, add_assoc]

/-- `w₄ = λ₁ + λ₂ + 4c₁₂`. -/
theorem quarticWeight_quarticH₄ :
    quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₄ = l₁ + l₂ + 4 • c₁₂ := by
  simp [quarticWeight, countWeight_apply, Fin.sum_univ_five, quarticH₄, add_assoc]

/-- `wick:prop:quarticH`: `w₃ = (w₁ + w₂ + w₄) / 2`, stated without division. -/
theorem two_nsmul_quarticWeight_quarticH₃ :
    2 • quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₃ =
      quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₁ + quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₂ +
        quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ quarticH₄ := by
  rw [quarticWeight_quarticH₁, quarticWeight_quarticH₂, quarticWeight_quarticH₃,
    quarticWeight_quarticH₄]
  abel

end Monoid

section OrderedMonoid

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  (l₁ l₂ c₁₁ c₁₂ c₂₂ : Γ)

/-- `wick:prop:quarticH`: the Hilbert-basis criterion (iii) of `wick:thm:main` reduces to the
three tests `w₁ = λ₁ + 2c₁₁ > 0`, `w₂ = λ₂ + 2c₂₂ > 0`, `w₄ = λ₁ + λ₂ + 4c₁₂ > 0`. -/
theorem forall_hilbertBasis_quarticWeight_pos_iff :
    (∀ h ∈ hilbertBasis quarticIncidence, 0 < quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ h) ↔
      0 < l₁ + 2 • c₁₁ ∧ 0 < l₂ + 2 • c₂₂ ∧ 0 < l₁ + l₂ + 4 • c₁₂ := by
  simp only [hilbertBasis_quarticIncidence, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  rw [quarticWeight_quarticH₁, quarticWeight_quarticH₂, quarticWeight_quarticH₄]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h4⟩
    refine ⟨h1, h2, ?_, h4⟩
    have h := two_nsmul_quarticWeight_quarticH₃ l₁ l₂ c₁₁ c₁₂ c₂₂
    rw [quarticWeight_quarticH₁, quarticWeight_quarticH₂, quarticWeight_quarticH₄] at h
    refine (nsmul_pos_iff two_ne_zero).mp ?_
    rw [h]
    exact add_pos (add_pos h1 h2) h4

/-- `wick:prop:quarticH`, with criterion (ii) of `wick:thm:main`: the weight is positive on
every nonzero element of `S` iff `w₁ > 0`, `w₂ > 0` and `w₄ > 0`. -/
theorem forall_kernel_quarticWeight_pos_iff :
    (∀ x, quarticIncidence x = 0 → x ≠ 0 → 0 < quarticWeight l₁ l₂ c₁₁ c₁₂ c₂₂ x) ↔
      0 < l₁ + 2 • c₁₁ ∧ 0 < l₂ + 2 • c₂₂ ∧ 0 < l₁ + l₂ + 4 • c₁₂ := by
  rw [forall_kernel_pos_iff_forall_hilbertBasis_pos,
    forall_hilbertBasis_quarticWeight_pos_iff]

end OrderedMonoid

section OrderedGroup

variable [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

private theorem exists_pos_of_nontrivial [Nontrivial Γ] : ∃ ε : Γ, 0 < ε := by
  obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
  rcases ha.lt_or_gt with h | h
  · exact ⟨-a, neg_pos.mpr h⟩
  · exact ⟨a, h⟩

/-- `wick:prop:quarticH`, irredundancy: over a nonzero ordered group, none of the three
tests `w₁ = λ₁ + 2c₁₁ > 0`, `w₂ = λ₂ + 2c₂₂ > 0`, `w₄ = λ₁ + λ₂ + 4c₁₂ > 0` follows from the
other two: for each test there is data `(λ₁, λ₂; c₁₁, c₁₂, c₂₂)` satisfying the other two and
violating it. As in the source, the witnesses have `c₁₁ = c₂₂ = 0`. -/
theorem quartic_tests_irredundant [Nontrivial Γ] :
    (∃ l₁ l₂ c₁₁ c₁₂ c₂₂ : Γ,
      ¬ 0 < l₁ + 2 • c₁₁ ∧ 0 < l₂ + 2 • c₂₂ ∧ 0 < l₁ + l₂ + 4 • c₁₂) ∧
    (∃ l₁ l₂ c₁₁ c₁₂ c₂₂ : Γ,
      0 < l₁ + 2 • c₁₁ ∧ ¬ 0 < l₂ + 2 • c₂₂ ∧ 0 < l₁ + l₂ + 4 • c₁₂) ∧
    (∃ l₁ l₂ c₁₁ c₁₂ c₂₂ : Γ,
      0 < l₁ + 2 • c₁₁ ∧ 0 < l₂ + 2 • c₂₂ ∧ ¬ 0 < l₁ + l₂ + 4 • c₁₂) := by
  obtain ⟨ε, hε⟩ := exists_pos_of_nontrivial (Γ := Γ)
  have h4 : 0 < 4 • ε := (nsmul_pos_iff (by norm_num)).mpr hε
  refine ⟨⟨-ε, ε, 0, ε, 0, ?_, ?_, ?_⟩, ⟨ε, -ε, 0, ε, 0, ?_, ?_, ?_⟩,
    ⟨ε, ε, 0, -ε, 0, ?_, ?_, ?_⟩⟩
  · simpa using hε.le
  · simpa using hε
  · simpa using h4
  · simpa using hε
  · simpa using hε.le
  · simpa using h4
  · simpa using hε
  · simpa using hε
  · have h2 : 0 < 2 • ε := (nsmul_pos_iff two_ne_zero).mpr hε
    have e : ε + ε + 4 • -ε = -(2 • ε) := by abel
    rw [e, not_lt, neg_nonpos]
    exact h2.le

variable (ε : Γ)

omit [LinearOrder Γ] [IsOrderedAddMonoid Γ] in
/-- `wick:eq:mixedmodel`, weights: for `λ₁ = λ₂ = -ε`, `c₁₁ = c₂₂ = 2ε`, `c₁₂ = 0` the weights
of `h₁, h₂, h₃, h₄` are `3ε, 3ε, 2ε, -2ε`. -/
theorem mixedModel_weights :
    quarticWeight (-ε) (-ε) (2 • ε) 0 (2 • ε) quarticH₁ = 3 • ε ∧
      quarticWeight (-ε) (-ε) (2 • ε) 0 (2 • ε) quarticH₂ = 3 • ε ∧
      quarticWeight (-ε) (-ε) (2 • ε) 0 (2 • ε) quarticH₃ = 2 • ε ∧
      quarticWeight (-ε) (-ε) (2 • ε) 0 (2 • ε) quarticH₄ = -(2 • ε) := by
  rw [quarticWeight_quarticH₁, quarticWeight_quarticH₂, quarticWeight_quarticH₃,
    quarticWeight_quarticH₄]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

/-- `wick:eq:mixedmodel`: for `ε > 0`, `h₄` is the only Hilbert basis element of nonpositive
weight, so it is the obstruction, while `w₁, w₂, w₃ > 0`. -/
theorem mixedModel_obstruction {ε : Γ} (hε : 0 < ε) :
    ∀ h ∈ hilbertBasis quarticIncidence,
      (quarticWeight (-ε) (-ε) (2 • ε) 0 (2 • ε) h ≤ 0 ↔ h = quarticH₄) := by
  obtain ⟨w1, w2, w3, w4⟩ := mixedModel_weights ε
  have h2 : 0 < 2 • ε := (nsmul_pos_iff two_ne_zero).mpr hε
  have h3 : 0 < 3 • ε := (nsmul_pos_iff (by norm_num)).mpr hε
  have n1 : quarticH₁ ≠ quarticH₄ := fun e => by simpa [quarticH₁, quarticH₄] using congrFun e 1
  have n2 : quarticH₂ ≠ quarticH₄ := fun e => by simpa [quarticH₂, quarticH₄] using congrFun e 0
  have n3 : quarticH₃ ≠ quarticH₄ := fun e => by simpa [quarticH₃, quarticH₄] using congrFun e 2
  rw [hilbertBasis_quarticIncidence]
  rintro h (rfl | rfl | rfl | rfl)
  · simp only [w1, n1, iff_false, not_le]; exact h3
  · simp only [w2, n2, iff_false, not_le]; exact h3
  · simp only [w3, n3, iff_false, not_le]; exact h2
  · simp only [w4, iff_true, neg_nonpos]; exact h2.le

/-- `wick:eq:mixedmodel`: for `ε > 0` the Hilbert-basis criterion fails for the mixed model. -/
theorem mixedModel_not_criterion {ε : Γ} (hε : 0 < ε) :
    ¬ ∀ h ∈ hilbertBasis quarticIncidence, 0 < quarticWeight (-ε) (-ε) (2 • ε) 0 (2 • ε) h := by
  intro H
  have hmem : quarticH₄ ∈ hilbertBasis quarticIncidence := by
    rw [hilbertBasis_quarticIncidence]; simp
  exact (H _ hmem).not_ge ((mixedModel_obstruction hε _ hmem).mpr rfl)

/-- `wick:eq:mixedmodel`, valuations: in `R((t^Γ))`, with `t` the monomial `single ε 1` of
valuation `ε` (the source takes `ε = 1`), the entries `g₁ = g₂ = t⁻¹`, `C₁₁ = C₂₂ = t²` and
`C₁₂ = 1` are nonzero, with valuations `-ε`, `2ε` and `0`. -/
theorem mixedModel_valuations {R : Type*} [Field R] :
    let t : HahnSeries Γ R := HahnSeries.single ε 1
    t⁻¹ ≠ 0 ∧ t ^ 2 ≠ 0 ∧ (1 : HahnSeries Γ R) ≠ 0 ∧
      t⁻¹.order = -ε ∧ (t ^ 2).order = 2 • ε ∧ (1 : HahnSeries Γ R).order = 0 := by
  intro t
  have ht : t ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  refine ⟨inv_ne_zero ht, pow_ne_zero 2 ht, one_ne_zero, ?_, ?_, HahnSeries.order_one⟩
  · simp [t]
  · simp [t]

/-- `wick:eq:mixedmodel`: for `C = [[t², 1], [1, t²]]` and `g₁ = g₂ = t⁻¹` in `ℂ((t^ℚ))`,
the weights computed from the valuations are `w₁ = w₂ = 3`, `w₃ = 2` and `w₄ = -2`, and `h₄` is
the only Hilbert basis element of nonpositive weight. -/
theorem mixedModel_weights_rat :
    let t : HahnSeries ℚ ℂ := HahnSeries.single 1 1
    let w := quarticWeight t⁻¹.order t⁻¹.order (t ^ 2).order (1 : HahnSeries ℚ ℂ).order
      (t ^ 2).order
    (w quarticH₁ = 3 ∧ w quarticH₂ = 3 ∧ w quarticH₃ = 2 ∧ w quarticH₄ = -2) ∧
      ∀ h ∈ hilbertBasis quarticIncidence, (w h ≤ 0 ↔ h = quarticH₄) := by
  intro t w
  obtain ⟨-, -, -, hg, hC, h1⟩ := mixedModel_valuations (R := ℂ) (1 : ℚ)
  have hw : w = quarticWeight (-1) (-1) (2 • 1) 0 (2 • 1) := by
    simp only [w, t, hg, hC, h1]
  obtain ⟨w1, w2, w3, w4⟩ := mixedModel_weights (1 : ℚ)
  refine ⟨?_, ?_⟩
  · rw [hw, w1, w2, w3, w4]
    norm_num
  · rw [hw]
    exact mixedModel_obstruction one_pos

end OrderedGroup

end Weights

end Surreal.Wick
