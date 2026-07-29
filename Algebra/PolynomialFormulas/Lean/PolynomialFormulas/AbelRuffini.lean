import Archive.Wiedijk100Theorems.AbelRuffini

/-!
# The Abel--Ruffini obstruction

Mathlib's `solvableByRad ℚ ℂ` is the smallest intermediate field containing
the rationals and closed under taking nonzero-order roots.  Thus membership in
this field is the semantic meaning of "obtainable from rational constants by
field operations and radicals".

This file also gives a small, explicitly typed syntax for such expressions.
Its `nthRoot` constructor records both the chosen root and its root equation.
The equivalence `RadicalExpression.nonempty_iff_mem_solvableByRad` identifies
this syntax exactly with mathlib's semantic closure.

The concrete quintic `X ^ 5 - 4 * X + 2` has symmetric Galois group and hence
no complex root in that closure.  Padding it with a power of `X` gives, for
every `n ≥ 5`, a degree-`n` polynomial with a root that has no radical
expression.  Consequently there cannot be a universal complete radical
solver in any degree at least five.
-/

namespace LeanProofs.PolynomialFormulas

open Polynomial

/-! ## Radical expressions and their semantic interpretation -/

/-- A typed syntax for complex numbers built from rational constants, field
operations, and chosen radicals.  The index is the value represented by the
expression.  In the `nthRoot` case, `value` is a chosen `n`th root of the
represented radicand, and `hvalue` records its defining equation. -/
inductive RadicalExpression : ℂ → Type
  | rational (q : ℚ) : RadicalExpression (algebraMap ℚ ℂ q)
  | add {x y : ℂ} : RadicalExpression x → RadicalExpression y → RadicalExpression (x + y)
  | sub {x y : ℂ} : RadicalExpression x → RadicalExpression y → RadicalExpression (x - y)
  | mul {x y : ℂ} : RadicalExpression x → RadicalExpression y → RadicalExpression (x * y)
  | inv {x : ℂ} : RadicalExpression x → RadicalExpression x⁻¹
  | nthRoot {radicand : ℂ} (n : ℕ) (hn : n ≠ 0) (value : ℂ)
      (hvalue : value ^ n = radicand) :
      RadicalExpression radicand → RadicalExpression value

namespace RadicalExpression

/-- Evaluate a typed radical expression.  The syntax index already records
the value, so evaluation is projection of that index. -/
def eval {z : ℂ} (_ : RadicalExpression z) : ℂ := z

@[simp]
theorem eval_eq {z : ℂ} (e : RadicalExpression z) : e.eval = z := rfl

/-- Every explicitly represented radical expression belongs to mathlib's
semantic field of elements solvable by radicals. -/
theorem eval_mem_solvableByRad {z : ℂ} (e : RadicalExpression z) :
    e.eval ∈ solvableByRad ℚ ℂ := by
  change z ∈ solvableByRad ℚ ℂ
  induction e with
  | rational q => exact IntermediateField.algebraMap_mem _ q
  | add _ _ hx hy => exact add_mem hx hy
  | sub _ _ hx hy => exact sub_mem hx hy
  | mul _ _ hx hy => exact mul_mem hx hy
  | inv _ hx => exact inv_mem hx
  | nthRoot n hn value hvalue _ hx =>
      apply solvableByRad.rad_mem hn
      rw [hvalue]
      exact hx

/-- A complex number has a radical expression exactly when it belongs to
mathlib's semantic field of elements solvable by radicals.  The reverse
direction follows the induction principle for the smallest radical-closed
field, translating each of its generators into the corresponding expression
constructor. -/
theorem nonempty_iff_mem_solvableByRad {z : ℂ} :
    Nonempty (RadicalExpression z) ↔ z ∈ solvableByRad ℚ ℂ := by
  constructor
  · rintro ⟨e⟩
    exact e.eval_mem_solvableByRad
  · intro hz
    induction hz using solvableByRad.induction with
    | mem q => exact ⟨.rational q⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨ex⟩ := ihx
        obtain ⟨ey⟩ := ihy
        exact ⟨.add ex ey⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨ex⟩ := ihx
        obtain ⟨ey⟩ := ihy
        exact ⟨.mul ex ey⟩
    | rad n x hn hx ih =>
        obtain ⟨exn⟩ := ih
        exact ⟨.nthRoot n hn x rfl exn⟩

end RadicalExpression

/-- Semantic complete solvability: every complex root of `p` belongs to the
field generated from `ℚ` by algebraic operations and radicals. -/
def CompletelySolvableByRadicals (p : ℚ[X]) : Prop :=
  ∀ x : p.rootSet ℂ, (x : ℂ) ∈ solvableByRad ℚ ℂ

/-- An explicit complete radical representation supplies, for every complex
root, a radical expression whose index is that root.

This is deliberately a nonuniform overapproximation of a single symbolic
formula: it may choose a separate expression for each root and each input
polynomial.  Proving that even this permissive notion fails is therefore
stronger than merely ruling out one fixed coefficient-parametrized formula. -/
def HasCompleteRadicalSolution (p : ℚ[X]) : Prop :=
  ∀ x : p.rootSet ℂ, Nonempty (RadicalExpression (x : ℂ))

/-- Explicit radical expressions are sound for the semantic closure. -/
theorem hasCompleteRadicalSolution_sound {p : ℚ[X]}
    (h : HasCompleteRadicalSolution p) : CompletelySolvableByRadicals p := by
  intro x
  obtain ⟨e⟩ := h x
  exact e.eval_mem_solvableByRad

/-- The explicit, per-root expression notion is equivalent to semantic
complete solvability.  This remains a deliberately nonuniform notion: the
existential expression may depend on both the polynomial and the chosen root,
so this theorem does not assert the existence of one coefficient-parametrized
symbolic formula. -/
theorem hasCompleteRadicalSolution_iff {p : ℚ[X]} :
    HasCompleteRadicalSolution p ↔ CompletelySolvableByRadicals p := by
  constructor
  · exact hasCompleteRadicalSolution_sound
  · intro h x
    exact RadicalExpression.nonempty_iff_mem_solvableByRad.mpr (h x)

/-! ## A concrete unsolvable quintic -/

/-- The explicit Abel--Ruffini quintic `X ^ 5 - 4 * X + 2`. -/
noncomputable def abelRuffiniQuintic : ℚ[X] :=
  AbelRuffini.Φ ℚ 4 2

theorem abelRuffiniQuintic_monic : abelRuffiniQuintic.Monic := by
  simpa [abelRuffiniQuintic] using (AbelRuffini.monic_Phi (R := ℚ) 4 2)

theorem abelRuffiniQuintic_natDegree : abelRuffiniQuintic.natDegree = 5 := by
  simpa [abelRuffiniQuintic] using (AbelRuffini.natDegree_Phi (R := ℚ) 4 2)

theorem abelRuffiniQuintic_irreducible : Irreducible abelRuffiniQuintic := by
  simpa [abelRuffiniQuintic] using
    (AbelRuffini.irreducible_Phi 4 2 2 (by decide) (by decide) (by decide) (by decide))

theorem abelRuffiniQuintic_complexRoots_card :
    Fintype.card (abelRuffiniQuintic.rootSet ℂ) = 5 := by
  simpa [abelRuffiniQuintic] using
    (AbelRuffini.complex_roots_Phi 4 2 abelRuffiniQuintic_irreducible.separable)

/-- Every complex root of the explicit quintic fails to be solvable by
radicals. -/
theorem abelRuffiniQuintic_root_not_solvableByRad {x : ℂ}
    (hx : x ∈ abelRuffiniQuintic.rootSet ℂ) :
    x ∉ solvableByRad ℚ ℂ := by
  apply AbelRuffini.not_solvable_by_rad' x
  exact aeval_eq_zero_of_mem_rootSet hx

/-- The explicit quintic has at least one complex root, and that root is not
solvable by radicals. -/
theorem exists_abelRuffiniQuintic_root_not_solvableByRad :
    ∃ x : abelRuffiniQuintic.rootSet ℂ,
      (x : ℂ) ∉ solvableByRad ℚ ℂ := by
  have hcard : 0 < Fintype.card (abelRuffiniQuintic.rootSet ℂ) := by
    rw [abelRuffiniQuintic_complexRoots_card]
    decide
  let x : abelRuffiniQuintic.rootSet ℂ :=
    Classical.choice (Fintype.card_pos_iff.mp hcard)
  exact ⟨x, abelRuffiniQuintic_root_not_solvableByRad x.property⟩

theorem abelRuffiniQuintic_not_completelySolvableByRadicals :
    ¬ CompletelySolvableByRadicals abelRuffiniQuintic := by
  intro h
  obtain ⟨x, hx⟩ := exists_abelRuffiniQuintic_root_not_solvableByRad
  exact hx (h x)

theorem abelRuffiniQuintic_hasNoCompleteRadicalSolution :
    ¬ HasCompleteRadicalSolution abelRuffiniQuintic :=
  fun h => abelRuffiniQuintic_not_completelySolvableByRadicals
    (hasCompleteRadicalSolution_sound h)

/-! ## Counterexamples in every degree at least five -/

/-!
The padded polynomial is a counterexample to a *complete* solver, because it
retains a quintic root that is not expressible by radicals.  The result does
not say that every polynomial of degree greater than four is unsolvable: many
such polynomials split or otherwise have solvable Galois group.
-/

/-- Pad the unsolvable quintic by zero roots to obtain any requested degree. -/
noncomputable def paddedAbelRuffiniPolynomial (n : ℕ) : ℚ[X] :=
  abelRuffiniQuintic * X ^ (n - 5)

theorem paddedAbelRuffiniPolynomial_monic (n : ℕ) :
    (paddedAbelRuffiniPolynomial n).Monic := by
  exact abelRuffiniQuintic_monic.mul (monic_X.pow (n - 5))

theorem paddedAbelRuffiniPolynomial_natDegree {n : ℕ} (hn : 5 ≤ n) :
    (paddedAbelRuffiniPolynomial n).natDegree = n := by
  rw [paddedAbelRuffiniPolynomial,
    abelRuffiniQuintic_monic.natDegree_mul (monic_X.pow (n - 5)),
    abelRuffiniQuintic_natDegree, natDegree_X_pow, Nat.add_sub_of_le hn]

/-- Every root of the quintic remains a root after degree padding. -/
theorem abelRuffiniQuintic_root_mem_padded (n : ℕ)
    (x : abelRuffiniQuintic.rootSet ℂ) :
    (x : ℂ) ∈ (paddedAbelRuffiniPolynomial n).rootSet ℂ := by
  rw [mem_rootSet_of_ne (paddedAbelRuffiniPolynomial_monic n).ne_zero]
  simp [paddedAbelRuffiniPolynomial, aeval_eq_zero_of_mem_rootSet x.property]

theorem paddedAbelRuffiniPolynomial_not_completelySolvableByRadicals (n : ℕ) :
    ¬ CompletelySolvableByRadicals (paddedAbelRuffiniPolynomial n) := by
  intro h
  obtain ⟨x, hx⟩ := exists_abelRuffiniQuintic_root_not_solvableByRad
  exact hx (h ⟨x, abelRuffiniQuintic_root_mem_padded n x⟩)

theorem paddedAbelRuffiniPolynomial_hasNoCompleteRadicalSolution (n : ℕ) :
    ¬ HasCompleteRadicalSolution (paddedAbelRuffiniPolynomial n) :=
  fun h => paddedAbelRuffiniPolynomial_not_completelySolvableByRadicals n
    (hasCompleteRadicalSolution_sound h)

/-- For every `n ≥ 5`, there is a monic degree-`n` rational polynomial that
is not completely solvable by radicals. -/
theorem exists_incomplete_radical_polynomial_of_degree {n : ℕ} (hn : 5 ≤ n) :
    ∃ p : ℚ[X], p.Monic ∧ p.natDegree = n ∧ ¬ CompletelySolvableByRadicals p := by
  exact ⟨paddedAbelRuffiniPolynomial n, paddedAbelRuffiniPolynomial_monic n,
    paddedAbelRuffiniPolynomial_natDegree hn,
    paddedAbelRuffiniPolynomial_not_completelySolvableByRadicals n⟩

/-- No degree `n ≥ 5` admits complete radical expressions for every root even
when inputs are restricted to monic rational polynomials.  This directly
refutes a universal formula made from rational constants, field operations,
and radicals. -/
theorem no_universal_complete_radical_solution {n : ℕ} (hn : 5 ≤ n) :
    ¬ ∀ p : ℚ[X], p.Monic → p.natDegree = n → HasCompleteRadicalSolution p := by
  intro h
  exact paddedAbelRuffiniPolynomial_hasNoCompleteRadicalSolution n
    (h (paddedAbelRuffiniPolynomial n) (paddedAbelRuffiniPolynomial_monic n)
      (paddedAbelRuffiniPolynomial_natDegree hn))

/-- Abel--Ruffini in the usual `degree > 4` wording: there is no universal
complete formula, built from field operations and radicals, for all roots of
all rational polynomials of that degree. -/
theorem no_universal_radical_formula_of_degree_gt_four {n : ℕ} (hn : 4 < n) :
    ¬ ∀ p : ℚ[X], p.Monic → p.natDegree = n → HasCompleteRadicalSolution p :=
  no_universal_complete_radical_solution (Nat.succ_le_iff.mpr hn)

/-- Semantic version of the universal Abel--Ruffini obstruction, again already
for the restricted class of monic inputs. -/
theorem no_universal_complete_solvability_by_radicals {n : ℕ} (hn : 5 ≤ n) :
    ¬ ∀ p : ℚ[X], p.Monic → p.natDegree = n → CompletelySolvableByRadicals p := by
  intro h
  exact paddedAbelRuffiniPolynomial_not_completelySolvableByRadicals n
    (h (paddedAbelRuffiniPolynomial n) (paddedAbelRuffiniPolynomial_monic n)
      (paddedAbelRuffiniPolynomial_natDegree hn))

end LeanProofs.PolynomialFormulas
