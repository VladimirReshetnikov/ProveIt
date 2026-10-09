import GowersSzemeredi.Proofs07BohrHom
import GowersSzemeredi.Proofs16BohrAnnulus

/-! Directional difference sets and row Bogolyubov: step 1 of the bilinear
Bogolyubov argument.

Milićević (arXiv:2601.01682, Theorem 1.6; proof in arXiv:2109.03093) builds
bilinear Bohr varieties inside iterated directional difference sets
`D_hor D_ver D_ver D_hor D_ver D_hor D_hor A`. Here
* `horDiff A = {(x₁ − x₂, y) : (x₁, y), (x₂, y) ∈ A}` and
* `verDiff A = {(x, y₁ − y₂) : (x, y₁), (x, y₂) ∈ A}`.

The first two operators act within rows. `D_hor D_hor A` has row
`(A_y − A_y) − (A_y − A_y) = 2A_y − 2A_y` (`mem_horDiff_horDiff`). So every
row of density `α_y > 0` contains a Bohr set `B(K_y; 1/(8π))` with
`|K_y| ≤ 16α_y⁻²`, by the classical Bogolyubov lemma `bogolyubov_classical`
(`row_bogolyubov`). The codimension here is polynomial in the reciprocal row density.
Research notes J.5 discuss a possible budget comparison; fitting the
remaining structure bounds into Theorem 16.2 is not yet proved. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- The horizontal difference set. -/
def horDiff {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => ∃ x₁ x₂, (x₁, p.2) ∈ A ∧ (x₂, p.2) ∈ A ∧ p.1 = x₁ - x₂

/-- The vertical difference set. -/
def verDiff {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => ∃ y₁ y₂, (p.1, y₁) ∈ A ∧ (p.1, y₂) ∈ A ∧ p.2 = y₁ - y₂

/-- The row of a set of pairs. -/
def rowOf {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (y : ZMod N) : Finset (ZMod N) :=
  Finset.univ.filter fun x => (x, y) ∈ A

/-- Rows of `D_hor D_hor A` contain `2A_y − 2A_y`. -/
theorem mem_horDiff_horDiff {N : Nat} [NeZero N] {A : Finset (ZMod N × ZMod N)} {y : ZMod N}
    {a e b c : ZMod N} (ha : a ∈ rowOf A y) (he : e ∈ rowOf A y) (hb : b ∈ rowOf A y)
    (hc : c ∈ rowOf A y) : (a + e - b - c, y) ∈ horDiff (horDiff A) := by
  unfold rowOf at ha he hb hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha he hb hc
  unfold horDiff
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, a - b, c - e, ?_, ?_, by ring⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, b, ha, hb, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, e, hc, he, rfl⟩

/-- **Row Bogolyubov.** Every row of positive density `α_y` of `D_hor D_hor A`
contains a Bohr set of codimension at most `16α_y⁻²` and radius `1/(8π)`. -/
theorem row_bogolyubov {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N)) (y : ZMod N)
    (hrow : (rowOf A y).Nonempty) :
    ∃ K : Finset (ZMod N),
      (K.card : Real) ≤ 16 * (((rowOf A y).card : Real) / N) ^ (-(2 : Real)) ∧
      ∀ d ∈ bohr K (1 / (8 * Real.pi)), (d, y) ∈ horDiff (horDiff A) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  set α := ((rowOf A y).card : Real) / N with hαdef
  have hα : 0 < α := div_pos (by exact_mod_cast hrow.card_pos) hNR
  have hcard : ((rowOf A y).card : Real) = α * N := by rw [hαdef]; field_simp
  obtain ⟨hK, hB⟩ := bogolyubov_classical (rowOf A y) α hα hcard
  refine ⟨section7Spectrum (rowOf A y) α, hK, fun d hd => ?_⟩
  obtain ⟨a, ha, e, he, b, hb, c, hc, rfl⟩ := hB d hd
  exact mem_horDiff_horDiff ha he hb hc

/-- Vertical differences of two points in the same column. -/
theorem mem_verDiff {N : Nat} [NeZero N] {A : Finset (ZMod N × ZMod N)} {d y₁ y₂ : ZMod N}
    (h₁ : (d, y₁) ∈ A) (h₂ : (d, y₂) ∈ A) : (d, y₁ - y₂) ∈ verDiff A := by
  unfold verDiff
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y₁, y₂, h₁, h₂, rfl⟩

/-- **Step 2 of [49] Theorem 35.** The fibre of `D_ver D_hor D_hor A` over `y`
contains `B(K_{y+z}; 1/(8π)) ∩ B(K_z; 1/(8π))` for every pair of nonempty
rows `y + z`, `z`, with `K` the row spectra of `row_bogolyubov`. -/
theorem verDiff_rowBohr_intersection {N : Nat} [NeZero N] (A : Finset (ZMod N × ZMod N))
    (y z : ZMod N) (h₁ : (rowOf A (y + z)).Nonempty) (h₂ : (rowOf A z).Nonempty) :
    ∃ K₁ K₂ : Finset (ZMod N),
      (K₁.card : Real) ≤ 16 * (((rowOf A (y + z)).card : Real) / N) ^ (-(2 : Real)) ∧
      (K₂.card : Real) ≤ 16 * (((rowOf A z).card : Real) / N) ^ (-(2 : Real)) ∧
      ∀ d ∈ bohr K₁ (1 / (8 * Real.pi)), d ∈ bohr K₂ (1 / (8 * Real.pi)) →
        (d, y) ∈ verDiff (horDiff (horDiff A)) := by
  obtain ⟨K₁, hK₁, hB₁⟩ := row_bogolyubov A (y + z) h₁
  obtain ⟨K₂, hK₂, hB₂⟩ := row_bogolyubov A z h₂
  refine ⟨K₁, K₂, hK₁, hK₂, fun d hd₁ hd₂ => ?_⟩
  have := mem_verDiff (hB₁ d hd₁) (hB₂ d hd₂)
  simpa using this

end LeanProofs.GowersSzemeredi
