import New.Spanning.Unfolding.Climbing
import New.UpperBound.Seesaw.AdmissibleCombinations

/-!
# Congruence levels inside the stabilizer of a glued lattice

A grading `Y` of a hermitian space `V` (a choice of basis vectors with a fixed Gram matrix) embeds
the finite adelic unitary group on `X ⊕ Unit` into that of `V`. When the lattice of `V` is the glued
lattice of `Y`, this file gives congruences on an element of the small group that put its image
into the stabilizer of the lattice, or into a congruence level of it.

Notions from other files:
* `Grading V N (X ⊕ Unit) s` splits the index set `ι` of the basis of `V` into `X ⊕ Unit`, on
  which the Gram matrix is `1`, and a string of `s` vectors, orthogonal to it and with a fixed Gram
  matrix that depends on `N`; `Y.inclXFin` is the resulting map on finite adelic unitary groups.
* The glued lattice of `Y` is the `Ô`-span of the columns of
  `gradedLatticeBasis Y.indexEquiv a π u`. For odd `s` it glues the last vector of `X ⊕ Unit` to
  the middle vector of the string.
* `Y.SpansLattice a π u`: the frame `V.xFin` of `V` spans the glued lattice. So in coordinates of
  this frame the glued lattice is the standard lattice `Ô^ι`.
* `IsSplitSquarefree P N π`: `N = π π̄`, the idele `π` is a uniformizer at the places in `P` and a
  unit elsewhere, and `P` contains no place together with its conjugate.
* `congruenceGL M e`: the integral invertible matrices whose rows `e i` agree with those of `1`
  modulo `M`.
* `stdLevel E ι` is the stabilizer of `Ô^ι` in the finite adelic unitary group `Gf E ι`, and
  `levelOf w ⊥` is the subgroup of its elements congruent to `1` at every place `w i`.

## Relation to the literature

Related work: `Grading.inclXFin_mem_stdLevel` is related to Nikulin's criterion for extending
isometries to an overlattice: the congruence on `h` plays the part of the condition that an isometry
preserve the gluing.
-/

namespace New

open Filling Matrix Seesaw Space
variable {E X ι : Type _} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X]
  [DecidableEq X] {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} (Y : Grading V N (X ⊕ Unit) s)
  {a π : (𝔸f E)ˣ}

/-- Let the grading `Y` split the index set `ι` of a basis of the hermitian space `V` over `E` into
`X ⊕ Unit` and a string of `s` vectors with a fixed Gram matrix depending on `N`. It gives the map
`Y.inclXFin` from the finite adelic unitary group `Gf E (X ⊕ Unit)` to `Gf E ι`, that of `V` in the
coordinates of its frame `V.xFin`. Assume that this frame spans the glued lattice of `Y`, that is,
the `Ô`-span of the basis `gradedLatticeBasis Y.indexEquiv a π u`, with ideles `a`, `π` and a
unitary adele `u` as parameters (`SpansLattice`).

Then there is an integral matrix `R` such that the image of every `h` is the matrix `1 + Rᴴ M R`.
Here `M = h - 1` if `s` is even; if `s` is odd, the last row (index `Sum.inr ()`) of `h - 1` is
divided by `π` and its last column by `star π` (`scaleAt p o` is the diagonal matrix with `p` at
`o` and `1` elsewhere). -/
lemma Grading.exists_inclXFin_sub_one_eq {u : unitary (𝔸f E)} (hL : Y.SpansLattice a π u) :
    ∃ R : Matrix (X ⊕ Unit) ι (𝔸f E), IsIntMatrix (Ô E) R ∧ ∀ h : Gf E (X ⊕ Unit),
      (Y.inclXFin h).val.val - 1 = Rᴴ * ((if Odd s then
        scaleAt π⁻¹.val (Sum.inr ()) * ((h.val.val - 1) * scaleAt (star π⁻¹.val) (Sum.inr ()))
        else h.val.val - 1) * R) := by
  -- In rational coordinates the element acts as `h` on `X ⊕ Unit` and as `1` on the string, so its
  -- matrix is `1 + Aᴴ (h - 1) A`, with `A` the rows of `V.xFin = gradedLatticeBasis · k` indexed by
  -- `X ⊕ Unit`. These are the rows `R` of `k`, the last divided by `star π` when `s` is odd.
  obtain ⟨k, hk, xFin_eq⟩ := hL
  set e : (X ⊕ Unit) ⊕ Fin s ≃ ι := Y.indexEquiv with he
  set R : Matrix (X ⊕ Unit) ι (𝔸f E) := of fun x ↦ k.val (e (Sum.inl x)) with hR
  refine ⟨R, fun x ↦ hk.isIntMatrix _, fun h ↦ ?_⟩
  have h_conj : (Y.inclXFin h).val.val - 1 =
      V.xFin⁻¹ * (V.ratCoordMatrixFin (Y.inclXFin h) - 1) * V.xFin := by
    simp [ratCoordMatrixFin, sub_mul, mul_sub, mul_assoc]
  set D : Matrix (X ⊕ Unit) (X ⊕ Unit) (𝔸f E) :=
    if Odd s then scaleAt (star π⁻¹.val) (Sum.inr ()) else 1 with hD
  -- The Gram matrix times `(h ⊕ 1) - 1` lives on the block `X ⊕ Unit`, where it is `h - 1`.
  have h_block : V.J.map (↑) * (gradedBlocks e e h.val.val 1 - 1) =
      reindex e e (fromBlocks (h.val.val - 1) 0 0 0) := by
    ext i j
    obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := e.surjective i, e.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Y.gram_eq, ← he, gradedGram, gradedBlocks, mul_apply, (reindex_equiv e).2,
        Matrix.one_apply, mul_sub]
  -- The rows of `V.xFin` in that block are those of `R`, the last divided by `star π` for odd `s`.
  have h_rows : V.xFin.val.submatrix (e ∘ Sum.inl) id = D * R := by
    ext (x | x) j <;> by_cases hs : Odd s <;>
      simp [xFin_eq, hD, hR, hs, mul_apply, gradedLatticeBasis, diagonal, (reindex_equiv e).2]
  have h_restrict (A : Matrix (X ⊕ Unit) (X ⊕ Unit) (𝔸f E)) :
      V.xFin.valᴴ * reindex e e (fromBlocks A 0 0 0) * V.xFin.val = (D * R)ᴴ * A * (D * R) := by
    rw [← h_rows]
    ext i j
    simp [mul_apply, (reindex_equiv e).2]
  rw [h_conj, Units.inv_eq_of_mul_eq_one_left gram_xFin, Y.ratCoordMatrixFin_inclXFin,
    Matrix.mul_assoc _ (V.J.map _), h_block, h_restrict, hD]
  split <;> simp [conjTranspose_mul, Matrix.mul_assoc, Pi.star_def, apply_ite star]

/-- Suppose that the frame `V.xFin` of `V` spans the glued lattice, the `Ô`-span of the explicit
basis `gradedLatticeBasis Y.indexEquiv a π u` (`SpansLattice`). Suppose also that `N = π π̄` and
that the idele `π` is a uniformizer at the places of `P`, a set without conjugate pairs, and a unit
elsewhere (`IsSplitSquarefree`).

If a unitary `h` on `X ⊕ Unit` is integral and its last row (index `Sum.inr ()`) is that of `1`
modulo `π` (`congruenceGL`), then its image `Y.inclXFin h` in `Gf E ι` stabilizes the glued lattice:
in the coordinates of `V.xFin` this is `Ô^ι`, with stabilizer `stdLevel E ι`. -/
lemma Grading.inclXFin_mem_stdLevel {P : Finset (FinPlace E)} {u : unitary (𝔸f E)}
    {h : Gf E (X ⊕ Unit)} (hL : Y.SpansLattice a π u) (hπ : IsSplitSquarefree P N π)
    (h_cong : h.val ∈ congruenceGL (Ô E ∙ π.val) Sum.inr) :
    Y.inclXFin h ∈ stdLevel E ι := by
  obtain ⟨R, R_int, h_eq⟩ := Y.exists_inclXFin_sub_one_eq hL
  rw [mem_stdLevel, sub_eq_iff_eq_add.mp (h_eq h)]
  suffices M_int : IsIntMatrix (Ô E) (if Odd s then
      scaleAt π⁻¹.val (Sum.inr ()) * ((h.val.val - 1) * scaleAt (star π⁻¹.val) (Sum.inr ()))
      else h.val.val - 1) from
    (R_int.conjTranspose.mul (M_int.mul R_int)).add .one
  -- At every place `π` or its conjugate is a unit.
  have h_unit (w : FinPlace E) : Valued.v (π.val w) = 1 ∨ Valued.v (π.val (star w)) = 1 := by
    by_cases hw : w ∈ P <;> simp [hπ.v_apply, hw, hπ.star_notMem w]
  -- For odd `s`, as `h` is unitary, the congruence on its last row absorbs both divisions.
  split
  · exact isIntMatrix_scaleAt_mul_sub_one_mul_scaleAt π (Sum.inr ()) h_unit h_cong
  · exact h_cong.1.isIntMatrix.sub .one

omit [CMType E] in
/-- An element of the finite adelic unitary group lies in `levelOf w ⊥`, the integral elements whose
reduction modulo every place `w i` is trivial, if and only if it is integral (`stdLevel`) and each
entry of its matrix minus `1` has valuation less than `1` in the completion at each `w i` (taken by
`evalAt`). -/
lemma mem_levelOf_bot [NumberField E] [NumberField.IsCMField E] {I : Type} {w : I → FinPlace E}
    {g : Gf E ι} :
    g ∈ levelOf w ⊥ ↔ g ∈ stdLevel E ι ∧
      ∀ (i : I) (b c : ι), Valued.v (evalAt (w i) ((g.val.val - 1) b c)) < 1 := by
  simp only [mem_levelOf, ← exists_prop, Subgroup.mem_bot, funext_iff]
  exact exists_congr fun hg ↦ forall_congr' fun i ↦
    (stdLevel.map_eq_one ι).trans (forall₂_congr fun b c ↦ reduceAt_eq_zero)

/-- Suppose that the frame `V.xFin` of `V` spans the glued lattice, the `Ô`-span of the explicit
basis `gradedLatticeBasis Y.indexEquiv a π u` (`SpansLattice`), that `N = π π̄` with `π` a
uniformizer at the places of `P` and a unit elsewhere, `P` being without conjugate pairs
(`IsSplitSquarefree`), and that the places `w i` and their conjugates lie outside `P`.

If a unitary `h` on `X ⊕ Unit` is integral, its last row (index `Sum.inr ()`) is that of `1` modulo
`π` (`congruenceGL`) and it is congruent to `1` at every `w i`, then so is its image `Y.inclXFin h`
in the coordinates of `V.xFin`: it is integral and congruent to `1` at every `w i`. -/
lemma Grading.inclXFin_mem_levelOf {P : Finset (FinPlace E)} {u : unitary (𝔸f E)}
    {h : Gf E (X ⊕ Unit)} {I : Type} {w : I → FinPlace E} (hL : Y.SpansLattice a π u)
    (hπ : IsSplitSquarefree P N π) (h_cong : h.val ∈ congruenceGL (Ô E ∙ π.val) Sum.inr)
    (hw : ∀ i : I, w i ∉ P) (hw_star : ∀ i : I, star (w i) ∉ P) (h_level : h ∈ levelOf w ⊥) :
    Y.inclXFin h ∈ levelOf w ⊥ := by
  obtain ⟨R, R_int, h_eq⟩ := Y.exists_inclXFin_sub_one_eq hL
  refine mem_levelOf_bot.mpr ⟨Y.inclXFin_mem_stdLevel hL hπ h_cong, fun i b c ↦ ?_⟩
  obtain ⟨-, h_small⟩ := mem_levelOf_bot.mp h_level
  rw [h_eq h]
  set M : Matrix (X ⊕ Unit) (X ⊕ Unit) (𝔸f E) := if Odd s then
    scaleAt π⁻¹.val (Sum.inr ()) * ((h.val.val - 1) * scaleAt (star π⁻¹.val) (Sum.inr ()))
    else h.val.val - 1 with hM
  have M_small (x x' : X ⊕ Unit) : Valued.v (evalAt (w i) (M x x')) < 1 := by
    rw [hM]
    split
    · -- An entry is multiplied by some of `π⁻¹` and `star π⁻¹`, which are units at `w i`.
      simp only [scaleAt, diagonal_mul, mul_diagonal]
      split_ifs <;>
        simpa [idele_inv_apply_and_ne_zero, hπ.v_apply, hw, hw_star] using h_small i x x'
    · exact h_small i x x'
  -- Each entry of `Rᴴ M R` is a sum of products of an entry of `M` with two integral elements.
  simp only [mul_apply, Finset.mul_sum, map_sum, map_mul]
  refine Valued.v.map_sum_lt one_ne_zero fun x _ ↦ Valued.v.map_sum_lt one_ne_zero fun x' _ ↦ ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (mem_Ô.1 (R_int.conjTranspose b x) (w i))).trans_lt
    ((mul_le_of_le_one_right' (mem_Ô.1 (R_int x' c) (w i))).trans_lt (M_small x x'))

end New
