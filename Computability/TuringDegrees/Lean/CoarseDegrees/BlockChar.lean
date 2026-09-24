import CoarseDegrees.Cone
import CoarseDegrees.DyadicRoute

/-!
# Classes with a least degree are exactly the block-code classes

Synthesis, Theorem 3.6 (with Theorem 3.1 for the spectrum), now that `blockCode_decode` is
proved in `CoarseDegrees.Block` and the sparse-coding step is `CoarseDegrees.implant`:

```lean
theorem isLeastNC_iff_blockCode {X : Set ℕ} :
    (∃ g, IsLeastNC (χ X) g) ↔ ∃ B : Set ℕ, χ X ≡ₙ χ (blockCode B)
```

So the coarse classes that *do* have a representative of least Turing degree are exactly the
classes of block codes, and `C1` is the assertion that every function is coarsely equivalent to
a block code.  Combined with `CoarseDegrees.not_C1` this exhibits, for each of the three routes,
a function that is coarsely equivalent to no block code.

The file also records the attainment half of the spectrum identity: a set whose degree merely
*computes* a coarse description of `X` is the degree of an actual representative of `X`, by
implanting a copy of it on the markers.  That is what turns "some representative is complicated"
into a statement about the spectrum, and without it no leastness question could be refuted.

Everything in this file is proved.
-/

noncomputable section

open scoped Classical Computability
open TuringDegrees
open scoped SetTuring

namespace CoarseDegrees

/-! ## Attainment: the spectrum is upward closed -/

/-- **The sparse-coding step of the spectrum identity** (synthesis, Theorem 3.1).  If `B`
computes a coarse description of `X`, then `B` is the exact Turing degree of a coarse
description of `X`.  Hence the spectrum of a coarse class is upward closed and is determined by
which degrees compute a description. -/
theorem exists_description_of_degree {X B D : Set ℕ} (hD : SetCoarseEq D X) (hDB : D ≤ᵀₛ B) :
    ∃ Y : Set ℕ, SetCoarseEq Y X ∧ Y ≡ᵀₛ B :=
  ⟨implant D B, (implant_coarseEq D B).trans hD, implant_equivalent hDB⟩

/-! ## Block codes have least representatives -/

/-- Every representative of the coarse class of a block code computes the coded set. -/
theorem tRed_of_ncEquiv_blockCode {B : Set ℕ} {h : ℕ → ℕ} (hh : h ≡ₙ χ (blockCode B)) :
    χ (blockCode B) ≤ₜ h := by
  obtain ⟨E, hE, hEh⟩ := hh.exists_description
  obtain ⟨C, hC, hCE⟩ := exists_set_description hE
  have hB : χ B ≤ₜ χ C := tRed_chi_iff.mpr (blockCode_decode hC)
  exact ((tRed_chi_iff.mpr (blockCode_reducible B)).trans hB).trans (hCE.trans hEh)

/-- The block code is a representative of least Turing degree in its own coarse class. -/
theorem isLeastNC_blockCode (B : Set ℕ) :
    IsLeastNC (χ (blockCode B)) (χ (blockCode B)) :=
  ⟨(CoarseEq.refl _).ncEquiv, fun _ hh => tRed_of_ncEquiv_blockCode hh⟩

/-! ## The characterization -/

/-- **Least representatives are exactly the block-code classes** (synthesis, Theorem 3.6, the
equivalence of clauses (i) and (v)).  A coarse class has a representative of least Turing degree
exactly when it is the class of a block code; and then the least degree is that of the coded
set, which may be taken to be the graph of the least representative. -/
theorem isLeastNC_iff_blockCode {X : Set ℕ} :
    (∃ g, IsLeastNC (χ X) g) ↔ ∃ B : Set ℕ, χ X ≡ₙ χ (blockCode B) := by
  constructor
  · rintro ⟨g, hgX, hgleast⟩
    refine ⟨graph g, ?_, ?_⟩
    · -- every description of the block code computes `g`, which computes a description of `X`
      intro D hD
      obtain ⟨E, hE, hEg⟩ := hgX.exists_description
      obtain ⟨C, hC, hCD⟩ := exists_set_description hD
      have hB : χ (graph g) ≤ₜ χ C := tRed_chi_iff.mpr (blockCode_decode hC)
      exact ⟨E, hE, hEg.trans ((tRed_graph g).trans (hB.trans hCD))⟩
    · -- every description of `X` computes `g`, hence the block code of its graph
      intro D hD
      refine ⟨χ (blockCode (graph g)), CoarseEq.refl _, ?_⟩
      have h1 : χ (blockCode (graph g)) ≤ₜ χ (graph g) :=
        tRed_chi_iff.mpr (blockCode_reducible _)
      exact (h1.trans (graph_tRed g)).trans (hgleast D hD.ncEquiv)
  · rintro ⟨B, hB⟩
    refine ⟨χ (blockCode B), hB.symm, fun h hh => ?_⟩
    exact tRed_of_ncEquiv_blockCode (hh.trans hB)

/-- `C1` says exactly that every function is coarsely equivalent to a block code. -/
theorem C1_iff_blockCode_sets :
    (∀ X : Set ℕ, ∃ g, IsLeastNC (χ X) g) ↔ ∀ X : Set ℕ, ∃ B : Set ℕ, χ X ≡ₙ χ (blockCode B) :=
  forall_congr' fun _ => isLeastNC_iff_blockCode

/-- Consequently the counterexamples of `CoarseDegrees.C1` and `CoarseDegrees.DyadicRoute` are
sets that are coarsely equivalent to no block code. -/
theorem exists_not_ncEquiv_blockCode : ∃ X : Set ℕ, ∀ B : Set ℕ, ¬ (χ X ≡ₙ χ (blockCode B)) := by
  obtain ⟨A, hnc, -⟩ := exists_dyadic_no_least
  exact ⟨Rc A, fun B hB => hnc (isLeastNC_iff_blockCode.mpr ⟨B, hB⟩)⟩

end CoarseDegrees
