import GowersSzemeredi.Proofs16RepresentationQuadImageTransfer

/-! The original bad-tuple predicate controls good flattened representation
blocks on their actual sixteen-column domain, without a reference-map restriction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem good_flattened_representation_image {N K : Nat} [NeZero N]
    (U : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (q : Fin 4 → ZMod N) (b : Fin 4 → FourRepresentationTuple N)
    (hb : ∀ i, b i ∈ fourDifferenceRepresentations U (q i))
    (hadd : q 0-q 1+q 2-q 3 = 0)
    (hgood : flattenFourRepresentations b ∉ columnTupleImageExceptions U T L rho K) :
    ((bohr (columnListSpectrum T (columnAnchorList (flattenFourRepresentations b))) (rho/2)).image
      (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList (flattenFourRepresentations b)))).card ≤ K := by
  apply not_lt.mp
  intro hgt
  exact hgood (Finset.mem_filter.mpr ⟨flattenFourRepresentations_mem_fibre U q b hb hadd,hgt⟩)

end LeanProofs.GowersSzemeredi
