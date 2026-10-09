import GowersSzemeredi.Proofs16TuplePatternBridge

/-! Robust row filling and proper-progression completion for arbitrary
finite tuples, with the same graph and error constants as the pattern form. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Tuple row geometry fills every target row in the robust spectrum Bohr set. -/
theorem robust_tuple_row_filled {N Q r : Nat} [NeZero N] [NeZero Q]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N)) (W C T F : Finset (ZMod N))
    (L : κ → ZMod N → ZMod N) (a y : ZMod N) {alpha sigma eta delta epsilon : Real}
    (ha : 0 < alpha) (hcard : (W.card : Real) = alpha * N) (hWC : W ⊆ C)
    (hsigma : 0 ≤ sigma) (heta : 0 < eta) (hC : C.Nonempty)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon)
    (hW : W ⊆ bohr T (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr T sigma) (L j)) (hzero : ∀ j, L j 0 = 0)
    (hgeom : tupleRowGeometry A W F L a eta)
    (hbox : boxSum (fun (x : ↥(bohr F eta)) (t : ↥C) =>
      (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j t) (eta / 4) then (1 : Real) else 0) - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2)
    (hy : y ∈ bohr (commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)) (1 / (4 * Real.pi)))
    (hK : (F ∪ Finset.univ.image (fun j => L j y)).card ≤ r) (hQ : 4 ≤ eta * Q)
    (hbudget : (4 : Real)^(r + 1) * (12 * epsilon) * (Q : Real)^r ≤
      (delta^3 * robustRepresentationDensity alpha C)^2) :
    ∀ d ∈ bohr (F ∪ Finset.univ.image (fun j => L j y)) (eta / 4 / 2),
      (d, y) ∈ horDiff (verDiff (verDiff A)) := by
  have h := robust_pattern_row_filled_rank A W C T F (tuplePatternMaps L)
    (tuplePatternIndices (Fintype.card κ)) a y ha hcard hWC hsigma heta hC hd0 hd1 heps hW
    (fun i _ => ⟨(hL _).freimanHom, hzero _⟩)
    (by simpa only [tuplePattern_frequencies, tupleRowGeometry] using hgeom)
    (by simpa only [tuplePattern_edgeIndicator] using hbox) hy
    (by simpa only [tuplePattern_frequencies] using hK) hQ hbudget
  simpa only [tuplePattern_frequencies] using h

/-- A tuple graph and its robust budget produce an actual proper progression
whose target rows are contained in the seven-operator set. -/
theorem proper_progression_tuple_completion {N Q r : Nat} [NeZero N] [NeZero Q]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N)) (W C T F : Finset (ZMod N))
    (L : κ → ZMod N → ZMod N) (a : ZMod N) {alpha sigma eta delta epsilon : Real}
    (ha : 0 < alpha) (hcard : (W.card : Real) = alpha * N) (hWC : W ⊆ C)
    (hsigma : 0 ≤ sigma) (heta : 0 < eta) (hC : C.Nonempty)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon)
    (hW : W ⊆ bohr T (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr T sigma) (L j)) (hzero : ∀ j, L j 0 = 0)
    (hgeom : tupleRowGeometry A W F L a eta)
    (hbox : boxSum (fun (x : ↥(bohr F eta)) (t : ↥C) =>
      (if (x : ZMod N) ∈ bohr (Finset.univ.image fun j => L j t) (eta / 4) then (1 : Real) else 0) - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2)
    (hF : F.card + 2 * Fintype.card κ ≤ r) (hQ : 4 ≤ eta * Q)
    (hbudget : (4 : Real)^(r + 1) * (12 * epsilon) * (Q : Real)^r ≤
      (delta^3 * robustRepresentationDensity alpha C)^2) :
    ∃ U : Finset (ZMod N), ∃ P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N,
      (U.card : Real) ≤ 16 / alpha^2 ∧ P.rank ≤ U.card + 1 ∧ P.Proper ∧
      0 ∈ P.carrier ∧ (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧ P.carrier ⊆ bohr T sigma ∧
      Real.exp (-(((U.card : Real) + 1) * Real.log (1 + Real.pi) +
        10 * ((U.card : Real) + 1)^2)) * N ≤ P.carrier.card ∧
      ∀ y ∈ P.carrier, ∀ d ∈ bohr (F ∪ Finset.univ.image (fun j => L j y)) (eta / 4 / 2),
        (d, y) ∈ horDiff (verDiff (verDiff A)) := by
  have h := proper_progression_pattern_completion A W C T F (tuplePatternMaps L)
    (tuplePatternIndices (Fintype.card κ)) a ha hcard hWC hsigma heta hC hd0 hd1 heps hW
    (fun i _ => ⟨(hL _).freimanHom, hzero _⟩)
    (by simpa only [tuplePattern_frequencies, tupleRowGeometry] using hgeom)
    (by simpa only [tuplePattern_edgeIndicator] using hbox)
    (fun _ => by simp [tuplePatternIndices]) hF hQ hbudget
  simpa only [tuplePattern_frequencies] using h

end LeanProofs.GowersSzemeredi
