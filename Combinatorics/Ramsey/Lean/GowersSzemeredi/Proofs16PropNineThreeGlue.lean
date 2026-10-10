import GowersSzemeredi.Proofs16FinalAssemblyTools
import GowersSzemeredi.Proofs16FinalPairChoice

/-! The two deterministic links of the Proposition 9.3 assembly (J.5c):
how the iteration's final state feeds the glued maps.

Fix the iteration data `θ, I` at Bohr radius `r/4`, the radius at which
`bohrQuarterSum` sees the column differences.
* `good_pair_domain` (Lemma A). Suppose `(x, y)` is good for `a`: the
  quadruple `(x+a, x, y+a, y)` is compatible and `(x, y, a)` is not a bad
  triple. Then for any `J ⊇ I_{x,a} ∪ I_{y,a}`, the Bohr set
  `B(θ_i(a) : i ∈ J; η)` lies in the quarter sum on which the glued map
  `gluedPairMap` is Freiman-linear.
* `twelve_good_respected` (Lemma B). A quadruple `q` of `a`'s whose
  12-tuple `twelveOf q (c ∘ q)` is not bad, has both 8-tuples respected,
  and has compatible chosen pairs, is respected by the glued maps on
  `⋂_j B(θ_i(q_j) : i ∈ J; η)` whenever `J` contains every
  `I_{x_{q_j},q_j} ∪ I_{y_{q_j},q_j}`. The split comes from "not bad"
  through `columnTupleFrequencies_twelveXSide`, and then
  `glued_quadruple_respected` applies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mem_bohr_iff_le {N : Nat} [NeZero N] (K : Finset (ZMod N)) (δ : Real) (d : ZMod N) :
    d ∈ bohr K δ ↔ ∀ k ∈ K, (centeredAbs (k * d) : Real) ≤ δ * N := by
  unfold bohr
  simp

/-- The pair of columns `(x + a, x)`. -/
abbrev colPair {N : Nat} (x a : ZMod N) : ZMod N × ZMod N := (x + a, x)

/-- **Lemma A: the glued map's domain contains the window Bohr set.** -/
theorem good_pair_domain {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N)) {r η : Real}
    (θ : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat) {x y a : ZMod N}
    (hgood : (x, y, a) ∉ propNineThreeBad T (r / 4) η θ I) {J : Finset Nat}
    (hJ : I x a ∪ I y a ⊆ J) :
    bohr (J.image fun i => θ i a) η ⊆
      bohrQuarterSum (columnDifferenceSpectrum T (colPair x a))
        (columnDifferenceSpectrum T (colPair y a)) r := by
  intro w hw
  have hsmall : ∀ i ∈ I x a ∪ I y a, (centeredAbs (θ i a * w) : Real) ≤ η * N := by
    intro i hi
    exact (mem_bohr_iff_le _ η w).mp hw _ (Finset.mem_image_of_mem _ (hJ hi))
  have hnot : ¬ ¬ ∃ u ∈ bohr (T (x + a) ∪ T x) (r / 4),
      ∃ v ∈ bohr (T (y + a) ∪ T y) (r / 4), w = u + v := by
    intro h
    exact hgood (Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hsmall, h⟩)
  obtain ⟨u, hu, v, hv, rfl⟩ := not_not.mp hnot
  exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩

/-- The index set of the chosen pair `c a`. -/
def chosenIndices {N : Nat} (I : ZMod N → ZMod N → Finset Nat)
    (c : ZMod N → ZMod N × ZMod N) (a : ZMod N) : Finset Nat :=
  I (c a).1 a ∪ I (c a).2 a

/-- The glued map at `a` for the chosen pair `c a`. -/
def chosenGlued {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (c : ZMod N → ZMod N × ZMod N) (a : ZMod N) :
    ZMod N → ZMod N :=
  gluedPairMap T L r (colPair (c a).1 a) (colPair (c a).2 a)

/-- **Lemma B: a good 12-tuple makes its quadruple respected.** -/
theorem twelve_good_respected {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r η : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    (θ : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat)
    (c : ZMod N → ZMod N × ZMod N) (q : Fin 4 → ZMod N) (hq : q 0 + q 1 = q 2 + q 3)
    (hcompat : ∀ j, ColumnPairCompatible T L r (colPair (c (q j)).1 (q j))
      (colPair (c (q j)).2 (q j)))
    (hbad : twelveOf q (fun j => c (q j)) ∉ propNineThreeBad12 T (r / 4) η θ I)
    (hrx : ColumnTupleRespected T L r (twelveXSide (twelveOf q (fun j => c (q j)))))
    (hry : ColumnTupleRespected T L r (twelveYSide (twelveOf q (fun j => c (q j)))))
    {J : Finset Nat} (hJ : ∀ j, chosenIndices I c (q j) ⊆ J) {w : ZMod N}
    (hw : ∀ j, w ∈ bohr (J.image fun i => θ i (q j)) η) :
    chosenGlued T L r c (q 0) w + chosenGlued T L r c (q 1) w =
      chosenGlued T L r c (q 2) w + chosenGlued T L r c (q 3) w := by
  set u := twelveOf q (fun j => c (q j)) with hu
  have hco : ∀ j, twelveX u j = (c (q j)).1 ∧ twelveY u j = (c (q j)).2 ∧ twelveA u j = q j :=
    twelveOf_coords q (fun j => c (q j)) hq
  have hpairX : ∀ j, columnTuplePairs (twelveXSide u) j = colPair (c (q j)).1 (q j) := by
    intro j
    rw [columnTuplePairs_twelveXSide]
    obtain ⟨h1, -, h3⟩ := hco j
    show (twelveX u j + twelveA u j, twelveX u j) = _
    rw [h1, h3]
  have hpairY : ∀ j, columnTuplePairs (twelveYSide u) j = colPair (c (q j)).2 (q j) := by
    intro j
    rw [columnTuplePairs_twelveYSide]
    obtain ⟨-, h2, h3⟩ := hco j
    show (twelveY u j + twelveA u j, twelveY u j) = _
    rw [h2, h3]
  -- the split from "not bad"
  have hsmall : ∀ j, ∀ i ∈ I (twelveX u j) (twelveA u j) ∪ I (twelveY u j) (twelveA u j),
      (centeredAbs (θ i (twelveA u j) * w) : Real) ≤ η * N := by
    intro j i hi
    obtain ⟨h1, h2, h3⟩ := hco j
    rw [h1, h2, h3] at hi
    rw [h3]
    exact (mem_bohr_iff_le _ η w).mp (hw j) _ (Finset.mem_image_of_mem _ (hJ j hi))
  have hsplit : ∃ v ∈ bohr (twelveK T u) (r / 4), ∃ v' ∈ bohr (twelveL T u) (r / 4),
      w = v + v' := by
    by_contra h
    exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hsmall, h⟩)
  rw [← columnTupleFrequencies_twelveXSide, ← columnTupleFrequencies_twelveYSide] at hsplit
  have hcompat' : ∀ j, ColumnPairCompatible T L r (columnTuplePairs (twelveXSide u) j)
      (columnTuplePairs (twelveYSide u) j) := by
    intro j
    rw [hpairX j, hpairY j]
    exact hcompat j
  have key := glued_quadruple_respected T L hr hL hL0 (twelveXSide u) (twelveYSide u) hcompat'
    hrx hry hsplit
  simp only [hpairX, hpairY] at key
  exact key

end LeanProofs.GowersSzemeredi
