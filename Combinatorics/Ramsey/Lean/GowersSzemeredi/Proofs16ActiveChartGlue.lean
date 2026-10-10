import GowersSzemeredi.Proofs16AffineChartCompletion
import GowersSzemeredi.Proofs16PropNineThreeGlue

/-! Completed charts preserve the assembly's original active tests.
The twelve-tuple split needs only the indices active at each individual
vertex, rather than all cross-values of a padded common index window. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Local Freiman data survives a completed window which retains the active
frequencies. The completed domain is contained in the active domain. -/
theorem completed_window_local_freiman {N : Nat} [NeZero N] {k : Type*} [DecidableEq k]
    (J S : Finset k) (theta completed : k → ZMod N) (eta : Real)
    (F : ZMod N → ZMod N) (hSJ : S ⊆ J) (heq : ∀ i ∈ S, completed i = theta i)
    (hF : IsFreimanLinearOn (bohr (S.image theta) eta) F) :
    IsFreimanLinearOn (bohr (J.image completed) eta) F :=
  hF.mono (completed_window_bohr_subset_active J S theta completed eta hSJ heq)

/-- Vertexwise active tests transfer to the completed common window, with
no agreement requirement at inactive map indices. -/
theorem completed_window_quadruple_respected {N : Nat} [NeZero N] {k : Type*} [DecidableEq k]
    (J : Finset k) (S : ZMod N → Finset k) (theta completed : k → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) (eta : Real) (q : Fin 4 → ZMod N)
    (hSJ : ∀ j, S (q j) ⊆ J) (heq : ∀ j, ∀ i ∈ S (q j), completed i (q j) = theta i (q j))
    (hquad : ∀ y, (∀ j, y ∈ bohr ((S (q j)).image fun i => theta i (q j)) eta) →
      F (q 0) y+F (q 1) y = F (q 2) y+F (q 3) y) :
    ∀ y, (∀ j, y ∈ bohr (J.image fun i => completed i (q j)) eta) →
      F (q 0) y+F (q 1) y = F (q 2) y+F (q 3) y := by
  intro y hy
  exact hquad y (fun j => completed_window_bohr_subset_active J (S (q j))
    (fun i => theta i (q j)) (fun i => completed i (q j)) eta (hSJ j) (heq j) (hy j))

/-- The glued map's domain is preserved by changing only inactive window
frequencies. This strengthens the common-window domain link. -/
theorem good_pair_domain_completed {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) {r eta : Real}
    (theta completed : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat)
    {x y a : ZMod N} (hgood : (x,y,a) ∉ propNineThreeBad T (r/4) eta theta I)
    {J : Finset Nat} (hJ : I x a ∪ I y a ⊆ J)
    (heq : ∀ i ∈ I x a ∪ I y a, completed i a = theta i a) :
    bohr (J.image fun i => completed i a) eta ⊆
      bohrQuarterSum (columnDifferenceSpectrum T (colPair x a))
        (columnDifferenceSpectrum T (colPair y a)) r := by
  exact (completed_window_bohr_subset_active J (I x a ∪ I y a)
    (fun i => theta i a) (fun i => completed i a) eta hJ heq).trans
    (good_pair_domain T theta I hgood (Finset.Subset.refl _))

/-- The original good twelve-tuple test needs only vertexwise active values. -/
theorem twelve_good_respected_active {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r η : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    (θ : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat)
    (c : ZMod N → ZMod N × ZMod N) (q : Fin 4 → ZMod N) (hq : q 0 + q 1 = q 2 + q 3)
    (hcompat : ∀ j, ColumnPairCompatible T L r (colPair (c (q j)).1 (q j))
      (colPair (c (q j)).2 (q j)))
    (hbad : twelveOf q (fun j => c (q j)) ∉ propNineThreeBad12 T (r / 4) η θ I)
    (hrx : ColumnTupleRespected T L r (twelveXSide (twelveOf q (fun j => c (q j)))))
    (hry : ColumnTupleRespected T L r (twelveYSide (twelveOf q (fun j => c (q j)))))
    {w : ZMod N}
    (hw : ∀ j, w ∈ bohr ((chosenIndices I c (q j)).image fun i => θ i (q j)) η) :
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
    exact (mem_bohr_iff_le _ η w).mp (hw j) _ (Finset.mem_image_of_mem _ hi)
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

/-- Consequently affine completion of inactive indices preserves every good
selected quadruple on the completed common-window domains. -/
theorem twelve_good_respected_completed {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) {r eta : Real}
    (hr : 0 ≤ r) (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    (theta completed : Nat → ZMod N → ZMod N) (I : ZMod N → ZMod N → Finset Nat)
    (c : ZMod N → ZMod N × ZMod N) (q : Fin 4 → ZMod N) (hq : q 0+q 1 = q 2+q 3)
    (hcompat : ∀ j, ColumnPairCompatible T L r (colPair (c (q j)).1 (q j)) (colPair (c (q j)).2 (q j)))
    (hbad : twelveOf q (fun j => c (q j)) ∉ propNineThreeBad12 T (r/4) eta theta I)
    (hrx : ColumnTupleRespected T L r (twelveXSide (twelveOf q (fun j => c (q j)))))
    (hry : ColumnTupleRespected T L r (twelveYSide (twelveOf q (fun j => c (q j)))))
    {J : Finset Nat} (hJ : ∀ j, chosenIndices I c (q j) ⊆ J)
    (heq : ∀ j, ∀ i ∈ chosenIndices I c (q j), completed i (q j) = theta i (q j)) :
    ∀ y, (∀ j, y ∈ bohr (J.image fun i => completed i (q j)) eta) →
      chosenGlued T L r c (q 0) y+chosenGlued T L r c (q 1) y =
        chosenGlued T L r c (q 2) y+chosenGlued T L r c (q 3) y := by
  exact completed_window_quadruple_respected J (chosenIndices I c) theta completed
    (chosenGlued T L r c) eta q hJ heq
    (fun y hy => twelve_good_respected_active T L hr hL hL0 theta I c q hq hcompat hbad hrx hry hy)

end LeanProofs.GowersSzemeredi
