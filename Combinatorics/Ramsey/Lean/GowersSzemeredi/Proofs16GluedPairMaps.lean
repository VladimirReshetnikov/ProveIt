import GowersSzemeredi.Proofs16BohrSumExtension
import GowersSzemeredi.Proofs16ColumnTupleRelations
import GowersSzemeredi.Proofs16SelectedColumnExtensions
import GowersSzemeredi.Proofs16VarietyRegularStep
import GowersSzemeredi.Proofs16VarietyUnions

/-! The glued maps of the final selection in Milićević's Proposition 9.3
(arXiv:2601.01682, printed pp. 67–68), and why they respect quadruples.

For a good pair `(x_a, y_a)`, Lemma 9.1 glues the two column differences
`φ_{x_a+a} − φ_{x_a}` and `φ_{y_a+a} − φ_{y_a}` into one Freiman-linear map
`ψ_a` on the quarter-radius sum of their Bohr sets (`gluedPairMap`, using
`bohrSumExtension`). This needs the quadruple `(x_a + a, x_a, y_a + a, y_a)`
to be Bohr-respected (`ColumnPairCompatible`).
* `columnDifferenceMap_freimanOn`: a difference of two column maps that are
  Freiman-linear on their own Bohr sets is Freiman-linear on the
  intersection.
* `gluedPairMap_spec`: `ψ` is Freiman-linear on the quarter sum, `ψ(0) = 0`,
  and `ψ` equals each difference on its own quarter Bohr set.
* `glued_quadruple_respected`: the heart of the "expected number of
  Bohr-respected quadruples" step. Suppose four compatible pairs
  `(P_j, Q_j)` have Bohr-respected 8-tuples on both sides, and `d = u + u'`
  splits into the two tuple Bohr sets at quarter radius (containment (26)).
  Then `ψ₀(d) + ψ₁(d) = ψ₂(d) + ψ₃(d)`. Each `ψ_j(u + u')` equals
  `(φ-difference at P_j)(u) + (φ-difference at Q_j)(u')`, and both 8-tuples
  cancel. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A difference of column maps is Freiman-linear on the common Bohr set. -/
theorem columnDifferenceMap_freimanOn {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real}
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (p : ZMod N × ZMod N) :
    IsFreimanLinearOn (bohr (columnDifferenceSpectrum T p) r) (columnDifferenceMap L p) := by
  intro a b c d ha hb hc hd he
  simp only [columnDifferenceSpectrum, bohr_union, Finset.mem_inter] at ha hb hc hd
  have h1 := hL p.1 a b c d ha.1 hb.1 hc.1 hd.1 he
  have h2 := hL p.2 a b c d ha.2 hb.2 hc.2 hd.2 he
  simp only [columnDifferenceMap]
  linear_combination h1 - h2

/-- **Lemma 9.1 for a good pair**: the glued difference map. -/
def gluedPairMap {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real) (p q : ZMod N × ZMod N) : ZMod N → ZMod N :=
  bohrSumExtension (columnDifferenceSpectrum T p) (columnDifferenceSpectrum T q)
    (columnDifferenceMap L p) (columnDifferenceMap L q) r

theorem gluedPairMap_spec {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    {p q : ZMod N × ZMod N} (hpq : ColumnPairCompatible T L r p q) :
    IsFreimanLinearOn (bohrQuarterSum (columnDifferenceSpectrum T p)
        (columnDifferenceSpectrum T q) r) (gluedPairMap T L r p q) ∧
      gluedPairMap T L r p q 0 = 0 ∧
      (∀ z ∈ bohr (columnDifferenceSpectrum T p) (r / 4),
        gluedPairMap T L r p q z = columnDifferenceMap L p z) ∧
      (∀ z ∈ bohr (columnDifferenceSpectrum T q) (r / 4),
        gluedPairMap T L r p q z = columnDifferenceMap L q z) := by
  have hf := columnDifferenceMap_freimanOn T L hL p
  have hg := columnDifferenceMap_freimanOn T L hL q
  have hf0 : columnDifferenceMap L p 0 = 0 := by simp [columnDifferenceMap, hL0]
  have hg0 : columnDifferenceMap L q 0 = 0 := by simp [columnDifferenceMap, hL0]
  obtain ⟨h0, hp, hq⟩ := bohrSumExtension_restrict _ _ _ _ hr hf hg hf0 hg0 hpq
  exact ⟨bohrSumExtension_freiman _ _ _ _ hr hf hg hf0 hg0 hpq, h0, hp, hq⟩

/-- The value of the glued map on a quarter-radius split point. -/
theorem gluedPairMap_split {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    {p q : ZMod N × ZMod N} (hpq : ColumnPairCompatible T L r p q) {u u' : ZMod N}
    (hu : u ∈ bohr (columnDifferenceSpectrum T p) (r / 4))
    (hu' : u' ∈ bohr (columnDifferenceSpectrum T q) (r / 4)) :
    gluedPairMap T L r p q (u + u') = columnDifferenceMap L p u + columnDifferenceMap L q u' := by
  have hf := columnDifferenceMap_freimanOn T L hL p
  have hg := columnDifferenceMap_freimanOn T L hL q
  have hf0 : columnDifferenceMap L p 0 = 0 := by simp [columnDifferenceMap, hL0]
  have hg0 : columnDifferenceMap L q 0 = 0 := by simp [columnDifferenceMap, hL0]
  exact bohrSumExtension_spec _ _ _ _ hr hf hg hf0 hg0 hpq hu hu'

theorem mem_bohr_columnTuplePair {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (v : Fin 8 → ZMod N) {r : Real} {u : ZMod N}
    (hu : u ∈ bohr (columnTupleFrequencies T v) r) (j : Fin 4) :
    u ∈ bohr (columnDifferenceSpectrum T (columnTuplePairs v j)) r := by
  refine bohr_anti ?_ r hu
  intro z hz
  simp only [columnTupleFrequencies, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, hz⟩

/-- **Glued maps respect a quadruple.** -/
theorem glued_quadruple_respected {N : Nat} [NeZero N] (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hL0 : ∀ x, L x 0 = 0)
    (v w : Fin 8 → ZMod N)
    (hcompat : ∀ j, ColumnPairCompatible T L r (columnTuplePairs v j) (columnTuplePairs w j))
    (hv : ColumnTupleRespected T L r v) (hw : ColumnTupleRespected T L r w)
    {d : ZMod N} (hd : ∃ u ∈ bohr (columnTupleFrequencies T v) (r / 4),
      ∃ u' ∈ bohr (columnTupleFrequencies T w) (r / 4), d = u + u') :
    gluedPairMap T L r (columnTuplePairs v 0) (columnTuplePairs w 0) d +
        gluedPairMap T L r (columnTuplePairs v 1) (columnTuplePairs w 1) d =
      gluedPairMap T L r (columnTuplePairs v 2) (columnTuplePairs w 2) d +
        gluedPairMap T L r (columnTuplePairs v 3) (columnTuplePairs w 3) d := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hd
  have hs : ∀ j, gluedPairMap T L r (columnTuplePairs v j) (columnTuplePairs w j) (u + u') =
      columnDifferenceMap L (columnTuplePairs v j) u +
        columnDifferenceMap L (columnTuplePairs w j) u' := fun j =>
    gluedPairMap_split T L hr hL hL0 (hcompat j) (mem_bohr_columnTuplePair T v hu j)
      (mem_bohr_columnTuplePair T w hu' j)
  have h1 : ColumnDifferenceQuadruple L (columnTuplePairs v) u := hv u hu
  have h2 : ColumnDifferenceQuadruple L (columnTuplePairs w) u' := hw u' hu'
  simp only [ColumnDifferenceQuadruple] at h1 h2
  rw [hs 0, hs 1, hs 2, hs 3]
  linear_combination h1 + h2

end LeanProofs.GowersSzemeredi
