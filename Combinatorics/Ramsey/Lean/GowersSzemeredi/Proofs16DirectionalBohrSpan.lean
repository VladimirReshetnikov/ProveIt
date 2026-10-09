import GowersSzemeredi.Proofs16BoundedSpanAlgebra
import GowersSzemeredi.Proofs16BohrSumRankCap
import GowersSzemeredi.Proofs16BilinearBogolyubovRows

/-! The bounded-span Bohr-sum theorem inside the directional difference
construction. This is the column-frequency input to the selection stage. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def frequencyDifference {N : Nat} (U V : Finset (ZMod N)) : Finset (ZMod N) :=
  (U ×ˢ V).image fun p => p.1 - p.2

def rowSpanAlphabet {N : Nat} [NeZero N] (Gamma : ZMod N → Finset (ZMod N))
    (R : Nat) (y : ZMod N) : Finset (ZMod N) :=
  boundedFrequencySpan (fun k : Gamma y => (k : ZMod N)) R

def directionalSpanCutoff (r M : Nat) (rho : Real) : Nat :=
  polynomialSpectrumCutoff (2 * r) (rho / 2) (bohrSumRankThreshold (2 * r) (2 * r) M M)

/-- The row alphabets meet the finite-size and zero-membership requirements
of the selection theorem. -/
theorem rowSpanAlphabet_bounds {N : Nat} [NeZero N]
    (Gamma : ZMod N → Finset (ZMod N)) (r R : Nat) (hGamma : ∀ y, (Gamma y).card ≤ r) :
    ∀ y, (0 : ZMod N) ∈ rowSpanAlphabet Gamma R y ∧
      (rowSpanAlphabet Gamma R y).card ≤ (2 * R + 1)^r := by
  intro y
  refine ⟨zero_mem_boundedFrequencySpan _ _, (boundedFrequencySpan_card_le _ _).trans ?_⟩
  simp only [Fintype.card_coe]
  exact Nat.pow_le_pow_right (by omega) (hGamma y)

/-- A union spectrum lies in the difference of the two row alphabets. -/
theorem boundedFrequencySpan_union_subset_difference {N : Nat} [NeZero N]
    (K L : Finset (ZMod N)) (R : Nat) :
    boundedFrequencySpan (fun k : ↥(K ∪ L) => (k : ZMod N)) R ⊆
      frequencyDifference (boundedFrequencySpan (fun k : K => (k : ZMod N)) R)
        (boundedFrequencySpan (fun l : L => (l : ZMod N)) R) := by
  intro x hx
  obtain ⟨u, hu, v, hv, hx⟩ := boundedFrequencySpan_union_difference K L R hx
  exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, hx.symm⟩

/-- The next horizontal difference contains the Bohr set of the common
row-difference frequencies, with one cutoff for all four rows. -/
theorem directional_bohr_span {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    (Gamma : ZMod N → Finset (ZMod N)) (r M : Nat) [NeZero M]
    (hGamma : ∀ t, (Gamma t).card ≤ r) {rho : Real}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M)
    (hrows : ∀ t ∈ Y, ∀ x ∈ bohr (Gamma t) rho, (x, t) ∈ A)
    (y z w d : ZMod N) (hyz : y + z ∈ Y) (hz : z ∈ Y) (hyw : y + w ∈ Y) (hw : w ∈ Y)
    (hd : d ∈ bohr
      (frequencyDifference (rowSpanAlphabet Gamma (directionalSpanCutoff r M rho) (y + z))
          (rowSpanAlphabet Gamma (directionalSpanCutoff r M rho) z) ∩
       frequencyDifference (rowSpanAlphabet Gamma (directionalSpanCutoff r M rho) (y + w))
          (rowSpanAlphabet Gamma (directionalSpanCutoff r M rho) w)) (1 / (4 * Real.pi))) :
    (d, y) ∈ horDiff (verDiff A) := by
  let K := Gamma (y + z) ∪ Gamma z
  let L := Gamma (y + w) ∪ Gamma w
  have hK : K.card ≤ 2 * r := (Finset.card_union_le _ _).trans (by have := hGamma (y + z); have := hGamma z; omega)
  have hL : L.card ≤ 2 * r := (Finset.card_union_le _ _).trans (by have := hGamma (y + w); have := hGamma w; omega)
  have hcommon : d ∈ bohr
      (boundedFrequencySpan (fun k : K => (k : ZMod N)) (directionalSpanCutoff r M rho) ∩
       boundedFrequencySpan (fun l : L => (l : ZMod N)) (directionalSpanCutoff r M rho))
      (1 / (4 * Real.pi)) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun q hq => ?_⟩
    obtain ⟨hqK, hqL⟩ := Finset.mem_inter.mp hq
    exact (Finset.mem_filter.mp hd).2 q (Finset.mem_inter.mpr
      ⟨boundedFrequencySpan_union_subset_difference _ _ _ hqK,
       boundedFrequencySpan_union_subset_difference _ _ _ hqL⟩)
  obtain ⟨u, hu, v, hv, hd'⟩ := bohr_sum_contains_rank_cap_span K L (2 * r) M hK hL hrho hrho1 hM d hcommon
  have hrowpair (t : ZMod N) (hyt : y + t ∈ Y) (ht : t ∈ Y) (x : ZMod N)
      (hx : x ∈ bohr (Gamma (y + t) ∪ Gamma t) rho) : (x, y) ∈ verDiff A := by
    have hx1 : x ∈ bohr (Gamma (y + t)) rho := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun q hq => (Finset.mem_filter.mp hx).2 q (Finset.mem_union_left _ hq)⟩
    have hx2 : x ∈ bohr (Gamma t) rho := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun q hq => (Finset.mem_filter.mp hx).2 q (Finset.mem_union_right _ hq)⟩
    simpa using mem_verDiff (hrows (y + t) hyt x hx1) (hrows t ht x hx2)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, -v,
    hrowpair z hyz hz u hu, hrowpair w hyw hw (-v) (neg_mem_bohr hv), by simpa using hd'⟩

end LeanProofs.GowersSzemeredi
