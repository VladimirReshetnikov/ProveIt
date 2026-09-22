import Surreal.HahnSeries.PolynomialCriticalBalls
import Mathlib.FieldTheory.Perfect

/-!
# A critical point at the nearest-root valuation

This proves the nearest-neighbour clause of `polynomial:cor:nearest` and
`polynomial:eq:nearest`. For a squarefree split polynomial of degree at least
two, each root has a critical point at the largest valuation of its difference
from another root, and every critical-point difference has at most that
valuation. Splitting of the derivative and characteristic zero of the
coefficient field are explicit. No algebraic closedness is assumed.

The finite-valued formulation records that no critical point equals the chosen
root; in particular, the total `order` function is never used at zero there.
-/

namespace Surreal.HahnSeries

open Polynomial Finset
open scoped _root_.HahnSeries Classical

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] [Field K]

private theorem openBallRootCount_eq_one_of_otherRoots_le
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hn : P.roots.Nodup)
    (a : K⟦Γ⟧) (ha : P.IsRoot a) (δ : Γ)
    (hbound : ∀ b, P.IsRoot b → b ≠ a → (b - a).orderTop ≤ (δ : WithTop Γ)) :
    openBallRootCount a δ P = 1 := by
  have hf : P.roots.filter (fun b => (δ : WithTop Γ) < (b - a).orderTop) = {a} := by
    apply (Multiset.Nodup.ext (hn.filter _) (Multiset.nodup_singleton a)).mpr
    intro b
    simp only [Multiset.mem_filter, Multiset.mem_singleton]
    constructor
    · rintro ⟨hb, hv⟩
      by_contra hne
      exact (not_lt_of_ge (hbound b ((mem_roots hP).mp hb) hne)) hv
    · rintro rfl
      exact ⟨(mem_roots hP).mpr ha, by simp⟩
  simp only [openBallRootCount, hf, Multiset.card_singleton]

variable [CharZero K]

local instance nearestHahnCharZero : CharZero K⟦Γ⟧ where
  cast_injective m n h := by
    apply Nat.cast_injective (R := K)
    apply _root_.HahnSeries.C_injective (Γ := Γ)
    simpa only [map_natCast] using h

/-- No critical point lies closer than a bound for all the other roots.
This is the open-ball half of `polynomial:eq:nearest`: the occupied open ball
contains exactly the single simple root, so its derivative count is zero. -/
theorem criticalPoint_orderTop_le_of_otherRoots_le
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits) (hsd : P.derivative.Splits)
    (hn : P.roots.Nodup) (a : K⟦Γ⟧) (ha : P.IsRoot a) (δ : Γ)
    (hbound : ∀ b, P.IsRoot b → b ≠ a → (b - a).orderTop ≤ (δ : WithTop Γ))
    {w : K⟦Γ⟧} (hw : P.derivative.IsRoot w) :
    (w - a).orderTop ≤ (δ : WithTop Γ) := by
  have hc := openBallRootCount_eq_one_of_otherRoots_le P hP hn a ha δ hbound
  have hdeg : 0 < P.natDegree :=
    (Multiset.card_pos_iff_exists_mem.mpr ⟨a, (mem_roots hP).mpr ha⟩).trans_le P.card_roots'
  have hd : P.derivative ≠ 0 := derivative_ne_zero.mpr (ne_of_gt hdeg)
  have hcd := openBallRootCount_iterate_derivative a δ P hP hs 1
    (by simpa only [Function.iterate_one] using hsd) (by omega)
  have hz : P.derivative.roots.filter
      (fun b => (δ : WithTop Γ) < (b - a).orderTop) = 0 := by
    apply Multiset.card_eq_zero.mp
    change openBallRootCount a δ P.derivative = 0
    simpa only [Function.iterate_one, hc, Nat.sub_self] using hcd
  by_contra hle
  have hm : w ∈ P.derivative.roots.filter
      (fun b => (δ : WithTop Γ) < (b - a).orderTop) :=
    Multiset.mem_filter.mpr ⟨(mem_roots hd).mpr hw, lt_of_not_ge hle⟩
  rw [hz] at hm
  exact Multiset.notMem_zero w hm

/-- The closed-ball half of `polynomial:eq:nearest`: when the bound on
other-root valuations is attained, a critical point attains the same finite
valuation. Root multiplicities are counted through the native root multiset. -/
theorem exists_criticalPoint_orderTop_eq_of_nearest_root
    (P : K⟦Γ⟧[X]) (hP : P ≠ 0) (hs : P.Splits) (hsd : P.derivative.Splits)
    (hn : P.roots.Nodup) (a : K⟦Γ⟧) (ha : P.IsRoot a) (δ : Γ)
    (hbound : ∀ b, P.IsRoot b → b ≠ a → (b - a).orderTop ≤ (δ : WithTop Γ))
    (hattain : ∃ b, P.IsRoot b ∧ b ≠ a ∧ (b - a).orderTop = (δ : WithTop Γ)) :
    ∃ w, P.derivative.IsRoot w ∧ w ≠ a ∧ (w - a).orderTop = (δ : WithTop Γ) := by
  obtain ⟨b, hb, hba, hv⟩ := hattain
  have hmem_a : a ∈ P.roots.filter
      (fun z => (δ : WithTop Γ) ≤ (z - a).orderTop) := by
    exact Multiset.mem_filter.mpr ⟨(mem_roots hP).mpr ha, by simp⟩
  have hmem_b : b ∈ P.roots.filter
      (fun z => (δ : WithTop Γ) ≤ (z - a).orderTop) :=
    Multiset.mem_filter.mpr ⟨(mem_roots hP).mpr hb, hv.ge⟩
  have htwo : 2 ≤ closedBallRootCount a δ P := by
    have hcard : 1 < (P.roots.filter
        (fun z => (δ : WithTop Γ) ≤ (z - a).orderTop)).toFinset.card :=
      Finset.one_lt_card.mpr ⟨a, by simpa using hmem_a, b, by simpa using hmem_b, hba.symm⟩
    have hle := Multiset.toFinset_card_le (P.roots.filter
      (fun z => (δ : WithTop Γ) ≤ (z - a).orderTop))
    exact hcard.trans_le hle
  have hcd := closedBallRootCount_iterate_derivative a δ P hP hs 1
    (by simpa only [Function.iterate_one] using hsd) (by omega)
  have hpos : 0 < (P.derivative.roots.filter
      (fun z => (δ : WithTop Γ) ≤ (z - a).orderTop)).card := by
    change 0 < closedBallRootCount a δ P.derivative
    simpa only [Function.iterate_one] using (show 0 < closedBallRootCount a δ (derivative^[1] P) by omega)
  obtain ⟨w, hw⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
  obtain ⟨hwr, hwδ⟩ := Multiset.mem_filter.mp hw
  have hroot : P.derivative.IsRoot w := Polynomial.isRoot_of_mem_roots hwr
  have heq := le_antisymm
    (criticalPoint_orderTop_le_of_otherRoots_le P hP hs hsd hn a ha δ hbound hroot) hwδ
  refine ⟨w, hroot, ?_, heq⟩
  intro he
  simp [he] at heq

/-- The finite set of valuations of differences from the other roots.
The center is removed before applying `order`, so every such difference is
nonzero. This is the right-hand maximum in `polynomial:eq:nearest`. -/
def otherRootValues (P : K⟦Γ⟧[X]) (a : K⟦Γ⟧) : Finset Γ :=
  (P.roots.toFinset.erase a).image (fun b => (b - a).order)

/-- The finite set of critical-point displacement orders. In the nearest-root
theorem below, squarefreeness ensures that these displacements are nonzero. -/
def criticalPointValues (P : K⟦Γ⟧[X]) (a : K⟦Γ⟧) : Finset Γ :=
  P.derivative.roots.toFinset.image (fun w => (w - a).order)

/-- `polynomial:eq:nearest`, stated as equality of attained maxima of finite
sets: the other-root and critical-point valuations have a common greatest
element. The final clause guarantees finite valuations at every critical
point. Both splitting hypotheses and residue characteristic zero are explicit. -/
theorem nearestCriticalValue
    (P : K⟦Γ⟧[X]) (hsq : Squarefree P) (hs : P.Splits)
    (hsd : P.derivative.Splits) (hdeg : 2 ≤ P.natDegree)
    (a : K⟦Γ⟧) (ha : P.IsRoot a) :
    ∃ δ : Γ, IsGreatest (↑(otherRootValues P a) : Set Γ) δ ∧
      IsGreatest (↑(criticalPointValues P a) : Set Γ) δ ∧
      (∀ w, P.derivative.IsRoot w → w ≠ a) := by
  have hP : P ≠ 0 := by intro hz; simp [hz] at hdeg
  have hn : P.roots.Nodup := Polynomial.nodup_roots
    (PerfectField.separable_iff_squarefree.mpr hsq)
  have hd : P.derivative ≠ 0 := derivative_ne_zero.mpr (by omega)
  have hcard : 1 < P.roots.toFinset.card := by
    rw [Multiset.toFinset_card_of_nodup hn, ← hs.natDegree_eq_card_roots]
    omega
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne hcard a
  have hne : (P.roots.toFinset.erase a).Nonempty := ⟨b, mem_erase.mpr ⟨hba, hb⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image (P.roots.toFinset.erase a)
    (fun b => (b - a).order) hne
  obtain ⟨hba, hbr⟩ := mem_erase.mp hb
  let δ := (b - a).order
  have hbδ : (b - a).orderTop = (δ : WithTop Γ) :=
    (_root_.HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr hba)).symm
  have hbound : ∀ c, P.IsRoot c → c ≠ a → (c - a).orderTop ≤ (δ : WithTop Γ) := by
    intro c hc hca
    rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr hca)]
    exact_mod_cast hmax c (mem_erase.mpr ⟨hca, by simpa using (mem_roots hP).mpr hc⟩)
  have hboundw := fun w (hw : P.derivative.IsRoot w) =>
    criticalPoint_orderTop_le_of_otherRoots_le P hP hs hsd hn a ha δ hbound hw
  have hwne : ∀ w, P.derivative.IsRoot w → w ≠ a := by
    intro w hw he
    have := hboundw w hw
    simp [he] at this
  obtain ⟨w, hw, hwa, hwδ⟩ := exists_criticalPoint_orderTop_eq_of_nearest_root
    P hP hs hsd hn a ha δ hbound
    ⟨b, (mem_roots hP).mp (by simpa using hbr), hba, hbδ⟩
  have hwδ' : (w - a).order = δ := by
    apply WithTop.coe_injective
    rw [_root_.HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr hwa), hwδ]
  refine ⟨δ, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hwne⟩
  · exact mem_image.mpr ⟨b, hb, rfl⟩
  · rintro γ hγ
    obtain ⟨c, hc, rfl⟩ := mem_image.mp hγ
    exact hmax c hc
  · exact mem_image.mpr ⟨w, by simpa using (mem_roots hd).mpr hw, hwδ'⟩
  · rintro γ hγ
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hγ
    have hzr := (mem_roots hd).mp (by simpa using hz)
    have hv := hboundw z hzr
    rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero (sub_ne_zero.mpr (hwne z hzr))] at hv
    exact_mod_cast hv

end

end Surreal.HahnSeries
