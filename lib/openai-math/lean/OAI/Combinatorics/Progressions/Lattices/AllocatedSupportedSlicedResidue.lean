import OAI.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
import OAI.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
import OAI.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
import OAI.Combinatorics.Progressions.Probability.AllocatedWholeDeckLaw

namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_residue_support
    (y : PrincipalIntegerTuples B h α L) (hy : (law).weight y ≠ 0) :
    ∀ j a, ((y j a : ℤ) : ZMod q) =
      (if a = none then (c j : ZMod q) else 0) + (step j : ZMod q) * r j a := by
  apply (weights).fiberLaw_support (containedProgressionTupleMap B h L H step c hL hsubset)
    (fun y => ∀ j a, ((y j a : ℤ) : ZMod q) =
      (if a = none then (c j : ZMod q) else 0) + (step j : ZMod q) * r j a) _ y hy
  intro z hz j a
  have hpos := lt_of_le_of_ne ((weights).nonneg z) hz.symm
  have hmem := ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp hpos).1
  have hr : principalResidueLabel q z = r := (Finset.mem_filter.mp hmem).2
  have hza : ((z j a : ℤ) : ZMod q) = r j a := congrFun (congrFun hr j) a
  have hcube := principalSupportedResidue_cube_support B h H hH q r hcell z hz j
  change ((containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (z j) a : ℤ) : ZMod q) = _
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ hcube]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero, hza]

theorem containedSupportedProgressionLaw_residue_eq
    (y z : PrincipalIntegerTuples B h α L) (hy : (law).weight y ≠ 0) (hz : (law).weight z ≠ 0) :
    principalResidueLabel q y = principalResidueLabel q z := by
  funext j a
  exact (containedSupportedProgressionLaw_residue_support B h L H step c hL hH hsubset q r hcell y hy j a).trans
    (containedSupportedProgressionLaw_residue_support B h L H step c hL hH hsubset q r hcell z hz j a).symm

theorem containedSupportedProgressionAxisLaw_fiberLaw (P : D → Prop) [DecidablePred P] :
    (law).fiberLaw (principalAxisRestrict P) =
      containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P := by
  apply FiniteProbabilityWeights.toPMF_injective
  exact (FiniteProbabilityWeights.toPMF_fiberLaw (law) (principalAxisRestrict P)).trans
    (containedSupportedProgressionLaw_axis_marginal B h L H step c hL hH hsubset q r hcell P)

theorem containedSupportedProgressionAxisLaw_residue_support (P : D → Prop) [DecidablePred P]
    (u : PrincipalAxisTuples (α := α) P L)
    (hu : (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0) :
    ∀ j a, ((u j a : ℤ) : ZMod q) =
      (if a = none then (c ⟨j.1.val, j.2⟩ : ZMod q) else 0) +
        (step ⟨j.1.val, j.2⟩ : ZMod q) * r ⟨j.1.val, j.2⟩ a := by
  rw [← containedSupportedProgressionAxisLaw_fiberLaw B h L H step c hL hH hsubset q r hcell P] at hu
  apply (law).fiberLaw_support (principalAxisRestrict P) _ _ u hu
  intro y hy j a
  exact containedSupportedProgressionLaw_residue_support B h L H step c hL hH hsubset q r hcell y hy ⟨j.1.val, j.2⟩ a

theorem containedSupportedProgressionAxisLaw_residue_eq (P : D → Prop) [DecidablePred P]
    (u v : PrincipalAxisTuples (α := α) P L)
    (hu : (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0)
    (hv : (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight v ≠ 0) :
    principalResidueLabel q u = principalResidueLabel q v := by
  funext j a
  exact (containedSupportedProgressionAxisLaw_residue_support B h L H step c hL hH hsubset q r hcell P u hu j a).trans
    (containedSupportedProgressionAxisLaw_residue_support B h L H step c hL hH hsubset q r hcell P v hv j a).symm

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerProgressionSupport_subset_iff_fin (L H step : ℕ) (start : ℤ) :
    integerProgressionSupport start (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ) ↔
      ∀ t : Fin H, 0 ≤ start + (step : ℤ) * t.val ∧
        start + (step : ℤ) * t.val < L := by
  constructor
  · intro hs t
    apply Finset.mem_Ico.mp
    apply hs
    rw [integerProgressionSupport, mem_translateSupport]
    apply Finset.mem_image.mpr
    refine ⟨(t.val : ℤ), Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast t.isLt⟩, ?_⟩
    change (step : ℤ) * t.val = _
    ring
  · intro hi z hz
    rw [integerProgressionSupport, mem_translateSupport] at hz
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz
    have hv' := Finset.mem_Ico.mp hv
    let t : Fin H := ⟨v.toNat, by omega⟩
    have ht : (t.val : ℤ) = v := Int.toNat_of_nonneg hv'.1
    have hi' := hi t
    rw [ht] at hi'
    change (step : ℤ) * v = _ at he
    apply Finset.mem_Ico.mpr
    constructor <;> omega

theorem integerProgressionSupport_subset_of_fin (L H step : ℕ) (start : ℤ)
    (hinside : ∀ t : Fin H, 0 ≤ start + (step : ℤ) * t.val ∧
      start + (step : ℤ) * t.val < L) :
    integerProgressionSupport start (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ) :=
  (integerProgressionSupport_subset_iff_fin L H step start).mpr hinside

private def finIntegerIntervalEquiv (L : ℕ) :
    Fin L ≃ ↥(Finset.Ico (0 : ℤ) (L : ℤ)) where
  toFun t := ⟨t.val, Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast t.isLt⟩⟩
  invFun z := ⟨z.val.toNat, by have hz := Finset.mem_Ico.mp z.property; omega⟩
  left_inv t := by apply Fin.ext; simp
  right_inv z := by
    apply Subtype.ext
    change (z.val.toNat : ℤ) = z.val
    exact Int.toNat_of_nonneg (Finset.mem_Ico.mp z.property).1

def zeroScalarFinPoint (L : ℕ) (t : Fin L) : IntegerScalarCubeBox Empty L :=
  fun _ => ⟨t.val, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast t.isLt⟩⟩

private theorem zeroScalar_fin_mean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℝ) :
    (integerScalarCubeWeights Empty L hL).mean f = 𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  rw [integerScalarCubeWeights_mean]
  apply Fintype.expect_equiv
    ((zeroScalarCubeIntervalEquiv Empty L).trans (finIntegerIntervalEquiv L).symm)
  intro x
  congr 1
  funext a
  apply Subtype.ext
  cases a with
  | none =>
    have hx := ((mem_integerScalarCubeSet L x.val).mp x.property) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at hx
    exact (Int.toNat_of_nonneg hx.1).symm
  | some a => exact isEmptyElim a

theorem zeroScalar_fin_complexMean (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox Empty L → ℂ) :
    (integerScalarCubeWeights Empty L hL).complexMean f =
      𝔼 t : Fin L, f (zeroScalarFinPoint L t) := by
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  rw [← FiniteProbabilityWeights.uniform_complexMean]
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).re)
  · simpa only [FiniteProbabilityWeights.complexMean_im, FiniteProbabilityWeights.uniform_mean]
      using zeroScalar_fin_mean L hL (fun z => (f z).im)

theorem integerScalarCubeWeights_pi_fin_complexMean
    {X : Type*} [Fintype X] [DecidableEq X]
    (H : X → ℕ) (hH : ∀ i, 0 < H i)
    (f : (∀ i, IntegerScalarCubeBox Empty (H i)) → ℂ) :
    (FiniteProbabilityWeights.pi (fun i => integerScalarCubeWeights Empty (H i) (hH i))).complexMean f =
      𝔼 t : (∀ i, Fin (H i)), f (fun i => zeroScalarFinPoint (H i) (t i)) := by
  let : ∀ i, Nonempty (Fin (H i)) := fun i => ⟨⟨0, hH i⟩⟩
  have htransport := FiniteProbabilityWeights.complexMean_pi_transport_fintype
    (fun i => integerScalarCubeWeights Empty (H i) (hH i))
    (fun i => FiniteProbabilityWeights.uniform (Fin (H i)))
    (fun _ x => x) (fun i => zeroScalarFinPoint (H i))
    (fun i g => (zeroScalar_fin_complexMean (H i) (hH i) g).trans
      (FiniteProbabilityWeights.uniform_complexMean _).symm) f
  exact htransport.trans (FiniteProbabilityWeights.pi_uniform_complexMean _)

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

def principalFinTuplePoint (t : ∀ j, Fin (H j)) : PrincipalIntegerTuples B h Empty H :=
  fun j => zeroScalarFinPoint (H j) (t j)

theorem principalTupleWeights_fin_complexMean (f : PrincipalIntegerTuples B h Empty H → ℂ) :
    (principalTupleWeights (α := Empty) B h H hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  exact integerScalarCubeWeights_pi_fin_complexMean H hH f

theorem principalTupleWeights_fin_mean (f : PrincipalIntegerTuples B h Empty H → ℝ) :
    (principalTupleWeights (α := Empty) B h H hH).mean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalFinTuplePoint B h H t) := by
  let : ∀ j, Nonempty (Fin (H j)) := fun j => ⟨⟨0, hH j⟩⟩
  have he := congrArg Complex.re (principalTupleWeights_fin_complexMean B h H hH (fun z => (f z : ℂ)))
  rw [← FiniteProbabilityWeights.uniform_complexMean] at he
  simpa only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re,
    FiniteProbabilityWeights.uniform_mean] using he

def principalFinResidueLabel (q : ℕ) (t : ∀ j, Fin (H j)) :
    PrincipalTupleIndex B h → Option Empty → ZMod q := fun j _ => ((t j).val : ZMod q)

noncomputable def principalFinResidueCell (q : ℕ)
    (r : PrincipalTupleIndex B h → Option Empty → ZMod q) : Finset (∀ j, Fin (H j)) :=
  Finset.univ.filter (fun t => principalFinResidueLabel B h H q t = r)

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
theorem principalFinTuplePoint_residue [Fintype D] [DecidableEq D]
    [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)]
    (q : ℕ) (t : ∀ j, Fin (H j)) :
    principalResidueLabel q (principalFinTuplePoint B h H t) = principalFinResidueLabel B h H q t := by
  funext j a
  simp only [principalResidueLabel, principalFinTuplePoint, zeroScalarFinPoint,
    principalFinResidueLabel, Int.cast_natCast]

theorem principalFinResidueCell_mass (q : ℕ)
    (r : PrincipalTupleIndex B h → Option Empty → ZMod q) :
    letI : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
    (FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).mass (principalFinResidueCell B h H q r) =
      (principalTupleWeights (α := Empty) B h H hH).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)) := by
  let : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
  rw [← FiniteProbabilityWeights.mean_indicator, ← FiniteProbabilityWeights.mean_indicator,
    FiniteProbabilityWeights.uniform_mean, principalTupleWeights_fin_mean]
  simp only [principalFinResidueCell, Finset.mem_filter, Finset.mem_univ, true_and,
    principalFinTuplePoint_residue]

variable (L step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hsubset : ∀ j, integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))

omit [Fintype D] [DecidableEq D] [∀ index, Fintype (B index)]
  [∀ index, DecidableEq (B index)] in
theorem containedProgressionTupleMap_finPoint [Fintype D] [DecidableEq D]
    [∀ index, Fintype (B index)] [∀ index, DecidableEq (B index)]
    (t : ∀ j, Fin (H j)) :
    containedProgressionTupleMap B h L H step start hL hsubset (principalFinTuplePoint B h H t) =
      principalAffineIntervalPoint B h L H step start hinside t := by
  funext j a
  apply Subtype.ext
  have hc : IntegerScalarCube (H j) (fun a => (principalFinTuplePoint B h H t j a : ℤ)) := by
    intro row
    have he : row = ∅ := Subsingleton.elim _ _
    simp only [he, integerScalarCubeValue, Finset.sum_empty, add_zero,
      principalFinTuplePoint, zeroScalarFinPoint]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩
  rw [containedProgressionTupleMap,
    containedProgressionCubeMap_value Empty _ _ _ _ _ _ _ hc]
  cases a with
  | none => rfl
  | some a => exact isEmptyElim a

theorem principalAffineIntervalLaw_eq_contained :
    principalAffineIntervalLaw B h L H step start hinside hH =
      (principalTupleWeights (α := Empty) B h H hH).fiberLaw
        (containedProgressionTupleMap B h L H step start hL hsubset) := by
  have he (f : PrincipalIntegerTuples B h Empty L → ℝ) :
      (principalAffineIntervalLaw B h L H step start hinside hH).mean f =
        ((principalTupleWeights (α := Empty) B h H hH).fiberLaw
          (containedProgressionTupleMap B h L H step start hL hsubset)).mean f := by
    rw [principalAffineIntervalLaw_mean, FiniteProbabilityWeights.fiberLaw_mean,
      principalTupleWeights_fin_mean]
    apply Finset.expect_congr rfl
    intro t _
    rw [containedProgressionTupleMap_finPoint B h H L step start hL hinside hsubset]
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  simpa [FiniteProbabilityWeights.mean] using he (fun y => if y = z then 1 else 0)

theorem containedSupportedProgressionLaw_fin_condition_mean
    (q : ℕ) (r : PrincipalTupleIndex B h → Option Empty → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := Empty) B h H hH).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (f : PrincipalIntegerTuples B h Empty L → ℝ) :
    letI : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
    (containedSupportedProgressionLaw B h L H step start hL hH hsubset q r hcell).mean f =
      ((FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).condition
        (principalFinResidueCell B h H q r)
        (by rw [principalFinResidueCell_mass B h H hH]; exact hcell)).mean
          (fun t => f (principalAffineIntervalPoint B h L H step start hinside t)) := by
  let : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
  rw [containedSupportedProgressionLaw, FiniteProbabilityWeights.fiberLaw_mean,
    FiniteProbabilityWeights.condition_mean, FiniteProbabilityWeights.condition_mean,
    principalFinResidueCell_mass B h H hH, principalTupleWeights_fin_mean,
    FiniteProbabilityWeights.uniform_mean]
  congr 1
  apply Finset.expect_congr rfl
  intro t _
  simp only [principalFinResidueCell, Finset.mem_filter, Finset.mem_univ, true_and,
    principalFinTuplePoint_residue,
    containedProgressionTupleMap_finPoint B h H L step start hL hinside hsubset]

theorem containedSupportedProgressionLaw_fin_condition_complexMean
    (q : ℕ) (r : PrincipalTupleIndex B h → Option Empty → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := Empty) B h H hH).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    letI : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
    (containedSupportedProgressionLaw B h L H step start hL hH hsubset q r hcell).complexMean f =
      ((FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).condition
        (principalFinResidueCell B h H q r)
        (by rw [principalFinResidueCell_mass B h H hH]; exact hcell)).complexMean
          (fun t => f (principalAffineIntervalPoint B h L H step start hinside t)) := by
  let : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
  apply Complex.ext
  · simpa only [FiniteProbabilityWeights.complexMean_re] using
      containedSupportedProgressionLaw_fin_condition_mean B h H hH L step start hL hinside hsubset
        q r hcell (fun z => (f z).re)
  · simpa only [FiniteProbabilityWeights.complexMean_im] using
      containedSupportedProgressionLaw_fin_condition_mean B h H hH L step start hL hinside hsubset
        q r hcell (fun z => (f z).im)

theorem containedSupportedProgressionLaw_eq_fin_condition
    (q : ℕ) (r : PrincipalTupleIndex B h → Option Empty → ZMod q)
    (hcell : 0 < (principalTupleWeights (α := Empty) B h H hH).mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
    letI : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
    containedSupportedProgressionLaw B h L H step start hL hH hsubset q r hcell =
      ((FiniteProbabilityWeights.uniform (∀ j, Fin (H j))).condition
        (principalFinResidueCell B h H q r)
        (by rw [principalFinResidueCell_mass B h H hH]; exact hcell)).finitePushforward
          (principalAffineIntervalPoint B h L H step start hinside) := by
  let : Nonempty (∀ j, Fin (H j)) := ⟨fun j => ⟨0, hH j⟩⟩
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  have hm := containedSupportedProgressionLaw_fin_condition_mean
    B h H hH L step start hL hinside hsubset q r hcell (fun y => if y = z then 1 else 0)
  simp only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hm
  rw [hm]
  unfold FiniteProbabilityWeights.finitePushforward
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : principalAffineIntervalPoint B h L H step start hinside t = z <;> simp [ht]

theorem principalAffineIntervalPoint_residue (q : ℕ) (t : ∀ j, Fin (H j))
    (r : PrincipalTupleIndex B h → Option Empty → ZMod q)
    (ht : t ∈ principalFinResidueCell B h H q r) :
    ∀ j a, ((principalAffineIntervalPoint B h L H step start hinside t j a : ℤ) : ZMod q) =
      (start j : ZMod q) + (step j : ZMod q) * r j a := by
  have hr := (Finset.mem_filter.mp ht).2
  intro j a
  have hj := congrFun (congrFun hr j) a
  simp only [principalFinResidueLabel] at hj
  simp only [principalAffineIntervalPoint_value, Int.cast_add, Int.cast_mul, Int.cast_natCast, hj]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (start : PrincipalTupleIndex B h → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < L j)
variable (hH : ∀ j, 0 < H j) (P : D → Prop)

theorem principalAffineIntervalLaw_partition_complexMean
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalLaw (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean (fun u =>
      (principalAffineIntervalLaw (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
        (principalAxisLength (fun d => ¬P d) step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean (fun v => f (principalAxisJoin P u v))) := by
  have hL (j : PrincipalTupleIndex B h) : 0 < L j := by
    have hi := hinside j ⟨0, hH j⟩
    omega
  have hsubset (j : PrincipalTupleIndex B h) :
      integerProgressionSupport (start j) (step j : ℤ) (H j) ⊆
        Finset.Ico (0 : ℤ) (L j : ℤ) :=
    integerProgressionSupport_subset_of_fin _ _ _ _ (hinside j)
  rw [principalAffineIntervalLaw_eq_contained B h H hH L step start hL hinside hsubset,
    FiniteProbabilityWeights.fiberLaw_complexMean,
    principalTupleWeights_partition P H hH]
  rw [principalAffineIntervalLaw_eq_contained
    (fun d : {d // P d} => B d.val) (fun d => h d.val)
    (principalAxisLength P H) (fun j => hH ⟨j.1.val, j.2⟩)
    (principalAxisLength P L) (principalAxisLength P step) (fun j => start ⟨j.1.val, j.2⟩)
    (fun j => hL ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
    (fun j => hsubset ⟨j.1.val, j.2⟩),
    FiniteProbabilityWeights.fiberLaw_complexMean]
  apply congrArg _
  funext u
  rw [principalAffineIntervalLaw_eq_contained
    (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
    (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)
    (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) step)
    (fun j => start ⟨j.1.val, j.2⟩)
    (fun j => hL ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
    (fun j => hsubset ⟨j.1.val, j.2⟩),
    FiniteProbabilityWeights.fiberLaw_complexMean]
  apply congrArg _
  funext v
  rw [containedProgressionTupleMap_axisJoin]

theorem principalAffineIntervalAxisLaw_complexMean_restricted
    (f : PrincipalAxisTuples (α := Empty) P L → ℂ) :
    (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean f =
      (principalAffineIntervalLaw (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean f := by
  rw [principalAffineIntervalAxisLaw, FiniteProbabilityWeights.complexMean_finitePushforward,
    principalAffineIntervalLaw_partition_complexMean B h L H step start hinside hH P]
  simp only [principalAxisRestrict_join_left, FiniteProbabilityWeights.complexMean_const]

theorem principalAffineIntervalAxisLaw_eq_restricted :
    principalAffineIntervalAxisLaw B h L H step start hinside hH P =
      principalAffineIntervalLaw (fun d : {d // P d} => B d.val) (fun d => h d.val)
        (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩) := by
  apply FiniteProbabilityWeights.toPMF_injective
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [FiniteProbabilityWeights.toPMF_toReal, FiniteProbabilityWeights.toPMF_toReal]
  have he := congrArg Complex.re
    (principalAffineIntervalAxisLaw_complexMean_restricted B h L H step start hinside hH P
      (fun y => if y = z then 1 else 0))
  simpa [FiniteProbabilityWeights.complexMean] using he

theorem principalAffineIntervalLaw_axis_complexMean
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean (fun u =>
      (principalAffineIntervalLaw (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
        (principalAxisLength (fun d => ¬P d) step)
        (fun j => start ⟨j.1.val, j.2⟩) (fun j t => hinside ⟨j.1.val, j.2⟩ t)
        (fun j => hH ⟨j.1.val, j.2⟩)).complexMean (fun v => f (principalAxisJoin P u v))) := by
  rw [principalAffineIntervalAxisLaw_eq_restricted]
  exact principalAffineIntervalLaw_partition_complexMean B h L H step start hinside hH P f

theorem principalAffineIntervalLaw_axis_contained_complexMean
    (hL : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      0 < principalAxisLength (fun d => ¬P d) L j)
    (hsubset : ∀ j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val),
      integerProgressionSupport (start ⟨j.1.val, j.2⟩)
        (principalAxisLength (fun d => ¬P d) step j : ℤ)
        (principalAxisLength (fun d => ¬P d) H j) ⊆
      Finset.Ico (0 : ℤ) (principalAxisLength (fun d => ¬P d) L j : ℤ))
    (f : PrincipalIntegerTuples B h Empty L → ℂ) :
    (principalAffineIntervalLaw B h L H step start hinside hH).complexMean f =
      (principalAffineIntervalAxisLaw B h L H step start hinside hH P).complexMean (fun u =>
      (principalTupleWeights (α := Empty) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
        (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)).complexMean
        (fun v => f (principalAxisJoin P u
          (containedProgressionTupleMap (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
            (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) H)
            (principalAxisLength (fun d => ¬P d) step) (fun j => start ⟨j.1.val, j.2⟩)
            hL hsubset v)))) := by
  rw [principalAffineIntervalLaw_axis_complexMean B h L H step start hinside hH P]
  apply congrArg _
  funext u
  rw [principalAffineIntervalLaw_eq_contained
    (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)
    (principalAxisLength (fun d => ¬P d) H) (fun j => hH ⟨j.1.val, j.2⟩)
    (principalAxisLength (fun d => ¬P d) L) (principalAxisLength (fun d => ¬P d) step)
    (fun j => start ⟨j.1.val, j.2⟩) hL (fun j t => hinside ⟨j.1.val, j.2⟩ t) hsubset,
    FiniteProbabilityWeights.fiberLaw_complexMean]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : ℕ) (hM : 0 < M)
variable (r : PrincipalTupleIndex
  (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
variable (hsize : ∀ d, (Fintype.card α + 1) * M ≤
  principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S) d)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedLongResidueWeights_support_label
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv : (allocatedLongResidueWeights B U b S M hM r hsize).weight v ≠ 0) :
    principalResidueLabel M v = r := by
  have h := principalResidueWeights_support (fun a : {a // ¬grid a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) lengths
    (fun j => allocatedPrincipalSides_pos B U b S ⟨j.1.val, j.2⟩) M hM r hsize v hv
  funext j i
  exact congrFun h ⟨j.1, j.2.1, j.2.2, i⟩

include hM hsize in
theorem exists_allocatedLongResidueReference :
    ∃ v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides, principalResidueLabel M v = r := by
  obtain ⟨v, hv, _⟩ := principalResidue_positive_witness (fun a : {a // ¬grid a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) lengths
    (fun j => allocatedPrincipalSides_pos B U b S ⟨j.1.val, j.2⟩) M hM hsize r
  exact ⟨v, hv⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))

omit [Fintype α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedNonkernelJetMatrix_residue_of_label
    (v w : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S)) (M : ℕ)
    (hlabel : principalResidueLabel M v = principalResidueLabel M w) (j : Fin m) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) M =
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j w) M :=
  integerMappedJetMatrix_residue (allocatedNonkernelExponent B j)
    (partitionedPrincipalInput (allocatedGridAxis (I := I) U b S.value) (fun g a => (g, a)))
    (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u))
    (rows j) (principalTupleIntegers v) (principalTupleIntegers w) M
    (congrArg principalTupleResidues hlabel)

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedLongResidueWeights_reference_matrix
    (M : ℕ) (hM : 0 < M)
    (label : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
    (hsize : ∀ t, (Fintype.card α+1)*M ≤ (principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S)) t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
    (hv₀ : principalResidueLabel M v₀ = label)
    (period : ℕ) (hdiv : period ∣ M)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))
    (hr : ∀ v, (allocatedLongResidueWeights B U b S M hM label hsize).weight v ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) period = residue j) :
    ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) period = residue j := by
  classical
  let p := allocatedLongResidueWeights B U b S M hM label hsize
  have hex : ∃ v, p.weight v ≠ 0 := by
    by_contra! h
    have ht := p.total
    simp only [h, Finset.sum_const_zero] at ht
    exact zero_ne_one ht
  obtain ⟨v, hv⟩ := hex
  have hl := (allocatedLongResidueWeights_support_label B U b S M hM label hsize v hv).trans hv₀.symm
  intro j
  have he := integerResidueMatrix_reduce _ _ hdiv
    (allocatedNonkernelJetMatrix_residue_of_label B U b S x rows u v v₀ M hl j)
  exact he.symm.trans (hr v hv j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
variable (u u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α) (q : ℕ)
variable (hu : principalResidueLabel q u = principalResidueLabel q u₀)
variable (hv : principalResidueLabel q v = principalResidueLabel q v₀)

include hu hv

theorem allocatedNonkernelJetMatrix_residue_both (j : Fin m) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) q =
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u₀ rows j v₀) q := by
  apply integerMappedJetMatrix_residue_both
  · funext z
    cases z with
    | inl z => rfl
    | inr z => exact congrFun (congrArg principalTupleResidues hu) z
  · exact congrArg principalTupleResidues hv

theorem allocatedPartitionedJetMatrix_residue_both (j : Fin m) :
    integerResidueMatrix (allocatedPartitionedJetMatrix B U b S x u v rows j) q =
      integerResidueMatrix (allocatedPartitionedJetMatrix B U b S x u₀ v₀ rows j) q := by
  apply integerMappedJetMatrix_residue_both
  · funext z
    cases z with
    | inl z => rfl
    | inr z => exact congrFun (congrArg principalTupleResidues hu) z
  · exact congrArg principalTupleResidues hv

variable [∀ j, Fintype (O j)]

theorem allocatedPartitionedJetMatrix_image_eq_of_residue_both
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) (j : Fin m) :
    (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range =
      (allocatedPartitionedJetMatrix B U b S x u₀ v₀ rows j).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ q
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u₀ v₀ rows j)
  · exact allocatedPartitionedJetMatrix_residue_both B U b S x u u₀ v v₀ rows q hu hv j

theorem allocatedPhysicalDeckJet_law_eq_of_residue_both
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) rows d) := by
  have hr (j : Fin m) :
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
      ← allocatedPartitionedJetMatrix_eq_physical B U b S x u₀ v₀ rows j]
    exact allocatedPartitionedJetMatrix_image_eq_of_residue_both B U b S x u u₀ v v₀ rows q hu hv hperiod j
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q) _ _ rows _ _ hr d)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) ((allocatedPrincipalSides B U b S) j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) sides H step c
  (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "longLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) sides H step c
  (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (fun a => ¬grid a)
variable (u u₀ : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (hu : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u ≠ 0) (hu₀ : ((containedSupportedProgressionAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell (allocatedGridAxis (I := I) U b S.value))).weight u₀ ≠ 0)
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

include hu hu₀

theorem allocatedSupportedSlicedNonkernel_residue_constant (j : Fin m) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v₀) q =
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u₀ rows j v₀) q := by
  have hlabel := containedSupportedProgressionAxisLaw_residue_eq B (layerSamplerDegree I n) sides H step c
    (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid u u₀ hu hu₀
  exact allocatedNonkernelJetMatrix_residue_both B U b S x u u₀ v₀ v₀ rows q hlabel rfl j

variable [∀ j, Fintype (O j)]

theorem allocatedSupportedSlicedDeck_law_constant
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u₀ v₀))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u₀ v₀)) rows d) := by
  have hlabel := containedSupportedProgressionAxisLaw_residue_eq B (layerSamplerDegree I n) sides H step c
    (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid u u₀ hu hu₀
  exact allocatedPhysicalDeckJet_law_eq_of_residue_both B U b S x u u₀ v₀ v₀ rows q hlabel rfl Q hperiod d

end Erdos3.VectorPolynomial

end

end OAI
