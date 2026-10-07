import OAI.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
import OAI.Combinatorics.Progressions.Linear.ContainedSupportedProgressionKernels

namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

include hq in
theorem principalSupportedResidue_restrict
    (hsize : ∀ j : PrincipalTupleIndex BP hP, (Fintype.card α + 1) * q ≤ H (embed j)) :
    (conditioned).toPMF.map (principalAxisRestrict P) =
      (principalResidueWeights BP hP (principalAxisLength P H) hHP q hq rP hsize).toPMF := by
  have hinj : Function.Injective embed := by
    intro a b hab
    rcases a with ⟨⟨a, ha⟩, av⟩
    rcases b with ⟨⟨b, hb⟩, bv⟩
    cases hab
    rfl
  have hm := FiniteProbabilityWeights.pi_condition_positive_fiber_marginal
    (fun j => integerScalarCubeWeights α (H j) (hH j))
    (fun j (z : IntegerScalarCubeBox α (H j)) a => ((z a : ℤ) : ZMod q)) r hcell embed hinj
  have hres := principalResidueWeights_eq_condition BP hP (principalAxisLength P H) hHP q hq rP hsize
  have hcond := principalSupportedResidueWeights_eq_pi BP hP (principalAxisLength P H) hHP q rP
    (principalResidueCell_mass_pos BP hP (principalAxisLength P H) hHP q hq rP hsize)
  have hpmf := congrArg (fun p : FiniteProbabilityWeights
    (PrincipalIntegerTuples BP hP α (principalAxisLength P H)) => p.toPMF) (hres.trans hcond)
  have hpi := FiniteProbabilityWeights.toPMF_pi (principalSupportedCoordinateWeights BP hP
    (principalAxisLength P H) hHP q rP (principalResidueCell_mass_pos BP hP (principalAxisLength P H) hHP q hq rP hsize))
  exact hm.trans (hpmf.trans hpi).symm

include hq in
theorem containedSupportedProgressionLaw_restrict
    (hsize : ∀ j : PrincipalTupleIndex BP hP, (Fintype.card α + 1) * q ≤ H (embed j)) :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).toPMF.map
        (principalAxisRestrict P) =
      (containedProgressionResidueLaw BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) hHP
        (fun j => hsubset (embed j)) q hq rP hsize).toPMF := by
  have hm := congrArg (fun p => p.map (containedProgressionTupleMap BP hP
      (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
      (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j))))
    (principalSupportedResidue_restrict B h H hH q hq r hcell P hsize)
  rw [PMF.map_comp] at hm
  simp only [containedSupportedProgressionLaw, containedProgressionResidueLaw,
    FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
  refine Eq.trans ?_ hm
  apply congrArg (fun f : PrincipalIntegerTuples B h α H → PrincipalAxisTuples (α := α) P L =>
    (conditioned).toPMF.map f)
  funext y j
  rfl

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

noncomputable def containedSupportedProgressionAxisLaw :
    FiniteProbabilityWeights (PrincipalAxisTuples (α := α) P L) :=
  (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP =>
    principalSupportedCoordinateWeights B h H hH q r hcell (embed j))).fiberLaw
      (containedProgressionTupleMap BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))

theorem containedSupportedProgressionLaw_partition (f : PrincipalIntegerTuples B h α L → ℂ) :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean f =
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean (fun u =>
        (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let w := principalSupportedCoordinateWeights B h H hH q r hcell
  let map := containedProgressionTupleMap (α := α) B h L H step c hL hsubset
  let wL := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j))
  let wR := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun a : {a // ¬P a} => B a.val) (fun a => h a.val) => w ⟨j.1.val,j.2⟩)
  let mapL := containedProgressionTupleMap (α := α) BP hP (principalAxisLength P L) (principalAxisLength P H)
    (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j))
  let mapR := containedProgressionTupleMap (α := α) (fun a : {a // ¬P a} => B a.val) (fun a => h a.val)
    (principalAxisLength (fun a => ¬P a) L) (principalAxisLength (fun a => ¬P a) H)
    (principalAxisLength (fun a => ¬P a) step) (fun j => c ⟨j.1.val,j.2⟩)
    (fun j => hL ⟨j.1.val,j.2⟩) (fun j => hsubset ⟨j.1.val,j.2⟩)
  have hjoin (u : PrincipalAxisTuples (α := α) P H) (v : PrincipalAxisTuples (α := α) (fun a => ¬P a) H) :
      map (principalAxisJoin P u v) = principalAxisJoin P (mapL u) (mapR v) := by
    funext j
    rcases j with ⟨a, bv⟩
    by_cases ha : P a <;>
      simp only [map, mapL, mapR, containedProgressionTupleMap, principalAxisJoin, ha, ↓reduceDIte] <;> rfl
  have hpart := principalCoordinateWeights_partition P H w (fun y => f (map y))
  have hpart' := hpart.trans (congrArg (fun g => wL.complexMean g) (funext (fun u =>
    congrArg (fun g => wR.complexMean g) (funext (fun v => congrArg f (hjoin u v))))))
  have hleft := (conditioned).fiberLaw_complexMean map f
  have hright := wL.fiberLaw_complexMean mapL (fun u =>
    (wR.fiberLaw mapR).complexMean (fun v => f (principalAxisJoin P u v)))
  have hinner (u : PrincipalAxisTuples (α := α) P L) :=
    wR.fiberLaw_complexMean mapR (fun v => f (principalAxisJoin P u v))
  have hright' := hright.trans (congrArg (fun g => wL.complexMean g)
    (funext (fun u => hinner (mapL u))))
  exact hleft.trans ((congrArg (fun p => p.complexMean (fun y => f (map y)))
    (principalSupportedResidueWeights_eq_pi B h H hH q r hcell)).trans (hpart'.trans hright'.symm))

include hq in
theorem containedSupportedProgressionAxisLaw_eq_of_size
    (hsize : ∀ j : PrincipalTupleIndex BP hP, (Fintype.card α + 1) * q ≤ H (embed j)) :
    containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P =
      containedProgressionResidueLaw BP hP (principalAxisLength P L) (principalAxisLength P H)
        (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) hHP
        (fun j => hsubset (embed j)) q hq rP hsize := by
  have hres := principalResidueWeights_eq_condition BP hP (principalAxisLength P H) hHP q hq rP hsize
  have hcond := principalSupportedResidueWeights_eq_pi BP hP (principalAxisLength P H) hHP q rP
    (principalResidueCell_mass_pos BP hP (principalAxisLength P H) hHP q hq rP hsize)
  exact congrArg (fun w => w.fiberLaw (containedProgressionTupleMap BP hP
    (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
    (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))) (hres.trans hcond).symm

theorem containedSupportedProgressionAxisLaw_cube_support
    (u : PrincipalAxisTuples (α := α) P L)
    (hu : (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0)
    (j : PrincipalTupleIndex BP hP) :
    IntegerScalarCube (principalAxisLength P L j) (fun a => (u j a : ℤ)) := by
  apply FiniteProbabilityWeights.fiberLaw_support _ _
    (fun u => IntegerScalarCube (principalAxisLength P L j) (fun a => (u j a : ℤ))) _ u hu
  intro z _
  exact containedProgressionCubeMap_cube α _ _ _ _ _ _ (z j)

theorem containedSupportedProgressionLaw_partition_comparison
    (f : PrincipalIntegerTuples B h α L → ℂ) (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f (principalAxisJoin P u v)) - g u‖ ≤ E) :
    ‖(containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean f -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  rw [containedSupportedProgressionLaw_partition B h L H step c hL hH hsubset q r hcell P f]
  exact ((containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).norm_complexMean_sub_le
    _ _ (fun _ => E) hpoint).trans_eq (FiniteProbabilityWeights.mean_const _ E)

theorem containedSupportedProgressionLaw_axis_marginal :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).toPMF.map
      (principalAxisRestrict P) =
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).toPMF := by
  let w := principalSupportedCoordinateWeights B h H hH q r hcell
  have hinj : Function.Injective embed := by
    intro a b hab
    rcases a with ⟨⟨a, ha⟩, av⟩
    rcases b with ⟨⟨b, hb⟩, bv⟩
    cases hab
    rfl
  have hraw := FiniteProbabilityWeights.pi_condition_positive_fiber_marginal
    (fun j => integerScalarCubeWeights α (H j) (hH j))
    (fun j (z : IntegerScalarCubeBox α (H j)) a => ((z a : ℤ) : ZMod q)) r hcell embed hinj
  have hpi := FiniteProbabilityWeights.toPMF_pi (fun j : PrincipalTupleIndex BP hP => w (embed j))
  have hraw' : (conditioned).toPMF.map (principalAxisRestrict P) =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j))).toPMF := hraw.trans hpi.symm
  have hm := congrArg (fun p => p.map (containedProgressionTupleMap BP hP
      (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
      (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))) hraw'
  rw [PMF.map_comp] at hm
  have hout := FiniteProbabilityWeights.toPMF_fiberLaw
    (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j)))
    (containedProgressionTupleMap BP hP (principalAxisLength P L) (principalAxisLength P H)
      (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))
  simp only [containedSupportedProgressionLaw, containedSupportedProgressionAxisLaw,
    FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
  refine Eq.trans ?_ (hm.trans hout.symm)
  apply congrArg (fun f : PrincipalIntegerTuples B h α H → PrincipalAxisTuples (α := α) P L =>
    (conditioned).toPMF.map f)
  funext y j
  rfl

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "rP" => (fun j : PrincipalTupleIndex BP hP => r (embed j))
local notation "hHP" => (fun j : PrincipalTupleIndex BP hP => hH (embed j))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem containedSupportedProgressionLaw_integral_comparison
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → PrincipalIntegerTuples B h α L → ℂ) (hf : ∀ y, Integrable (fun p => f p y) μ)
    (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(∫ p, (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f p (principalAxisJoin P u v)) ∂μ) - g u‖ ≤ E) :
    ‖(∫ p, (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean (f p) ∂μ) -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  rw [FiniteProbabilityWeights.integral_complexMean _ μ f hf]
  apply containedSupportedProgressionLaw_partition_comparison B h L H step c hL hH hsubset q r hcell P
  intro u hu
  have he := (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).integral_complexMean
    μ (fun p v => f p (principalAxisJoin P u v)) (fun v => hf (principalAxisJoin P u v))
  exact he ▸ hpoint u hu

end Erdos3

end

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)

theorem principalTupleWeights_weight_pos_of_cube (y : PrincipalIntegerTuples B h α L)
    (hy : ∀ j, IntegerScalarCube (L j) (fun a => (y j a : ℤ))) :
    0 < (principalTupleWeights B h L hL).weight y := by
  apply Finset.prod_pos
  intro j _
  apply (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (y j)).mpr
  refine ⟨(mem_integerScalarCubeSet (L j) (y j)).mpr (hy j), ?_⟩
  let : Nonempty (IntegerScalarCubeBox α (L j)) := ⟨y j⟩
  change 0 < (Fintype.card (IntegerScalarCubeBox α (L j)) : ℝ)⁻¹
  positivity

theorem principalResidueCell_pos_of_cube (q : ℕ) (y : PrincipalIntegerTuples B h α L)
    (hy : ∀ j, IntegerScalarCube (L j) (fun a => (y j a : ℤ))) :
    0 < (principalTupleWeights B h L hL).mass
      (Finset.univ.filter (fun z => principalResidueLabel q z = principalResidueLabel q y)) := by
  apply lt_of_lt_of_le (principalTupleWeights_weight_pos_of_cube B h L hL y hy)
  exact Finset.single_le_sum (fun z _ => (principalTupleWeights B h L hL).nonneg z)
    (by simp : y ∈ Finset.univ.filter (fun z => principalResidueLabel q z = principalResidueLabel q y))

omit [Fintype D] [DecidableEq D] [DecidableEq α]
  [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] in
theorem principalAxisJoin_cube (P : D → Prop) [DecidablePred P]
    (u : PrincipalAxisTuples (α := α) P L) (v : PrincipalAxisTuples (α := α) (fun a => ¬P a) L)
    (hu : ∀ j, IntegerScalarCube (principalAxisLength P L j) (fun a => (u j a : ℤ)))
    (hv : ∀ j, IntegerScalarCube (principalAxisLength (fun a => ¬P a) L j) (fun a => (v j a : ℤ))) :
    ∀ j, IntegerScalarCube (L j) (fun a => (principalAxisJoin P u v j a : ℤ)) := by
  rintro ⟨a, bv⟩
  by_cases ha : P a
  · simpa only [principalAxisJoin, ha, ↓reduceDIte, principalAxisLength] using hu ⟨⟨a, ha⟩, bv⟩
  · simpa only [principalAxisJoin, ha, ↓reduceDIte, principalAxisLength] using hv ⟨⟨a, ha⟩, bv⟩

end Erdos3

end

end OAI
