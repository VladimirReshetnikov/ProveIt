/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
import OAI.Combinatorics.Progressions.Lattices.WeightedScalarResidueCell
import OAI.Combinatorics.Progressions.Probability.LowerMassWeightNormalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_successive_localized_cells
    {X Y E G C D T U : Type*} [Fintype X] [Fintype Y]
    [Fintype T] [Nonempty T] [Fintype U] [Nonempty U]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (a : X → E) (b : Y → G) (cell : C → T → E) (other : D → U → G)
    (Good : C → Prop) (OtherGood : D → Prop) {ζ η θ : ℝ}
    (first : ∀ H : E → ℂ, (∀ x, ‖H x‖ ≤ 1) →
      ζ ≤ ‖p.complexMean (fun x => H (a x))‖ →
      ∃ c, Good c ∧ η ≤ ‖𝔼 t, H (cell c t)‖)
    (second : ∀ H : G → ℂ, (∀ y, ‖H y‖ ≤ 1) →
      η ≤ ‖q.complexMean (fun y => H (b y))‖ →
      ∃ d, OtherGood d ∧ θ ≤ ‖𝔼 u, H (other d u)‖)
    (F : E → G → ℂ) (hF : ∀ x y, ‖F x y‖ ≤ 1)
    (hbias : ζ ≤ ‖p.complexMean (fun x => q.complexMean (fun y => F (a x) (b y)))‖) :
    ∃ c d, Good c ∧ OtherGood d ∧ θ ≤ ‖𝔼 t, 𝔼 u, F (cell c t) (other d u)‖ := by
  have hfirst (x : E) : ‖q.complexMean (fun y => F x (b y))‖ ≤ 1 :=
    (q.norm_complexMean_le_mean_norm _).trans
      ((q.mean_mono (fun y => hF x (b y))).trans_eq (q.mean_const 1))
  obtain ⟨c, hc, hmiddle⟩ := first (fun x => q.complexMean (fun y => F x (b y))) hfirst hbias
  have hsecond (y : G) : ‖𝔼 t, F (cell c t) y‖ ≤ 1 :=
    (RCLike.norm_expect_le (K := ℂ)).trans
      ((Finset.expect_le_expect (fun t _ => hF (cell c t) y)).trans_eq (Fintype.expect_const 1))
  have hm : η ≤ ‖q.complexMean (fun y => 𝔼 t, F (cell c t) (b y))‖ := by
    rwa [q.complexMean_finset_expect]
  obtain ⟨d, hd, hlast⟩ := second (fun y => 𝔼 t, F (cell c t) y) hsecond hm
  refine ⟨c, d, hc, hd, ?_⟩
  rwa [Finset.expect_comm] at hlast

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_finite_family_localized_cells (n : ℕ)
    (X E C T : Fin n → Type*) [∀ i, Fintype (X i)]
    [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)]
    (p : ∀ i, FiniteProbabilityWeights (X i)) (a : ∀ i, X i → E i)
    (cell : ∀ i, C i → T i → E i) (Good : ∀ i, C i → Prop)
    (τ : Fin (n + 1) → ℝ)
    (localize : ∀ i (H : E i → ℂ), (∀ x, ‖H x‖ ≤ 1) →
      τ i.castSucc ≤ ‖(p i).complexMean (fun x => H (a i x))‖ →
      ∃ c, Good i c ∧ τ i.succ ≤ ‖𝔼 t, H (cell i c t)‖)
    (F : (∀ i, E i) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi p).complexMean (fun x => F (fun i => a i (x i)))‖) :
    ∃ c : ∀ i, C i, (∀ i, Good i (c i)) ∧
      τ (Fin.last n) ≤ ‖𝔼 t : ∀ i, T i, F (fun i => cell i (c i) (t i))‖ := by
  induction n with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    rw [expect_empty_tuple]
    rw [FiniteProbabilityWeights.complexMean_empty_tuple] at hbias
    have he : (fun i : Fin 0 => a i (Fin.elim0 i)) =
        (fun i : Fin 0 => cell i (Fin.elim0 i) (Fin.elim0 i)) := Subsingleton.elim _ _
    rw [he] at hbias
    exact hbias
  | succ n ih =>
    let q := FiniteProbabilityWeights.pi (fun i : Fin n => p i.succ)
    let H (x : E 0) := q.complexMean (fun y => F (Fin.cons x (fun i => a i.succ (y i))))
    have hH (x : E 0) : ‖H x‖ ≤ 1 :=
      (q.norm_complexMean_le_mean_norm _).trans
        ((q.mean_mono (fun y => hF _)).trans_eq (q.mean_const 1))
    have hfirst : τ (0 : Fin (n + 1)).castSucc ≤
        ‖(p 0).complexMean (fun x => H (a 0 x))‖ := by
      rw [FiniteProbabilityWeights.complexMean_pi_fin_cons] at hbias
      simp only [dependent_fin_cons_map] at hbias
      exact hbias
    obtain ⟨c0, hc0, hmiddle⟩ := localize 0 H hH hfirst
    let G (y : ∀ i : Fin n, E i.succ) := 𝔼 t : T 0, F (Fin.cons (cell 0 c0 t) y)
    have hG (y) : ‖G y‖ ≤ 1 :=
      (RCLike.norm_expect_le (K := ℂ)).trans
        ((Finset.expect_le_expect (fun t _ => hF _)).trans_eq (Fintype.expect_const 1))
    have htail : (τ (Fin.succ 0)) ≤ ‖q.complexMean (fun y => G (fun i => a i.succ (y i)))‖ := by
      rw [q.complexMean_finset_expect]
      exact hmiddle
    obtain ⟨c, hc, hlast⟩ := ih
      (fun i => X i.succ) (fun i => E i.succ) (fun i => C i.succ) (fun i => T i.succ)
      (fun i => p i.succ) (fun i => a i.succ) (fun i => cell i.succ) (fun i => Good i.succ)
      (fun i => τ i.succ) (fun i => localize i.succ) G hG htail
    refine ⟨Fin.cons c0 c, ?_, ?_⟩
    · intro i
      exact Fin.cases hc0 (fun j => hc j) i
    · have he (t0 : T 0) (t : ∀ i : Fin n, T i.succ) :
          (fun i => cell i (Fin.cons c0 c i) (Fin.cons t0 t i)) =
          Fin.cons (cell 0 c0 t0) (fun i => cell i.succ (c i) (t i)) := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have hmean : (𝔼 t : ∀ i : Fin (n + 1), T i,
          F (fun i => cell i (Fin.cons c0 c i) (t i))) =
          𝔼 t : ∀ i : Fin n, T i.succ, G (fun i => cell i.succ (c i) (t i)) := by
        rw [expect_dependent_fin_cons]
        simp only [he]
        exact Finset.expect_comm _ _ _
      rw [hmean]
      exact hlast

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

structure ScalarCubeLocalizationData (I : Type*) [Fintype I] [DecidableEq I] where
  length : ℕ
  modulusBound : ℕ
  length_pos : 0 < length
  modulus : Option I → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ modulusBound
  size : (Fintype.card I + 1) * modulusBound ≤ length
  gridSmall : scalarCubeGridBoundaryConstant I * ((modulusBound : ℝ) / length) <
    volume.real (scalarCubeDomain I)
  transitionBound : ℝ≥0
  transition_lipschitz : LipschitzWith transitionBound Real.smoothTransition
  radius : ℝ≥0
  radius_pos : 0 < radius
  weight : (Option I → ℝ) → ℝ
  weightBound : ℝ≥0
  weightLipschitz : ℝ≥0
  weightBound_pos : 0 < weightBound
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ weightBound
  weight_lipschitz : LipschitzWith weightLipschitz weight
  normalized : (scalarCubeResidueWeights I length modulusBound length_pos modulus residue
    modulus_pos modulus_le size).mean (fun z => weight (fun i => (z i : ℝ) / length)) = 1
  mesh : ℝ
  mesh_pos : 0 < mesh
  mesh_le_one : mesh ≤ 1
  meshLarge : 2 * (modulusBound : ℝ) ≤ mesh * length
  margin : ((Fintype.card I : ℝ) + 1) * mesh < radius

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def baseLaw : FiniteProbabilityWeights (IntegerScalarCubeBox I d.length) :=
  scalarCubeResidueWeights I d.length d.modulusBound d.length_pos d.modulus d.residue
    d.modulus_pos d.modulus_le d.size

noncomputable def point (z : IntegerScalarCubeBox I d.length) : Option I → ℝ :=
  fun i => (z i : ℝ) / d.length

noncomputable def source : FiniteProbabilityWeights (IntegerScalarCubeBox I d.length) :=
  d.baseLaw.reweight (fun z => d.weight (d.point z)) (fun z => (d.weight_range (d.point z)).1) d.normalized

noncomputable def cellLength : ℕ := residueCellLength d.mesh d.length d.modulusBound

noncomputable def cellCount : ℕ := residueCellCount d.length d.cellLength

noncomputable def cell (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) : Option I → ℝ :=
  residueCellPosition d.length d.cellLength d.cellCount d.modulus d.residue k t

noncomputable def error (η : ℝ) : ℝ :=
  d.weightBound * scalarCubeResidueCutoffBudget I d.transitionBound d.radius d.length d.modulusBound +
    paddedResidueDensityCap I d.modulusBound *
      (((d.weightLipschitz : ℝ) + d.weightBound * scalarCubeCutoffLipschitzConstant I d.transitionBound d.radius) *
        d.mesh + d.weightBound * η)

theorem cellLength_pos : 0 < d.cellLength :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).1

theorem cellLength_lower : d.mesh * d.length / (2 * d.modulusBound) ≤ (d.cellLength : ℝ) :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).2.2.1

theorem cellCount_pos : 0 < d.cellCount := residueCellCount_pos d.length d.cellLength

theorem source_complexMean (F : (Option I → ℝ) → ℂ) :
    d.source.complexMean (fun z => F (d.point z)) =
      d.baseLaw.complexMean (fun z => (d.weight (d.point z) : ℂ) * F (d.point z)) :=
  d.baseLaw.reweight_complexMean _ _ _ _

theorem localize {ζ η : ℝ} (hη : 0 < η) (herror : d.error η ≤ ζ)
    (F : (Option I → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : ζ ≤ ‖d.source.complexMean (fun z => F (d.point z))‖) :
    ∃ k : Option I → Fin d.cellCount,
      (∀ t : Option I → Fin d.cellLength, d.cell k t ∈ scalarCubeDomain I) ∧
      η ≤ ‖𝔼 t : Option I → Fin d.cellLength, F (d.cell k t)‖ := by
  rw [d.source_complexMean] at hbias
  exact scalarCubeResidue_weighted_interior_cell I d.length d.modulusBound d.length_pos
    d.modulus d.residue d.modulus_pos d.modulus_le d.size d.gridSmall
    d.transitionBound d.transition_lipschitz d.radius_pos d.weight d.weightBound_pos
    d.weight_range d.weight_lipschitz d.mesh_pos d.mesh_le_one hη d.meshLarge d.margin
    herror F hF hbias

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

structure NormalizedScalarCubeSource (I : Type*) [Fintype I] [DecidableEq I] where
  length : ℕ
  modulusBound : ℕ
  length_pos : 0 < length
  modulus : Option I → ℕ
  residue : ∀ i, ZMod (modulus i)
  modulus_pos : ∀ i, 0 < modulus i
  modulus_le : ∀ i, modulus i ≤ modulusBound
  size : (Fintype.card I + 1) * modulusBound ≤ length
  weight : (Option I → ℝ) → ℝ
  weightBound : ℝ≥0
  weightLipschitz : ℝ≥0
  weightBound_pos : 0 < weightBound
  weight_range : ∀ x, 0 ≤ weight x ∧ weight x ≤ weightBound
  weight_lipschitz : LipschitzWith weightLipschitz weight
  normalized : (scalarCubeResidueWeights I length modulusBound length_pos modulus residue
    modulus_pos modulus_le size).mean (fun z => weight (fun i => (z i : ℝ) / length)) = 1

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)

noncomputable def baseLaw : FiniteProbabilityWeights (IntegerScalarCubeBox I s.length) :=
  scalarCubeResidueWeights I s.length s.modulusBound s.length_pos s.modulus s.residue
    s.modulus_pos s.modulus_le s.size

noncomputable def source : FiniteProbabilityWeights (IntegerScalarCubeBox I s.length) :=
  s.baseLaw.reweight (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized

end NormalizedScalarCubeSource

theorem scalarCube_weight_normalizer_bounds (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) {B K : ℝ≥0} (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B)
    (hLip : LipschitzWith K w) (hmass : ∫ x, w x ∂scalarCubeMeasure I = 1)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L)
    (htest : 2 * M * scalarCubeRiemannAllowance I B K ≤ L) :
    1 / 2 ≤ (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L)) ∧
    (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L)) ≤ 3 / 2 := by
  have hbound (x) : ‖w x‖ ≤ B := by
    rw [Real.norm_of_nonneg (hw x).1]
    exact (hw x).2
  have h := scalarCubeResidueWeights_riemann_of_length I L M hL m res hm hmM hsize w
    hLip B.coe_nonneg hbound (by norm_num : (0 : ℝ) < 1 / 2) hlarge (by
      convert htest using 1
      ring)
  rw [hmass] at h
  have hh := abs_le.mp h
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3.ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def integerOffset (k : Option I → Fin d.cellCount) : Option I → ℝ :=
  fun i => (d.residue i).val + (d.modulus i : ℝ) * ((d.cellLength : ℝ) * (k i).val - d.length)

theorem point_scale (z : IntegerScalarCubeBox I d.length) (i : Option I) :
    (d.length : ℝ) * d.point z i = (z i : ℝ) := by
  have hL : (d.length : ℝ) ≠ 0 := by exact_mod_cast d.length_pos.ne'
  change (d.length : ℝ) * ((z i : ℝ) / d.length) = _
  exact mul_div_cancel₀ _ hL

theorem cell_scale (k : Option I → Fin d.cellCount) (t : Option I → Fin d.cellLength) :
    (fun i => (d.length : ℝ) * d.cell k t i) =
      fun i => d.integerOffset k i + (d.modulus i : ℝ) * (t i).val := by
  have hL : (d.length : ℝ) ≠ 0 := by exact_mod_cast d.length_pos.ne'
  have he := residueCellIntegerPoint_normalized d.length d.cellLength d.cellCount d.modulus d.residue k t
  funext i
  have hi := congrFun he i
  change (residueCellIntegerPoint d.length d.cellLength d.cellCount d.modulus d.residue k t i : ℝ) /
    d.length = d.cell k t i at hi
  calc
    _ = (residueCellIntegerPoint d.length d.cellLength d.cellCount d.modulus d.residue k t i : ℝ) := by
      rw [← hi]
      exact mul_div_cancel₀ _ hL
    _ = _ := by
      simp only [residueCellIntegerPoint, scalarResidueGridPoint, integerOffset,
        Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      ring

end Erdos3.ScalarCubeLocalizationData

end

section

namespace Erdos3

open scoped BigOperators

theorem scalarCubeFamily_localize {n : ℕ} (I : Fin n → Type*)
    [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (d : ∀ j, ScalarCubeLocalizationData (I j)) (τ : Fin (n + 1) → ℝ)
    (hτ : ∀ j : Fin n, 0 < τ j.succ) (herror : ∀ j, (d j).error (τ j.succ) ≤ τ j.castSucc)
    (F : (∀ j, Option (I j) → ℝ) → ℂ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hbias : τ 0 ≤ ‖(FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
      (fun z => F (fun j => (d j).point (z j)))‖) :
    ∃ k : ∀ j, Option (I j) → Fin (d j).cellCount,
      (∀ j (t : Option (I j) → Fin (d j).cellLength), (d j).cell (k j) t ∈ scalarCubeDomain (I j)) ∧
      τ (Fin.last n) ≤ ‖𝔼 t : ∀ j, Option (I j) → Fin (d j).cellLength,
        F (fun j => (d j).cell (k j) (t j))‖ := by
  let : ∀ j, Nonempty (Option (I j) → Fin (d j).cellLength) :=
    fun j => ⟨fun _ => ⟨0, (d j).cellLength_pos⟩⟩
  exact exists_finite_family_localized_cells n
    (fun j => IntegerScalarCubeBox (I j) (d j).length) (fun j => Option (I j) → ℝ)
    (fun j => Option (I j) → Fin (d j).cellCount) (fun j => Option (I j) → Fin (d j).cellLength)
    (fun j => (d j).source) (fun j => (d j).point) (fun j => (d j).cell)
    (fun j k => ∀ t, (d j).cell k t ∈ scalarCubeDomain (I j)) τ
    (fun j H hH h => (d j).localize (hτ j) (herror j) H hH h) F hF hbias

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

noncomputable def lengthLoss : ℝ := 2 * d.modulusBound / d.mesh

theorem lengthLoss_pos : 0 < d.lengthLoss := by
  have hM : 0 < d.modulusBound := (d.modulus_pos none).trans_le (d.modulus_le none)
  exact div_pos (by positivity) d.mesh_pos

theorem length_le_lengthLoss_mul_cellLength :
    (d.length : ℝ) ≤ d.lengthLoss * d.cellLength := by
  have hM : (0 : ℝ) < d.modulusBound := by
    exact_mod_cast (d.modulus_pos none).trans_le (d.modulus_le none)
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d.modulusBound)).mp d.cellLength_lower
  unfold lengthLoss
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ d.mesh_pos).mpr
  nlinarith

end ScalarCubeLocalizationData

theorem reciprocal_product_le_of_lengths {J : Type*} [Fintype J]
    (a b c : J → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hlen : ∀ j, a j ≤ c j * b j) {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, b j) ≤ Q * (∏ j, c j) / (∏ j, a j) := by
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => (ha j).le) (fun j _ => hlen j)
  rw [Finset.prod_mul_distrib] at hprod
  apply (div_le_div_iff₀ (Finset.prod_pos (fun j _ => hb j)) (Finset.prod_pos (fun j _ => ha j))).mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hQ

theorem scalarCubeCell_inverse_product {J : Type*} [Fintype J]
    (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (d : ∀ j, ScalarCubeLocalizationData (I j)) {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, ((d j).cellLength : ℝ)) ≤
      Q * (∏ j, (d j).lengthLoss) / (∏ j, ((d j).length : ℝ)) := by
  apply reciprocal_product_le_of_lengths _ _ _ _ _ (fun j => (d j).length_le_lengthLoss_mul_cellLength) hQ
  · intro j
    exact_mod_cast (d j).length_pos
  · intro j
    exact_mod_cast (d j).cellLength_pos

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def normalizedScalarCubeSourceOfMeanLower (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (B T η : ℝ≥0) (hB : 0 < B) (hη : 0 < η)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
    (hZ : (η : ℝ) ≤ (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L))) : NormalizedScalarCubeSource I := by
  let p := scalarCubeResidueWeights I L M hL m res hm hmM hsize
  let Z := p.mean (fun z => w (fun i => (z i : ℝ) / L))
  have hZ0 : 0 < Z := (show (0 : ℝ) < η from hη).trans_le hZ
  exact {
    length := L, modulusBound := M, length_pos := hL
    modulus := m, residue := res, modulus_pos := hm, modulus_le := hmM, size := hsize
    weight := fun x => w x / Z, weightBound := B / η, weightLipschitz := T / η
    weightBound_pos := div_pos hB hη
    weight_range := weight_div_range_of_lower w hη hZ hw
    weight_lipschitz := weight_div_lipschitz_of_lower w hη hZ hLip
    normalized := finite_mean_div_self p _ hZ0.ne' }

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def normalizedScalarCubeSourceOfWeight (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (B K : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith K w)
    (hZ : 1 / 2 ≤ (scalarCubeResidueWeights I L M hL m res hm hmM hsize).mean
      (fun z => w (fun i => (z i : ℝ) / L))) : NormalizedScalarCubeSource I := by
  let p := scalarCubeResidueWeights I L M hL m res hm hmM hsize
  let Z := p.mean (fun z => w (fun i => (z i : ℝ) / L))
  have hZ0 : 0 < Z := by dsimp only [Z, p]; linarith
  exact {
    length := L, modulusBound := M, length_pos := hL
    modulus := m, residue := res, modulus_pos := hm, modulus_le := hmM, size := hsize
    weight := fun x => w x / Z, weightBound := 2 * B, weightLipschitz := 2 * K
    weightBound_pos := mul_pos (by norm_num) hB
    weight_range := fun x => by
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using normalized_weight_range w hw hZ x
    weight_lipschitz := normalized_weight_lipschitz w hLip hZ
    normalized := finite_mean_div_self p _ hZ0.ne' }

noncomputable def normalizedScalarCubeSourceOfContinuousWeight (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (res : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L)
    (w : (Option I → ℝ) → ℝ) (B K : ℝ≥0) (hB : 0 < B)
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith K w)
    (hmass : ∫ x, w x ∂scalarCubeMeasure I = 1)
    (hlarge : 2 * scalarCubeGridBoundaryConstant I * M / volume.real (scalarCubeDomain I) ≤ L)
    (htest : 2 * M * scalarCubeRiemannAllowance I B K ≤ L) : NormalizedScalarCubeSource I :=
  normalizedScalarCubeSourceOfWeight I L M hL m res hm hmM hsize w B K hB hw hLip
    (scalarCube_weight_normalizer_bounds I L M hL m res hm hmM hsize w hw hLip hmass hlarge htest).1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def coefficientResidueSet (L m : ℕ) (r : ZMod m) : Finset ℤ :=
  (Finset.Ico 0 (L : ℤ)).filter (fun z => (z : ZMod m) = r)

noncomputable def emptyScalarCubeResidueEquiv (L : ℕ) (m : Option Empty → ℕ)
    (r : ∀ i, ZMod (m i)) :
    ↥((integerScalarCubeSet Empty L) ∩ scalarCubeResidueSet Empty L m r) ≃
      ↥(coefficientResidueSet L (m none) (r none)) where
  toFun x := by
    have hx := Finset.mem_inter.mp x.property
    have h0 := ((mem_integerScalarCubeSet L x.val).mp hx.1) ∅
    simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h0
    exact ⟨x.val none, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr h0,
      (mem_scalarCubeResidueSet L m r x.val).mp hx.2 none⟩⟩
  invFun z := by
    have hz := Finset.mem_filter.mp z.property
    have hb := Finset.mem_Ico.mp hz.1
    let x : IntegerScalarCubeBox Empty L := fun _ =>
      ⟨z.val, Finset.mem_Ico.mpr ⟨by omega, hb.2⟩⟩
    refine ⟨x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply (mem_integerScalarCubeSet L x).mpr
      intro t
      have ht : t = ∅ := Subsingleton.elim _ _
      simpa only [ht, integerScalarCubeValue, Finset.sum_empty, add_zero] using hb
    · apply (mem_scalarCubeResidueSet L m r x).mpr
      intro i
      cases i with
      | none => exact hz.2
      | some a => exact a.elim
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    cases i with
    | none => rfl
    | some a => exact a.elim
  right_inv z := by apply Subtype.ext; rfl

namespace NormalizedScalarCubeSource

abbrev CoefficientDomain (s : NormalizedScalarCubeSource Empty) :=
  ↥(coefficientResidueSet s.length (s.modulus none) (s.residue none))

theorem baseLaw_coefficient_mean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℝ) :
    s.baseLaw.mean (fun x => f (x none : ℤ)) = 𝔼 z : s.CoefficientDomain, f z := by
  unfold baseLaw
  rw [scalarCubeResidueWeights_mean]
  exact Fintype.expect_equiv (emptyScalarCubeResidueEquiv s.length s.modulus s.residue) _ _ (fun _ => rfl)

theorem weight_empty_coordinate (s : NormalizedScalarCubeSource Empty)
    (x : IntegerScalarCubeBox Empty s.length) :
    s.weight (fun i => (x i : ℝ) / s.length) = s.weight (fun _ => (x none : ℝ) / s.length) := by
  congr 1
  funext i
  cases i with
  | none => rfl
  | some a => exact a.elim

noncomputable def coefficientDensity (s : NormalizedScalarCubeSource Empty) (z : s.CoefficientDomain) : ℝ :=
  s.weight (fun _ => (z.val : ℝ) / s.length)

theorem coefficientDensity_nonneg (s : NormalizedScalarCubeSource Empty) (z : s.CoefficientDomain) :
    0 ≤ s.coefficientDensity z := (s.weight_range _).1

theorem coefficientDensity_mean_one (s : NormalizedScalarCubeSource Empty) :
    (𝔼 z : s.CoefficientDomain, s.coefficientDensity z) = 1 := by
  have he := s.baseLaw_coefficient_mean (fun z => s.weight (fun _ => (z : ℝ) / s.length))
  have hn : s.baseLaw.mean (fun x => s.weight (fun _ => (x none : ℝ) / s.length)) = 1 := by
    have h := s.normalized
    simpa only [s.weight_empty_coordinate, baseLaw] using h
  exact he.symm.trans hn

noncomputable def coefficientWeights (s : NormalizedScalarCubeSource Empty) :
    FiniteProbabilityWeights s.CoefficientDomain :=
  FiniteProbabilityWeights.ofDensity s.coefficientDensity s.coefficientDensity_nonneg s.coefficientDensity_mean_one

theorem source_coefficient_mean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℝ) :
    s.source.mean (fun x => f (x none : ℤ)) = (s.coefficientWeights).mean (fun z => f z) := by
  apply (FiniteProbabilityWeights.reweight_mean s.baseLaw
    (fun z => s.weight (fun i => (z i : ℝ) / s.length))
    (fun z => (s.weight_range (fun i => (z i : ℝ) / s.length)).1) s.normalized
    (fun x => f (x none : ℤ))).trans
  rw [coefficientWeights, FiniteProbabilityWeights.ofDensity_mean]
  simp only [s.weight_empty_coordinate, coefficientDensity]
  exact s.baseLaw_coefficient_mean (fun z => s.weight (fun _ => (z : ℝ) / s.length) * f z)

theorem source_coefficient_complexMean (s : NormalizedScalarCubeSource Empty) (f : ℤ → ℂ) :
    s.source.complexMean (fun x => f (x none : ℤ)) = (s.coefficientWeights).complexMean (fun z => f z) := by
  apply Complex.ext
  · rw [FiniteProbabilityWeights.complexMean_re, FiniteProbabilityWeights.complexMean_re]
    exact s.source_coefficient_mean (fun z => (f z).re)
  · rw [FiniteProbabilityWeights.complexMean_im, FiniteProbabilityWeights.complexMean_im]
    exact s.source_coefficient_mean (fun z => (f z).im)

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

structure FiniteCoefficientSlice where
  length : ℕ
  offset : ℤ
  stride : ℤ
  modulus : ℕ
  residue : ZMod modulus

namespace FiniteCoefficientSlice

abbrev Domain (s : FiniteCoefficientSlice) :=
  ↥(coefficientResidueSet s.length s.modulus s.residue)

def value (s : FiniteCoefficientSlice) (x : s.Domain) : ℤ := s.offset + s.stride * x.val

def radius (s : FiniteCoefficientSlice) : ℕ := s.offset.natAbs + s.stride.natAbs * s.length

theorem value_abs_le (s : FiniteCoefficientSlice) (x : s.Domain) : |s.value x| ≤ (s.radius : ℤ) := by
  have hx := Finset.mem_Ico.mp (Finset.mem_filter.mp x.property).1
  have habs : |x.val| ≤ (s.length : ℤ) := by
    rw [abs_of_nonneg hx.1]
    exact hx.2.le
  unfold value radius
  simp only [Nat.cast_add, Nat.cast_mul, Int.natCast_natAbs]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left habs (abs_nonneg _)))

end FiniteCoefficientSlice

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def coefficientSliceEmbedding (s : FiniteCoefficientSlice) (P : Set ℤ) (hstride : s.stride ≠ 0)
    (hP : ∀ x : s.Domain, s.value x ∈ P) : s.Domain ↪ P where
  toFun x := ⟨s.value x, hP x⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change s.offset + s.stride * x.val = s.offset + s.stride * y.val at he
    exact mul_left_cancel₀ hstride (add_left_cancel he)

noncomputable def coefficientSliceEvent (s : FiniteCoefficientSlice) (P : Set ℤ) [Fintype P] : Finset P :=
  Finset.univ.filter (fun x => ∃ z : ℤ, 0 ≤ z ∧ z < s.length ∧ (z : ZMod s.modulus) = s.residue ∧
    s.offset + s.stride * z = x.val)

theorem coefficientSliceEmbedding_range (s : FiniteCoefficientSlice) (P : Set ℤ) [Fintype P]
    (hstride : s.stride ≠ 0) (hP : ∀ x : s.Domain, s.value x ∈ P) :
    finiteEmbeddingRange (coefficientSliceEmbedding s P hstride hP) = coefficientSliceEvent s P := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
    subst x
    have hs := Finset.mem_filter.mp y.property
    have hi := Finset.mem_Ico.mp hs.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.val, hi.1, hi.2, hs.2, rfl⟩
  · intro hx
    obtain ⟨z, hz0, hzL, hzr, hzx⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_map.mpr ⟨⟨z, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hz0, hzL⟩, hzr⟩⟩,
      Finset.mem_univ _, ?_⟩
    exact Subtype.ext hzx

noncomputable def conditionCoefficientSlice (s : FiniteCoefficientSlice) (P : Set ℤ) [Fintype P]
    (hstride : s.stride ≠ 0) (hP : ∀ x : s.Domain, s.value x ∈ P)
    (w : ℤ → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x : s.Domain, w (s.value x)) :
    FiniteProbabilityWeights P :=
  FiniteProbabilityWeights.conditionAlongEmbedding (fun x => w x.val) (fun x => hw x.val)
    (coefficientSliceEmbedding s P hstride hP) hmass

theorem conditionCoefficientSlice_complexMean (s : FiniteCoefficientSlice) (P : Set ℤ) [Fintype P]
    (hstride : s.stride ≠ 0) (hP : ∀ x : s.Domain, s.value x ∈ P)
    (w : ℤ → ℝ) (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x : s.Domain, w (s.value x)) (f : ℤ → ℂ) :
    (conditionCoefficientSlice s P hstride hP w hw hmass).complexMean (fun x => f x.val) =
      (FiniteProbabilityWeights.ofPositiveWeights (fun x : s.Domain => w (s.value x))
        (fun x => hw (s.value x)) hmass).complexMean (fun x => f (s.value x)) :=
  FiniteProbabilityWeights.conditionAlongEmbedding_complexMean _ _
    (coefficientSliceEmbedding s P hstride hP) hmass _

theorem uniform_condition_coefficientSlice_mean (s : FiniteCoefficientSlice) (P : Set ℤ) [Fintype P]
    [Nonempty P] (hstride : s.stride ≠ 0) (hP : ∀ x : s.Domain, s.value x ∈ P)
    (hmass : 0 < (FiniteProbabilityWeights.uniform P).mass
      (finiteEmbeddingRange (coefficientSliceEmbedding s P hstride hP))) (f : ℤ → ℝ) :
    ((FiniteProbabilityWeights.uniform P).condition
      (finiteEmbeddingRange (coefficientSliceEmbedding s P hstride hP)) hmass).mean (fun x => f x.val) =
        𝔼 x : s.Domain, f (s.value x) := by
  refine (FiniteProbabilityWeights.uniform_condition_embedding_mean
    (coefficientSliceEmbedding s P hstride hP) hmass (fun x : P => f x.val)).trans ?_
  apply Finset.expect_congr
  · apply Finset.ext
    intro x
    exact ⟨fun _ => Finset.mem_univ x, fun _ => Finset.mem_univ x⟩
  · intro x _
    rfl

end Erdos3

end

end OAI
