/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.ControlledCoordinateLifts
import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization

namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ) (f : Basis ι ℚ (L ⧸ F.layer d 2))

noncomputable def realHorizontalMap :
    (F.layer d 1).baseChange ℝ →ₗ[ℝ] ℝ ⊗[ℚ] F.HigherHorizontal d :=
  ((F.higherHorizontalMk d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer d 1)).symm.toLinearMap

@[simp] theorem realHorizontalMap_baseChange (v : ℝ ⊗[ℚ] F.layer d 1) :
    F.realHorizontalMap d (realificationSubmoduleEquiv (F.layer d 1) v) =
      (F.higherHorizontalMk d).baseChange ℝ v := by
  exact congrArg ((F.higherHorizontalMk d).baseChange ℝ)
    ((realificationSubmoduleEquiv (F.layer d 1)).symm_apply_apply v)

theorem realHigherHorizontalCoordinates_map (x : (F.layer d 1).baseChange ℝ) :
    F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d x) =
      realRationalCoordinateEquiv ((F.ambientHorizontalCoordinates d f).baseChange ℝ x.val) := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective x
  rw [F.realHorizontalMap_baseChange]
  simp only [realificationSubmoduleEquiv_coe]
  induction v using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realHigherHorizontalCoordinates_mem (x : ℝ ⊗[ℚ] F.HigherHorizontal d) :
    F.realHigherHorizontalCoordinates d f x ∈
      realRationalCoordinateSpan ((F.layer d 1).map (F.ambientHorizontalCoordinates d f)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨v, rfl⟩ := F.higherHorizontalMk_surjective d x
    exact ⟨a ⊗ₜ[ℚ] F.ambientHorizontalCoordinates d f v.val,
      Submodule.tmul_mem_baseChange_of_mem a ⟨v.val, v.property, rfl⟩, rfl⟩
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

theorem exists_controlled_horizontal_lifts
    {μ κ σ : Type*} [Fintype μ] [Fintype κ]
    (b : Basis μ ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = F.layer d 1)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hvH : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hfH : ∀ j i, RationalHeightLE (F.ambientHorizontalCoordinates d f (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hμ : (Fintype.card μ : ℝ) ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) ∧ l ∣ m ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x y z : ℝ ⊗[ℚ] F.HigherHorizontal d)
        (a q : ι → ℝ), F.realHigherHorizontalCoordinates d f (x - y - z) = a + q →
        ‖a‖ ≤ Real.exp p / monomialScale T α → q ∈ realDenominatorGrid l →
        ∃ E Q : (F.layer d 1).baseChange ℝ,
          F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d E) = a ∧
          F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d Q) = q ∧
          x - y - F.realHorizontalMap d E - F.realHorizontalMap d Q = z ∧
          ‖(b.baseChange ℝ).equivFun E.val‖ ≤
            Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p) / monomialScale T α ∧
          (b.baseChange ℝ).equivFun Q.val ∈ realDenominatorGrid m := by
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_controlled_coordinate_lifts b (F.layer d 1) v hv
    (F.ambientHorizontalCoordinates d f) hH hl hvH hfH hp hμ hι hκ hHp hlp T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x y z a q heq ha hq
  have hsum := F.realHigherHorizontalCoordinates_mem d f (x - y - z)
  rw [heq] at hsum
  obtain ⟨E, Q, hE, hQ, hEa, hQq, hslow, hgrid⟩ := hsolve α hα a q hsum ha hq
  let E' : (F.layer d 1).baseChange ℝ := ⟨E, hE⟩
  let Q' : (F.layer d 1).baseChange ℝ := ⟨Q, hQ⟩
  have hEa' : F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d E') = a :=
    (F.realHigherHorizontalCoordinates_map d f E').trans hEa
  have hQq' : F.realHigherHorizontalCoordinates d f (F.realHorizontalMap d Q') = q :=
    (F.realHigherHorizontalCoordinates_map d f Q').trans hQq
  refine ⟨E', Q', hEa', hQq', ?_, hslow, hgrid⟩
  apply F.realHigherHorizontalCoordinates_injective d f
  simp only [map_sub] at heq ⊢
  rw [hEa', hQq']
  linear_combination heq

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_firstProjection_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (J : Submodule ℚ (Fin 4 → V)) {x : ℝ ⊗[ℚ] (Fin 4 → V)}
    (hx : x ∈ J.baseChange ℝ) :
    (LinearMap.proj (0 : Fin 4)).baseChange ℝ x ∈ (fourFirstProjection J).baseChange ℝ := by
  rw [fourFirstProjection, realification_map]
  exact ⟨x, hx, rfl⟩

namespace DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

noncomputable def realFourLayerComponent (k : Fin 4) :
    (F.fourHorizontalLayer d).baseChange ℝ →ₗ[ℝ] (F.layer d 1).baseChange ℝ :=
  (((LinearMap.proj k).baseChange ℝ).comp ((F.fourHorizontalLayer d).baseChange ℝ).subtype).codRestrict
    ((F.layer d 1).baseChange ℝ) (fun x => baseChange_mem_of_mapsTo
      (F.fourHorizontalLayer d) (F.layer d 1) (LinearMap.proj k)
      (fun v hv => (F.mem_fourHorizontalLayer d v).mp hv k) x.property)

@[simp] theorem realFourLayerComponent_coe (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    (F.realFourLayerComponent d k x).val = (LinearMap.proj k).baseChange ℝ x.val := rfl

theorem realFourLayerComponent_horizontal (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) :
    (LinearMap.proj k).baseChange ℝ (F.realFourHorizontalMap d x) =
      F.realHorizontalMap d (F.realFourLayerComponent d k x) := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.fourHorizontalLayer d)).surjective x
  rw [F.realFourHorizontalMap_baseChange]
  induction y using TensorProduct.inductionOn with
  | tmul a v =>
    let u : F.layer d 1 := ⟨v.val k, (F.mem_fourHorizontalLayer d v.val).mp v.property k⟩
    have heq : F.realFourLayerComponent d k
        (realificationSubmoduleEquiv (F.fourHorizontalLayer d) (a ⊗ₜ[ℚ] v)) =
        realificationSubmoduleEquiv (F.layer d 1) (a ⊗ₜ[ℚ] u) := by
      apply Subtype.ext
      rfl
    rw [heq, F.realHorizontalMap_baseChange]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourLayerComponent_norm_bound {ι : Type*} [Fintype ι] (b : Basis ι ℚ L)
    (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hx : ∀ j, |((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x.val j| ≤ B) :
    ‖(b.baseChange ℝ).equivFun (F.realFourLayerComponent d k x).val‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  change |(b.baseChange ℝ).repr ((LinearMap.proj k).baseChange ℝ x.val) i| ≤ B
  rw [real_pi_projection_coordinates]
  exact hx ⟨k, i⟩

theorem realFourLayerComponent_grid {ι : Type*} (b : Basis ι ℚ L)
    (k : Fin 4) (x : (F.fourHorizontalLayer d).baseChange ℝ) (l : ℕ)
    (hx : (fun j => ((Pi.basis (fun _ : Fin 4 => b)).baseChange ℝ).repr x.val j) ∈ realDenominatorGrid l) :
    (fun i => (b.baseChange ℝ).repr (F.realFourLayerComponent d k x).val i) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => z ⟨k, i⟩, ?_⟩
  funext i
  exact (congrFun hz ⟨k, i⟩).trans (congrArg (fun a : ℝ => (l : ℝ) * a)
    (real_pi_projection_coordinates b x.val k i).symm)

end DegreeRankLieFiltration
end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem realHorizontalMap_surjective (d : ℕ) :
    Function.Surjective (F.realHorizontalMap d) := by
  intro x
  obtain ⟨v, hv⟩ := LinearMap.baseChange_surjective ℝ (F.higherHorizontalMk_surjective d) x
  exact ⟨realificationSubmoduleEquiv (F.layer d 1) v,
    (F.realHorizontalMap_baseChange d v).trans hv⟩

theorem realHorizontalMap_ambient (d : ℕ) (x : (F.layer d 1).baseChange ℝ) :
    (F.higherHorizontalAmbient d).baseChange ℝ (F.realHorizontalMap d x) =
      (F.layer d 2).mkQ.baseChange ℝ x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective x
  rw [F.realHorizontalMap_baseChange]
  simp only [realificationSubmoduleEquiv_coe]
  induction v using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add v w hv hw => simp only [map_add, hv, hw]

theorem realHorizontalMap_eq (d : ℕ) (x y : (F.layer d 1).baseChange ℝ) :
    F.realHorizontalMap d x = F.realHorizontalMap d y ↔
      x.val - y.val ∈ (F.layer d 2).baseChange ℝ := by
  rw [← realification_mkQ_eq_zero_iff, map_sub, sub_eq_zero]
  constructor
  · intro h
    rw [← F.realHorizontalMap_ambient d x, ← F.realHorizontalMap_ambient d y, h]
  · intro h
    apply F.real_higherHorizontalAmbient_injective d
    rwa [F.realHorizontalMap_ambient, F.realHorizontalMap_ambient]

noncomputable def realHorizontalRepresentative (d : ℕ)
    (x : ℝ ⊗[ℚ] F.HigherHorizontal d) : (F.layer d 1).baseChange ℝ := by
  classical
  exact if x = 0 then 0 else Classical.choose (F.realHorizontalMap_surjective d x)

@[simp] theorem realHorizontalRepresentative_zero (d : ℕ) :
    F.realHorizontalRepresentative d 0 = 0 := by
  classical
  simp only [realHorizontalRepresentative, ↓reduceIte]

theorem realHorizontalMap_representative (d : ℕ) (x : ℝ ⊗[ℚ] F.HigherHorizontal d) :
    F.realHorizontalMap d (F.realHorizontalRepresentative d x) = x := by
  classical
  by_cases hx : x = 0
  · simp only [hx, realHorizontalRepresentative_zero, map_zero]
  · simpa only [realHorizontalRepresentative, ite_eq_right hx] using
      Classical.choose_spec (F.realHorizontalMap_surjective d x)

noncomputable def realHorizontalTreeValue (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, ℝ ⊗[ℚ] F.HigherHorizontal (d i)) : ℝ ⊗[ℚ] L :=
  lieTreeEval (fun i => (F.realHorizontalRepresentative (d i) (v i)).val) a

theorem realHorizontalTreeValue_map (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, (F.layer (d i) 1).baseChange ℝ) :
    F.realHorizontalTreeValue d a (fun i => F.realHorizontalMap (d i) (v i)) =
      lieTreeEval (fun i => (v i).val) a := by
  apply F.realification.top_lieTreeEval_congr _ _ d
    (fun i => (F.realHorizontalRepresentative (d i) (F.realHorizontalMap (d i) (v i))).property)
    (fun i => (v i).property) _ a hd hr
  intro i
  exact (F.realHorizontalMap_eq (d i) _ _).mp (F.realHorizontalMap_representative _ _)

theorem realHorizontalTreeValue_zero_of_leaf (d : I → ℕ) (a : FreeMagma I)
    (v : ∀ i, ℝ ⊗[ℚ] F.HigherHorizontal (d i)) {i : I}
    (hi : i ∈ lieTreeSupport a) (hv : v i = 0) : F.realHorizontalTreeValue d a v = 0 := by
  apply lieTreeEval_eq_zero_of_leaf _ a hi
  simp only [hv, realHorizontalRepresentative_zero, ZeroMemClass.coe_zero]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem rankLayerCoefficient_tensor_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.layer (Finsupp.weight w α) 1).subtype.baseChange ℝ
        ((F.rankLayerCoefficient w α).baseChange ℝ x) =
      coefficients (F.associatedDegree.realAdaptedPolynomialMap w x) α := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
      F.rankLayerCoefficient_coe, F.associatedDegree.realAdaptedPolynomialMap_coefficient_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem rankLayerCoefficient_tensor_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.associatedDegree.adaptedLieSubalgebra w) :
    (F.higherHorizontalMk (Finsupp.weight w α)).baseChange ℝ
        ((F.rankLayerCoefficient w α).baseChange ℝ x) =
      (F.higherHorizontalCoefficient w α).baseChange ℝ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem nativeHorizontalCoefficientHom_eq_realHorizontalMap (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (v : (F.layer (Finsupp.weight w α) 1).baseChange ℝ)
    (hv : v.val = coefficients g.log α) :
    Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) =
      F.realHorizontalMap (Finsupp.weight w α) v := by
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  have heq : v = realificationSubmoduleEquiv (F.layer (Finsupp.weight w α) 1)
      ((F.rankLayerCoefficient w α).baseChange ℝ x) := by
    apply Subtype.ext
    rw [realificationSubmoduleEquiv_coe, F.rankLayerCoefficient_tensor_coe, hv, hlog]
  rw [F.nativeHorizontalCoefficientHom_tensor hs b ω hF w α g x hlog, heq,
    F.realHorizontalMap_baseChange, F.rankLayerCoefficient_tensor_horizontal]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (d : ℕ)

def horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d)) : Submodule ℚ L :=
  (U.comap (F.higherHorizontalMk d)).map (F.layer d 1).subtype

theorem horizontalPreimage_le (U : Submodule ℚ (F.HigherHorizontal d)) :
    F.horizontalPreimage d U ≤ F.layer d 1 := by
  rintro x ⟨v, _, rfl⟩
  exact v.property

theorem horizontalPreimage_mono {U V : Submodule ℚ (F.HigherHorizontal d)} (h : U ≤ V) :
    F.horizontalPreimage d U ≤ F.horizontalPreimage d V :=
  Submodule.map_mono (Submodule.comap_mono h)

theorem mem_horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d))
    (v : F.layer d 1) :
    v.val ∈ F.horizontalPreimage d U ↔ F.higherHorizontalMk d v ∈ U := by
  constructor
  · rintro ⟨w, hw, h⟩
    have he : w = v := Subtype.ext h
    exact he ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem horizontalPreimage_coordinates {ι : Type*} [Fintype ι]
    (f : Basis ι ℚ (L ⧸ F.layer d 2)) (U : Submodule ℚ (F.HigherHorizontal d)) :
    F.horizontalPreimage d U = F.layer d 1 ⊓
      (U.map (F.higherHorizontalCoordinates d f)).comap (F.ambientHorizontalCoordinates d f) := by
  ext x
  constructor
  · intro hx
    have hxl := F.horizontalPreimage_le d U hx
    exact ⟨hxl, ⟨F.higherHorizontalMk d ⟨x, hxl⟩,
      (F.mem_horizontalPreimage d U ⟨x, hxl⟩).mp hx, rfl⟩⟩
  · rintro ⟨hxl, y, hy, he⟩
    apply (F.mem_horizontalPreimage d U ⟨x, hxl⟩).mpr
    have he' : y = F.higherHorizontalMk d ⟨x, hxl⟩ :=
      F.higherHorizontalCoordinates_injective d f he
    exact he' ▸ hy

theorem mem_real_horizontalPreimage (U : Submodule ℚ (F.HigherHorizontal d))
    (v : (F.layer d 1).baseChange ℝ) :
    v.val ∈ (F.horizontalPreimage d U).baseChange ℝ ↔
      F.realHorizontalMap d v ∈ U.baseChange ℝ := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer d 1)).surjective v
  rw [F.realHorizontalMap_baseChange, realificationSubmoduleEquiv_coe,
    horizontalPreimage, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := realification_subtype_injective (F.layer d 1) he
    exact hyx ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem native_coefficient_mem_horizontalPreimage {σ ι : Type*} (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w)
    (U : Submodule ℚ (F.HigherHorizontal (Finsupp.weight w α))) :
    coefficients g.log α ∈ (F.horizontalPreimage (Finsupp.weight w α) U).baseChange ℝ ↔
      Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) ∈
        U.baseChange ℝ := by
  obtain ⟨x, hx⟩ := F.associatedDegree.realAdaptedPolynomialTensor_surjective w b ω hF
    (⟨g.log, g.property⟩ : F.associatedDegree.realification.adaptedLieSubalgebra w)
  have hlog : g.log = F.associatedDegree.realAdaptedPolynomialMap w x :=
    (congrArg Subtype.val hx).symm
  let v := realificationSubmoduleEquiv (F.layer (Finsupp.weight w α) 1)
    ((F.rankLayerCoefficient w α).baseChange ℝ x)
  have hv : v.val = coefficients g.log α := by
    rw [hlog]
    exact F.rankLayerCoefficient_tensor_coe w α x
  rw [F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α g v hv,
    ← hv, F.mem_real_horizontalPreimage]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

theorem polynomialOrbit_coefficient_mem_rank_one (w : σ → ℕ) (α : σ →₀ ℕ)
    (g : F.associatedDegree.realification.PolynomialOrbit w) :
    coefficients g.log α ∈ (F.layer (Finsupp.weight w α) 1).baseChange ℝ := by
  have h := (F.associatedDegree.realification.adapted_iff_coefficients w g.log).mp g.adapted α
  change coefficients g.log α ∈ (F.layer (Finsupp.weight w α) 0).baseChange ℝ at h
  rwa [F.rank_zero_eq_one] at h

theorem polynomialOrbit_log_mul_mod_rank_two (hs : 1 ≤ s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (α : σ →₀ ℕ)
    (g h : F.associatedDegree.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (F.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  let x : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients g.log α, F.polynomialOrbit_coefficient_mem_rank_one w α g⟩
  let y : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients h.log α, F.polynomialOrbit_coefficient_mem_rank_one w α h⟩
  let z : (F.layer (Finsupp.weight w α) 1).baseChange ℝ :=
    ⟨coefficients (g * h).log α, F.polynomialOrbit_coefficient_mem_rank_one w α (g * h)⟩
  apply (F.realHorizontalMap_eq (Finsupp.weight w α) z (x + y)).mp
  rw [← F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α (g * h) z rfl,
    map_mul]
  change Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α g) +
      Multiplicative.toAdd (F.nativeHorizontalCoefficientHom hs b ω hF w α h) = _
  rw [F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α g x rfl,
    F.nativeHorizontalCoefficientHom_eq_realHorizontalMap hs b ω hF w α h y rfl, map_add]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s n r : ℕ}
  {E : RationalFilteredNilmanifold L s n} (T : E.DegreeRankStructure r)

theorem orbit_log_mul_mod_rank_two (hs : 1 ≤ s) (c : Basis ι ℚ L) (τ : ι → ℕ)
    (hF : ∀ j, T.filtration.associatedDegree.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (w : σ → ℕ) (α : σ →₀ ℕ) (g h : E.filtration.realification.PolynomialOrbit w) :
    coefficients (g * h).log α - (coefficients g.log α + coefficients h.log α) ∈
      (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ := by
  have hp := T.filtration.polynomialOrbit_log_mul_mod_rank_two hs c τ hF w α
    (T.orbitEquiv w g) (T.orbitEquiv w h)
  have hprod : ((T.orbitEquiv w g) * (T.orbitEquiv w h)).log = (g * h).log :=
    (congrArg (fun z => z.log) (map_mul (T.orbitEquiv w) g h).symm).trans
      (T.orbitEquiv_log w (g * h))
  have heq := congrArg₂ (fun x y => x - y) (congrArg (fun z => coefficients z α) hprod)
    (congrArg₂ (fun x y => x + y)
      (congrArg (fun z => coefficients z α) (T.orbitEquiv_log w g))
      (congrArg (fun z => coefficients z α) (T.orbitEquiv_log w h)))
  exact (congrArg (fun z => z ∈ (T.filtration.layer (Finsupp.weight w α) 2).baseChange ℝ) heq).mp hp

end Erdos3.RationalFilteredNilmanifold.DegreeRankStructure

end

end OAI
