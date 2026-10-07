/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Geometry.FilteredSymbolMapCoordinates
import OAI.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol

namespace OAI

section

namespace Erdos3

theorem lieTreeEval_hom {I L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] (φ : L →ₗ⁅ℚ⁆ M) (v : I → L) (a : FreeMagma I) :
    lieTreeEval (fun i => φ (v i)) a = φ (lieTreeEval v a) := by
  induction a using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb =>
    simp only [lieTreeEval, ha, hb, LieHom.map_lie]

namespace DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (P : DegreeRankLieFiltration M s r)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ P.layer d 1 → ∀ k, φ x k ∈ F.layer d 1)

def horizontalProjectionMap (d : ℕ) : P.layer d 1 →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) :=
  (F.fourHorizontalMap d).comp
    (((φ : M →ₗ[ℚ] (Fin 4 → L)).comp (P.layer d 1).subtype).codRestrict
      (F.fourHorizontalLayer d)
      (fun x => (F.mem_fourHorizontalLayer d (φ x.val)).mpr (hφ d x.val x.property)))

def horizontalProjectionImage (K : LieSubalgebra ℚ M) (d : ℕ) :
    Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  (K.toSubmodule.comap (P.layer d 1).subtype).map (F.horizontalProjectionMap P φ hφ d)

theorem mem_horizontalProjectionImage (K : LieSubalgebra ℚ M) (d : ℕ)
    (v : Fin 4 → F.HigherHorizontal d) :
    v ∈ F.horizontalProjectionImage P φ hφ K d ↔
      ∃ w : P.layer d 1, w.val ∈ K ∧ F.horizontalProjectionMap P φ hφ d w = v := Iff.rfl

theorem horizontalProjectionImage_frequency {E : Type*} [AddCommGroup E] [Module ℚ E]
    (K : LieSubalgebra ℚ M) (η : L →ₗ[ℚ] E)
    (hK : ∀ x ∈ K, x ∈ P.layer s r →
      η (φ x 0) + η (φ x 1) - η (φ x 2) - η (φ x 3) = 0)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, Fin 4 → F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ F.horizontalProjectionImage P φ hφ K (d i)) :
    η (F.horizontalTreeValue d a (fun i => v i 0)) +
      η (F.horizontalTreeValue d a (fun i => v i 1)) -
      η (F.horizontalTreeValue d a (fun i => v i 2)) -
      η (F.horizontalTreeValue d a (fun i => v i 3)) = 0 := by
  classical
  have hlift (i : I) := (F.mem_horizontalProjectionImage P φ hφ K (d i) (v i)).mp (hv i)
  choose w hwK hwm using hlift
  let u (i : I) : M := (w i).val
  let lifted (k : Fin 4) (i : I) : F.layer (d i) 1 := ⟨φ (u i) k, hφ (d i) (u i) (w i).property k⟩
  have hmap (k : Fin 4) :
      (fun i => F.higherHorizontalMk (d i) (lifted k i)) = (fun i => v i k) := by
    funext i
    exact congrFun (hwm i) k
  have hvalue (k : Fin 4) : F.horizontalTreeValue d a (fun i => v i k) = φ (lieTreeEval u a) k := by
    rw [← hmap k]
    calc
      _ = lieTreeEval (fun i => φ (u i) k) a := F.horizontalTreeValue_mk d a hd hr (lifted k)
      _ = lieTreeEval (fun i => φ (u i)) a k := (lieTreeEval_pi _ a k).symm
      _ = _ := congrFun (lieTreeEval_hom φ u a) k
  have htree : lieTreeEval u a ∈ K := by
    have hmem (t : FreeMagma I) : lieTreeEval u t ∈ K := by
      induction t using FreeMagma.rec with
      | of i => exact hwK i
      | mul a b ha hb => exact K.lie_mem ha hb
    exact hmem a
  have htop : lieTreeEval u a ∈ P.layer s r := by
    simpa only [hd, hr] using P.lieTreeEval_mem_length u d (fun i => (w i).property) a
  rw [hvalue 0, hvalue 1, hvalue 2, hvalue 3]
  exact hK _ htree htop

end DegreeRankLieFiltration

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

def layerHorizontalMap (d : ℕ) : A d →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) :=
  (F.fourHorizontalMap d).comp
    (((φ : M →ₗ[ℚ] (Fin 4 → L)).comp (A d).subtype).codRestrict
      (F.fourHorizontalLayer d)
      (fun x => (F.mem_fourHorizontalLayer d (φ x.val)).mpr (hφ d x.val x.property)))

def layerHorizontalImage (d : ℕ) : Submodule ℚ (Fin 4 → F.HigherHorizontal d) :=
  LinearMap.range (F.layerHorizontalMap A φ hφ d)

theorem mem_layerHorizontalImage (d : ℕ) (v : Fin 4 → F.HigherHorizontal d) :
    v ∈ F.layerHorizontalImage A φ hφ d ↔
      ∃ w : A d, F.layerHorizontalMap A φ hφ d w = v := Iff.rfl

theorem layerHorizontalImage_frequency {E : Type*} [AddCommGroup E] [Module ℚ E]
    (η : L →ₗ[ℚ] E) (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ u : I → M, (∀ i, u i ∈ A (d i)) →
      η (φ (lieTreeEval u a) 0) + η (φ (lieTreeEval u a) 1) -
        η (φ (lieTreeEval u a) 2) - η (φ (lieTreeEval u a) 3) = 0)
    (v : ∀ i, Fin 4 → F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ F.layerHorizontalImage A φ hφ (d i)) :
    η (F.horizontalTreeValue d a (fun i => v i 0)) +
      η (F.horizontalTreeValue d a (fun i => v i 1)) -
      η (F.horizontalTreeValue d a (fun i => v i 2)) -
      η (F.horizontalTreeValue d a (fun i => v i 3)) = 0 := by
  classical
  have hlift (i : I) := (F.mem_layerHorizontalImage A φ hφ (d i) (v i)).mp (hv i)
  choose w hw using hlift
  let u (i : I) : M := (w i).val
  let lifted (k : Fin 4) (i : I) : F.layer (d i) 1 :=
    ⟨φ (u i) k, hφ (d i) (u i) (w i).property k⟩
  have hmap (k : Fin 4) :
      (fun i => F.higherHorizontalMk (d i) (lifted k i)) = (fun i => v i k) := by
    funext i
    exact congrFun (hw i) k
  have hvalue (k : Fin 4) : F.horizontalTreeValue d a (fun i => v i k) = φ (lieTreeEval u a) k := by
    rw [← hmap k]
    calc
      _ = lieTreeEval (fun i => φ (u i) k) a := F.horizontalTreeValue_mk d a hd hr (lifted k)
      _ = lieTreeEval (fun i => φ (u i)) a k := (lieTreeEval_pi _ a k).symm
      _ = _ := congrFun (lieTreeEval_hom φ u a) k
  rw [hvalue 0, hvalue 1, hvalue 2, hvalue 3]
  exact hker u (fun i => (w i).property)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M E : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [AddCommGroup E] [Module ℚ E] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (P : DegreeRankLieFiltration M s r)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ P.layer d 1 → ∀ k, φ x k ∈ F.layer d 1)

theorem projected_sunflower_bracket
    (K : LieSubalgebra ℚ M) (η : L →ₗ[ℚ] E)
    (hK : ∀ x ∈ K, x ∈ P.layer s r →
      η (φ x 0) + η (φ x 1) - η (φ x 2) - η (φ x 3) = 0)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ fourFirstProjection (F.horizontalProjectionImage P φ hφ K (d i)))
    (i j : I) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ fourDependentProjection (F.horizontalProjectionImage P φ hφ K (d i)))
    (hvj : v j ∈ fourDependentProjection (F.horizontalProjectionImage P φ hφ K (d j))) :
    η (F.horizontalTreeValue d a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a) (F.horizontalTreeValue d a)
    (fun u k hk hu => F.horizontalTreeValue_zero_of_leaf d a u (i := k) hk hu)
    η (map_zero η) (fun k => F.horizontalProjectionImage P φ hφ K (d k))
    (F.horizontalProjectionImage_frequency P φ hφ K η hK d a hd hr) v hv i j hij hi hj hvi hvj

theorem projected_sunflower_representatives
    (K : LieSubalgebra ℚ M) (η : L →ₗ[ℚ] E)
    (hK : ∀ x ∈ K, x ∈ P.layer s r →
      η (φ x 0) + η (φ x 1) - η (φ x 2) - η (φ x 3) = 0)
    (d : I → ℕ) (a : FreeMagma I) (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (v : ∀ i, F.layer (d i) 1)
    (hv : ∀ i, F.higherHorizontalMk (d i) (v i) ∈
      fourFirstProjection (F.horizontalProjectionImage P φ hφ K (d i)))
    (i j : I) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : F.higherHorizontalMk (d i) (v i) ∈
      fourDependentProjection (F.horizontalProjectionImage P φ hφ K (d i)))
    (hvj : F.higherHorizontalMk (d j) (v j) ∈
      fourDependentProjection (F.horizontalProjectionImage P φ hφ K (d j))) :
    η (lieTreeEval (fun i => (v i).val) a) = 0 := by
  have h := F.projected_sunflower_bracket P φ hφ K η hK d a hd hr
    (fun k => F.higherHorizontalMk (d k) (v k)) hv i j hij hi hj hvi hvj
  rwa [F.horizontalTreeValue_mk d a hd hr v] at h

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L M E : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [AddCommGroup E] [Module ℚ E] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (A : ℕ → Submodule ℚ M)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ A d → ∀ k, φ x k ∈ F.layer d 1)

theorem layer_sunflower_bracket (η : L →ₗ[ℚ] E) (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ u : I → M, (∀ i, u i ∈ A (d i)) →
      η (φ (lieTreeEval u a) 0) + η (φ (lieTreeEval u a) 1) -
        η (φ (lieTreeEval u a) 2) - η (φ (lieTreeEval u a) 3) = 0)
    (v : ∀ i, F.HigherHorizontal (d i))
    (hv : ∀ i, v i ∈ fourFirstProjection (F.layerHorizontalImage A φ hφ (d i)))
    (i j : I) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : v i ∈ fourDependentProjection (F.layerHorizontalImage A φ hφ (d i)))
    (hvj : v j ∈ fourDependentProjection (F.layerHorizontalImage A φ hφ (d j))) :
    η (F.horizontalTreeValue d a v) = 0 :=
  four_dependent_inputs_vanish (lieTreeSupport a) (F.horizontalTreeValue d a)
    (fun u k hk hu => F.horizontalTreeValue_zero_of_leaf d a u (i := k) hk hu)
    η (map_zero η) (fun k => F.layerHorizontalImage A φ hφ (d k))
    (F.layerHorizontalImage_frequency A φ hφ η d a hd hr hker) v hv i j hij hi hj hvi hvj

theorem layer_sunflower_representatives (η : L →ₗ[ℚ] E) (d : I → ℕ) (a : FreeMagma I)
    (hd : lieTreeWeight d a = s) (hr : a.length = r)
    (hker : ∀ u : I → M, (∀ i, u i ∈ A (d i)) →
      η (φ (lieTreeEval u a) 0) + η (φ (lieTreeEval u a) 1) -
        η (φ (lieTreeEval u a) 2) - η (φ (lieTreeEval u a) 3) = 0)
    (v : ∀ i, F.layer (d i) 1)
    (hv : ∀ i, F.higherHorizontalMk (d i) (v i) ∈
      fourFirstProjection (F.layerHorizontalImage A φ hφ (d i)))
    (i j : I) (hij : i ≠ j) (hi : i ∈ lieTreeSupport a) (hj : j ∈ lieTreeSupport a)
    (hvi : F.higherHorizontalMk (d i) (v i) ∈
      fourDependentProjection (F.layerHorizontalImage A φ hφ (d i)))
    (hvj : F.higherHorizontalMk (d j) (v j) ∈
      fourDependentProjection (F.layerHorizontalImage A φ hφ (d j))) :
    η (lieTreeEval (fun i => (v i).val) a) = 0 := by
  have h := F.layer_sunflower_bracket A φ hφ η d a hd hr hker
    (fun k => F.higherHorizontalMk (d k) (v k)) hv i j hij hi hj hvi hvj
  rwa [F.horizontalTreeValue_mk d a hd hr v] at h

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

include hφ in
theorem projectedComponent_mem_layer (k : Fin 4) (d : ℕ) (x : M) (hx : x ∈ F.layer d) :
    ((liePiEval k).comp φ) x ∈ G.associatedDegree.layer d := by
  change φ x k ∈ G.layer d 0
  rw [G.rank_zero_eq_one]
  exact hφ d x hx k

noncomputable def projectedComponentSymbolMap (w : σ → ℕ) (k : Fin 4) :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ G.associatedDegree.PolynomialSymbol w :=
  F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) w

noncomputable def projectedHorizontalSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.PolynomialSymbol w →ₗ[ℚ] (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) :=
  LinearMap.pi (fun k => (G.higherHorizontalSymbolCoefficient w α).comp
    (G.projectedComponentSymbolMap F φ hφ w k).toLinearMap)

theorem projectedHorizontalSymbolCoefficient_symbol (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolMap w p) =
      G.layerHorizontalMap F.layer φ hφ (Finsupp.weight w α)
        ⟨coefficients p.val α, p.property α⟩ := by
  funext k
  change G.higherHorizontalSymbolCoefficient w α
    (F.filteredPolynomialSymbolMap G.associatedDegree ((liePiEval k).comp φ)
      (G.projectedComponent_mem_layer F φ hφ k) w (F.polynomialSymbolMap w p)) = _
  rw [F.filteredPolynomialSymbolMap_symbol, G.higherHorizontalSymbolCoefficient_map]
  apply congrArg (G.higherHorizontalMk (Finsupp.weight w α))
  apply Subtype.ext
  exact F.filteredPolynomialMap_coefficient G.associatedDegree ((liePiEval k).comp φ)
    (G.projectedComponent_mem_layer F φ hφ k) w p α

theorem projectedHorizontalSymbolCoefficient_lie (w : σ → ℕ) (α : σ →₀ ℕ)
    (x y : F.PolynomialSymbol w) :
    G.projectedHorizontalSymbolCoefficient F φ hφ w α ⁅x, y⁆ = 0 := by
  funext k
  change G.higherHorizontalSymbolCoefficient w α
    ((G.projectedComponentSymbolMap F φ hφ w k) ⁅x, y⁆) = 0
  rw [LieHom.map_lie]
  exact G.higherHorizontalSymbolCoefficient_lie w α _ _

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r) (F : NilpotentLieFiltration M t)
  (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

noncomputable def realProjectedHorizontalSymbolHom (ht : 1 ≤ t) (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.RealPolynomialSymbolGroup w →*
      Multiplicative (ℝ ⊗[ℚ] (Fin 4 → G.HigherHorizontal (Finsupp.weight w α))) where
  toFun X := Multiplicative.ofAdd
    ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord)
  map_one' := by
    change Multiplicative.ofAdd ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ 0) = 1
    rw [map_zero]
    rfl
  map_mul' X Y := by
    change Multiplicative.ofAdd ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
      (lieBCH t X.coord Y.coord)) = Multiplicative.ofAdd
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord +
          (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ Y.coord)
    exact congrArg Multiplicative.ofAdd (linearMap_baseChange_lieBCH_eq_add
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α)
      (G.projectedHorizontalSymbolCoefficient_lie F φ hφ w α) ht X.coord Y.coord)

@[simp] theorem realProjectedHorizontalSymbolHom_apply (ht : 1 ≤ t) (w : σ → ℕ) (α : σ →₀ ℕ)
    (X : F.RealPolynomialSymbolGroup w) :
    Multiplicative.toAdd (G.realProjectedHorizontalSymbolHom F φ hφ ht w α X) =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ X.coord := rfl

theorem real_projectedHorizontalSymbolCoefficient_component (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.PolynomialSymbol w) (k : Fin 4) :
    (LinearMap.proj k : (Fin 4 → G.HigherHorizontal (Finsupp.weight w α)) →ₗ[ℚ]
      G.HigherHorizontal (Finsupp.weight w α)).baseChange ℝ
        ((G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ x) =
      (G.higherHorizontalSymbolCoefficient w α).baseChange ℝ
        ((G.projectedComponentSymbolMap F φ hφ w k).toLinearMap.baseChange ℝ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp only [LinearMap.baseChange_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (G : DegreeRankLieFiltration L s r)

noncomputable def realFourHorizontalMap (d : ℕ) :
    (G.fourHorizontalLayer d).baseChange ℝ →ₗ[ℝ]
      ℝ ⊗[ℚ] (Fin 4 → G.HigherHorizontal d) :=
  ((G.fourHorizontalMap d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (G.fourHorizontalLayer d)).symm.toLinearMap

@[simp] theorem realFourHorizontalMap_baseChange (d : ℕ)
    (v : ℝ ⊗[ℚ] G.fourHorizontalLayer d) :
    G.realFourHorizontalMap d (realificationSubmoduleEquiv (G.fourHorizontalLayer d) v) =
      (G.fourHorizontalMap d).baseChange ℝ v := by
  exact congrArg ((G.fourHorizontalMap d).baseChange ℝ)
    ((realificationSubmoduleEquiv (G.fourHorizontalLayer d)).symm_apply_apply v)

variable (F : NilpotentLieFiltration M t) (φ : M →ₗ⁅ℚ⁆ (Fin 4 → L))
  (hφ : ∀ d x, x ∈ F.layer d → ∀ k, φ x k ∈ G.layer d 1)

noncomputable def projectedLayerCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] G.fourHorizontalLayer (Finsupp.weight w α) :=
  (φ.toLinearMap.comp (F.adaptedCoefficientMap w α)).codRestrict
    (G.fourHorizontalLayer (Finsupp.weight w α))
    (fun p => (G.mem_fourHorizontalLayer _ _).mpr (hφ _ _ (p.property α)))

@[simp] theorem projectedLayerCoefficient_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    (G.projectedLayerCoefficient F φ hφ w α p : Fin 4 → L) = φ (coefficients p.val α) := rfl

theorem projectedLayerCoefficient_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    G.fourHorizontalMap (Finsupp.weight w α) (G.projectedLayerCoefficient F φ hφ w α p) =
      G.projectedHorizontalSymbolCoefficient F φ hφ w α (F.polynomialSymbolMap w p) := by
  rw [G.projectedHorizontalSymbolCoefficient_symbol]
  rfl

theorem projectedLayerCoefficient_tensor_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (G.fourHorizontalLayer (Finsupp.weight w α)).subtype.baseChange ℝ
        ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) =
      φ.toLinearMap.baseChange ℝ (coefficients (F.realAdaptedPolynomialMap w x) α) := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    simp only [LinearMap.baseChange_tmul, G.projectedLayerCoefficient_coe,
      F.realAdaptedPolynomialMap_coefficient_tmul, Submodule.subtype_apply]
    rfl
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem projectedLayerCoefficient_tensor_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (x : ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) :
    (G.fourHorizontalMap (Finsupp.weight w α)).baseChange ℝ
        ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
        (F.realExtendedSymbolMap w x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a p =>
    change (G.fourHorizontalMap (Finsupp.weight w α)).baseChange ℝ
      ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ (a ⊗ₜ[ℚ] p)) =
        (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
          (a ⊗ₜ[ℚ] F.polynomialSymbolMap w p)
    simp only [LinearMap.baseChange_tmul, G.projectedLayerCoefficient_horizontal]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (b : Basis ι ℚ M) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hφ hF in
theorem real_projectedCoefficient_mem (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.realification.adaptedLieSubalgebra w) :
    φ.toLinearMap.baseChange ℝ (coefficients p.val α) ∈
      (G.fourHorizontalLayer (Finsupp.weight w α)).baseChange ℝ := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  rw [F.realAdaptedPolynomialTensor_coe, ← G.projectedLayerCoefficient_tensor_coe F φ hφ]
  exact (realificationSubmoduleEquiv (G.fourHorizontalLayer (Finsupp.weight w α))
    ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x)).property

theorem real_projectedCoefficient_horizontal (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.realification.adaptedLieSubalgebra w)
    (v : (G.fourHorizontalLayer (Finsupp.weight w α)).baseChange ℝ)
    (hv : v.val = φ.toLinearMap.baseChange ℝ (coefficients p.val α)) :
    G.realFourHorizontalMap (Finsupp.weight w α) v =
      (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
        (F.realPolynomialSymbolMap b ω hF w p) := by
  obtain ⟨x, rfl⟩ := F.realAdaptedPolynomialTensor_surjective w b ω hF p
  have heq : v = realificationSubmoduleEquiv (G.fourHorizontalLayer (Finsupp.weight w α))
      ((G.projectedLayerCoefficient F φ hφ w α).baseChange ℝ x) := by
    apply Subtype.ext
    exact hv.trans (G.projectedLayerCoefficient_tensor_coe F φ hφ w α x).symm
  rw [heq, G.realFourHorizontalMap_baseChange, G.projectedLayerCoefficient_tensor_horizontal]
  change _ = (G.projectedHorizontalSymbolCoefficient F φ hφ w α).baseChange ℝ
    (F.realSymbolOfPolynomial b ω hF w (F.realAdaptedPolynomialMap w x))
  rw [F.realSymbolOfPolynomial_realAdaptedPolynomialMap]

end Erdos3.DegreeRankLieFiltration

end

end OAI
