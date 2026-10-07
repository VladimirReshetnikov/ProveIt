import OAI.Combinatorics.Progressions.Lattices.JointAffineUnitSource
import OAI.Combinatorics.Progressions.Linear.KernelJetSupportIdentity
import OAI.Combinatorics.Progressions.Linear.SelectedKernelReconstruction
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport

namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

theorem realJetMatrix_sumColumns {α K I J N : Type*} [DecidableEq α]
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (vertices : Finset α → K → ℝ) (rows : I → Finset α) :
    realJetMatrix (fun j => MvPolynomial.monomial (Sum.elim eK eN j) 1) vertices rows =
      Matrix.fromCols (realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) vertices rows)
        (realJetMatrix (fun n => MvPolynomial.monomial (eN n) 1) vertices rows) := by
  funext i j
  cases j <;> rfl

theorem affineJetUnitMap_monomial_jet {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) (normalizedCubeTuple input z x) rows)
    (c w r : J ⊕ N → ℝ) (i : I) :
    let E := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
      (fun j => hS (s j)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) (fun _ => H))
    affineJetUnitMap s E F eN input z rows c w x r i =
      booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input z x t)
        (monomialArrayPolynomial (Sum.elim eK eN) (fun j => c j+w j*r j))) (rows i) := by
  dsimp only
  rw [← realJetMatrix_monomialArray (Sum.elim eK eN) (normalizedCubeTuple input z x) rows
    (fun j => c j+w j*r j) i, realJetMatrix_sumColumns, Matrix.fromCols_mulVec]
  unfold affineJetUnitMap
  rw [normalizedJetColumns_eq_realJetMatrix]
  have hk := normalizedKernel_reconstruct M s hM S (fun _ => H) hS (fun _ => hH)
    (fun j => c (.inl j)+w (.inl j)*r (.inl j))
  rw [hkernel] at hk
  rw [← hk]
  rfl

theorem affineJetUnitMap_raw_monomial_jet {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) (normalizedCubeTuple input z x) rows)
    (T : K → ℝ) (hT : ∀ k, T k ≠ 0) (c w r : J ⊕ N → ℝ) (i : I) :
    let E := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
      (fun j => hS (s j)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) (fun _ => H))
    booleanCoefficient (fun t => MvPolynomial.eval (fun k => T k*normalizedCubeTuple input z x t k)
      (monomialArrayPolynomial (Sum.elim eK eN)
        (fun j => H*(c j+w j*r j)/monomialScale T (Sum.elim eK eN j)))) (rows i)/H =
      affineJetUnitMap s E F eN input z rows c w x r i := by
  dsimp only
  exact (monomialArrayPolynomial_jet_rescale (Sum.elim eK eN) (fun j => c j+w j*r j) T
    (normalizedCubeTuple input z x) H hH.ne' hT (rows i)).trans
    (affineJetUnitMap_monomial_jet M s hM S hS hH eK eN input z rows x hkernel c w r i).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem monomialArrayPolynomial_equiv {C D K : Type*} [Fintype C] [Fintype D]
    (f : C ≃ D) (e : D → K →₀ ℕ) (a : D → ℝ) :
    monomialArrayPolynomial (e ∘ f) (a ∘ f) = monomialArrayPolynomial e a := by
  unfold monomialArrayPolynomial
  exact f.sum_comp (fun d => MvPolynomial.monomial (e d) (a d))

noncomputable def originalMonomialJetMap {C Z X K α O : Type*}
    [Fintype C] [Fintype α] [DecidableEq α]
    (e : C → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℝ)
    (rows : O → Finset α) (c w : C → ℝ) (x : X → ℝ) (r : C → ℝ) (o : O) : ℝ :=
  booleanCoefficient (fun t => MvPolynomial.eval (normalizedCubeTuple input z x t)
    (monomialArrayPolynomial e (fun j => c j + w j * r j))) (rows o)

theorem originalMonomialJetMap_measurable_comp {Ω C Z X K α O : Type*}
    [MeasurableSpace Ω] [Fintype C] [Fintype α] [DecidableEq α] [Fintype O]
    (e : C → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (rows : O → Finset α)
    (c w : C → ℝ) (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (x : Ω → X → ℝ) (hx : ∀ j, Measurable (fun a => x a j))
    (r : Ω → C → ℝ) (hr : ∀ j, Measurable (fun a => r a j)) :
    Measurable (fun a => originalMonomialJetMap e input (z a) rows c w (x a) (r a)) := by
  have he (a : Ω) : originalMonomialJetMap e input (z a) rows c w (x a) (r a) =
      polynomialColumns (fun o j => normalizedJetColumn (e j) input (z a) (rows o))
        (x a) (fun j => c j + w j * r a j) := by
    rw [normalizedJetColumns_eq_realJetMatrix]
    funext o
    exact (realJetMatrix_monomialArray e (normalizedCubeTuple input (z a) (x a)) rows
      (fun j => c j + w j * r a j) o).symm
  simp_rw [he]
  exact normalizedJetColumns_measurable_comp e input rows z hz x hx _
    (fun j => measurable_const.add (measurable_const.mul (hr j)))

theorem originalMonomialJetMap_eq_affine {C Z X K α O J N : Type*}
    [Fintype C] [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N]
    (f : J ⊕ N ≃ C) (e : C → K →₀ ℕ)
    (M : Matrix O J ℤ) (s : O ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : O → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (e (f (.inl j))) 1)
        (normalizedCubeTuple input z x) rows) (c w r : C → ℝ) :
    originalMonomialJetMap e input z rows c w x r =
      affineJetUnitMap s
        (normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
          (fun j => hS (s j)) (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s)
          (fun j => S j.val) (fun _ => H)))
        (fun n => e (f (.inr n))) input z rows (c ∘ f) (w ∘ f) x (r ∘ f) := by
  have he : Sum.elim (fun j => e (f (.inl j))) (fun n => e (f (.inr n))) = e ∘ f := by
    funext j
    cases j <;> rfl
  funext o
  have hi := affineJetUnitMap_monomial_jet M s hM S hS hH
    (fun j => e (f (.inl j))) (fun n => e (f (.inr n))) input z rows x hkernel
    (c ∘ f) (w ∘ f) (r ∘ f) o
  rw [he] at hi
  have ha : (fun j => (c ∘ f) j + (w ∘ f) j * (r ∘ f) j) =
      (fun j => c j + w j * r j) ∘ f := rfl
  rw [ha, monomialArrayPolynomial_equiv] at hi
  exact hi.symm

theorem originalMonomialJetMap_unit_law {C Z X K α O J N : Type*}
    [Fintype C] [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
    [Fintype J] [DecidableEq J] [Fintype N]
    (f : J ⊕ N ≃ C) (e : C → K →₀ ℕ)
    (M : Matrix O J ℤ) (s : O ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : O → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (e (f (.inl j))) 1)
        (normalizedCubeTuple input z x) rows)
    (c w : C → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j| + w j ≤ R) :
    (unitCoefficientSource C).map (originalMonomialJetMap e input z rows c w x) =
      realDensityMeasure volume
        (affineSelectedJetDensity s
          (normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
            (fun j => hS (s j)) (fun _ => hH))
          (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s)
            (fun j => S j.val) (fun _ => H)))
          (fun n => e (f (.inr n))) input z rows (c ∘ f) (w ∘ f) x) := by
  let A := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
    (fun j => hS (s j)) (fun _ => hH)
  let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s)
    (fun j => S j.val) (fun _ => H))
  let U := affineJetUnitMap s A F (fun n => e (f (.inr n))) input z rows (c ∘ f) (w ∘ f) x
  have hU : Measurable U :=
    affineJetUnitMap_measurable_comp s A F (fun n => e (f (.inr n))) input rows
      (fun _ => c ∘ f) (fun _ => w ∘ f) id measurable_const measurable_const measurable_id
      (fun _ => z) (fun _ => measurable_const) (fun _ => x) (fun _ => measurable_const)
  have he : originalMonomialJetMap e input z rows c w x = U ∘ (fun r => r ∘ f) :=
    funext (fun r => originalMonomialJetMap_eq_affine f e M s hM S hS hH
      input z rows x hkernel c w r)
  rw [he, ← Measure.map_map hU (by fun_prop)]
  have hr : (unitCoefficientSource C).map (fun r => r ∘ f) =
      unitCoefficientSource (J ⊕ N) := by
    simpa only [Equiv.symm_symm] using unitCoefficientSource_reindex f.symm
  rw [hr]
  exact affineSelectedJetDensity_unit_law s A F (fun n => e (f (.inr n)))
    input z rows (c ∘ f) (w ∘ f) (fun j => hw (f j)) R (fun j => hsupport (f j)) x

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

noncomputable def rawAffinePolynomialJet {J K α I : Type*} [Fintype J] [DecidableEq α]
    (e : J → K →₀ ℕ) (H : ℝ) (T : K → ℝ) (vertices : Finset α → K → ℝ)
    (rows : I → Finset α) (c w r : J → ℝ) (i : I) : ℝ :=
  booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (scaledAffinePolynomial e H T c w r)) (rows i)/H

theorem rawAffinePolynomialJet_eq_affine {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) (normalizedCubeTuple input z x) rows)
    (T : K → ℝ) (hT : ∀ k, T k ≠ 0) (vertices : Finset α → K → ℝ)
    (hvertices : ∀ t k, vertices t k = T k*normalizedCubeTuple input z x t k)
    (c w r : J ⊕ N → ℝ) :
    let E := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
      (fun j => hS (s j)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) (fun _ => H))
    rawAffinePolynomialJet (Sum.elim eK eN) H T vertices rows c w r =
      affineJetUnitMap s E F eN input z rows c w x r := by
  dsimp only
  funext i
  unfold rawAffinePolynomialJet scaledAffinePolynomial
  have hv : vertices = fun t k => T k*normalizedCubeTuple input z x t k := funext (fun t => funext (hvertices t))
  rw [hv]
  exact affineJetUnitMap_raw_monomial_jet M s hM S hS hH eK eN input z rows x hkernel T hT c w r i

theorem rawAffinePolynomialJet_unit_law {Z X K α I J N : Type*}
    [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype N]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j) {H : ℝ} (hH : 0 < H)
    (eK : J → K →₀ ℕ) (eN : N → K →₀ ℕ)
    (input : K → Option α → Z ⊕ X) (z : Z → ℝ) (rows : I → Finset α) (x : X → ℝ)
    (hkernel : normalizedIntegerColumns M S (fun _ => H) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK j) 1) (normalizedCubeTuple input z x) rows)
    (T : K → ℝ) (hT : ∀ k, T k ≠ 0) (vertices : Finset α → K → ℝ)
    (hvertices : ∀ t k, vertices t k = T k*normalizedCubeTuple input z x t k)
    (c w : J ⊕ N → ℝ) (hw : ∀ j, 0 < w j) (R : ℝ≥0) (hsupport : ∀ j, |c j|+w j ≤ R) :
    let E := normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
      (fun j => hS (s j)) (fun _ => hH)
    let F := matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) (fun _ => H))
    (realDensityMeasure MeasureTheory.volume (smoothProductProfile (J ⊕ N))).map
      (rawAffinePolynomialJet (Sum.elim eK eN) H T vertices rows c w) =
      realDensityMeasure MeasureTheory.volume (affineSelectedJetDensity s E F eN input z rows c w x) := by
  dsimp only
  have he : rawAffinePolynomialJet (Sum.elim eK eN) H T vertices rows c w =
      affineJetUnitMap s
        (normalizedPivotEquiv (M.submatrix id s) hM (fun j => S (s j)) (fun _ => H)
          (fun j => hS (s j)) (fun _ => hH))
        (matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns M s) (fun j => S j.val) (fun _ => H)))
        eN input z rows c w x := funext (fun r =>
    rawAffinePolynomialJet_eq_affine M s hM S hS hH eK eN input z rows x hkernel T hT vertices hvertices c w r)
  rw [he]
  exact affineSelectedJetDensity_unit_law s _ _ eN input z rows c w hw R hsupport x

end Erdos3

end

end OAI
