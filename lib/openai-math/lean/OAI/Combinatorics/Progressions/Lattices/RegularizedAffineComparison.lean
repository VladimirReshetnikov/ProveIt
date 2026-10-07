import OAI.Combinatorics.Progressions.Estimates.UniformRegularizedProfileComparison
import OAI.Combinatorics.Progressions.Polynomial.RawAffinePolynomialJet

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem nonprincipalDilation_width_pos {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {t : ℝ} (ht : 0 < t)
    (w : C → ℝ) (hw : ∀ j, 0 < w j) (j : C) :
    0 < nonprincipalDilation e principal t j*w j :=
  mul_pos (nonprincipalDilation_pos e principal ht j) (hw j)

theorem nonprincipalDilation_width_lower {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {t δ : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (w : C → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hδ : ∀ j, δ ≤ w j) (j : C) :
    t*δ ≤ nonprincipalDilation e principal t j*w j :=
  (mul_le_mul_of_nonneg_left (hδ j) ht).trans
    (mul_le_mul_of_nonneg_right (nonprincipalDilation_lower e principal ht1 j) (hw j))

theorem nonprincipalDilation_profile_support {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (c w : C → ℝ) (hw : ∀ j, 0 ≤ w j) (hsupport : ∀ j, |c j|+w j ≤ R) (j : C) :
    |nonprincipalDilation e principal t j*c j| + nonprincipalDilation e principal t j*w j ≤ R := by
  rw [abs_mul, abs_of_pos (nonprincipalDilation_pos e principal ht j), ← mul_add]
  exact (mul_le_of_le_one_left (add_nonneg (abs_nonneg _) (hw j))
    (nonprincipalDilation_le_one e principal ht1 j)).trans (hsupport j)

theorem affineAllowance_nonprincipal_sum_le {C B K : Type*} [Fintype C] [Fintype B]
    (e : C → K →₀ ℕ) (principal : B → K →₀ ℕ) (c w : C → ℝ) :
    (∑ j ∈ nonprincipalCoefficientSlots e principal, |affineCoefficientAllowance (c j) (w j)|) ≤
      ∑ j, affineCoefficientAllowance (c j) (w j) := by
  simp only [abs_of_pos (affineCoefficientAllowance_pos _ _)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _ _ => (affineCoefficientAllowance_pos (c j) (w j)).le)

theorem affinePrincipal_sum_le {C B : Type*} [Fintype B]
    (index : B → C) (c w r : C → ℝ) (hr : ∀ j, |r j| ≤ 1) :
    (∑ b, |c (index b)+w (index b)*r (index b)|) ≤ ∑ b, (|c (index b)|+|w (index b)|) :=
  Finset.sum_le_sum (fun b _ => affineParameter_abs_upper _ _ _ (hr (index b)))

theorem affineConstantCoefficient_measurable {Ω C K : Type*} [MeasurableSpace Ω] [Fintype C]
    (e : C → K →₀ ℕ) (c w : C → ℝ) (r : Ω → C → ℝ)
    (hr : ∀ j, Measurable (fun ω => r ω j)) :
    Measurable (fun ω => (monomialArrayPolynomial e (fun j => c j+w j*r ω j)).coeff 0) := by
  classical
  simp only [monomialArrayPolynomial, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.measurable_sum
  intro j _
  split_ifs <;> fun_prop

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def canonicalAffineRawArray {D G α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (Q : D → ℝ) (T : SamplerTupleIndex G B h → ℝ) (c w r : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (tuple : Finset α → SamplerTupleIndex G B h → ℝ) :
    (Σ d, O d) → ℝ :=
  let p := fun d => scaledAffinePolynomial (e d) (Q d) T (c d) (w d) (r d)
  rawProductArrayJet h sets
    (fun d => fixedNonprincipalExponents (monomialExponentSet (e d)) (canonicalPrincipalExponent h d))
    (fun _ m => m) (fun d b v => .inr ⟨d, b, v⟩)
    (fun d b => (p d).coeff (canonicalPrincipalExponent h d b))
    (fun d m => (p d).coeff m) (fun d => (p d).coeff 0) Q tuple

theorem canonicalAffineRawArray_eq {D G α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (Q : D → ℝ) (T : SamplerTupleIndex G B h → ℝ) (c w r : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (tuple : Finset α → SamplerTupleIndex G B h → ℝ) :
    canonicalAffineRawArray h e Q T c w r sets tuple =
      fun o => rawAffinePolynomialJet (e o.1) (Q o.1) T tuple (sets o.1) (c o.1) (w o.1) (r o.1) o.2 := by
  funext o
  exact canonicalRawJet_of_support h hh
    (fun d => scaledAffinePolynomial (e d) (Q d) T (c d) (w d) (r d))
    (fun d => monomialExponentSet (e d))
    (fun d => scaledAffinePolynomial_support (e d) (Q d) T (c d) (w d) (r d)) sets Q tuple o

theorem scaledAffinePolynomial_principal_coefficient {D G : Type*}
    {B C : D → Type*} [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (Q : D → ℝ) (T : SamplerTupleIndex G B h → ℝ) (c w r : ∀ d, C d → ℝ) (d : D) (b : B d) :
    (scaledAffinePolynomial (e d) (Q d) T (c d) (w d) (r d)).coeff (canonicalPrincipalExponent h d b) =
      scaledPrincipalCoefficient h Q T (fun d b v => .inr ⟨d, b, v⟩)
        (fun d b => c d (index d b)+w d (index d b)*r d (index d b)) d b := by
  rw [← hindex d b, scaledAffinePolynomial_coeff (e d) (he d), hindex d b,
    monomialScale_canonicalPrincipal]
  rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem canonicalAffineRawArray_eq_jointUnitMap {D G Z α : Type*} [Fintype D]
    [Fintype α] [DecidableEq α] {B O J N : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
    (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
    (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
    (Q : D → ℝ) (hQ : ∀ d, 0 < Q d) (T : SamplerTupleIndex G B h → ℝ)
    (hT : ∀ k, T k ≠ 0)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (extra : G → Option α → Z) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ)
    (hkernel : ∀ d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
        (normalizedCubeTuple (canonicalTupleInput extra) z x) (sets d))
    (c w r : ∀ d, J d ⊕ N d → ℝ) :
    let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
      (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
    let F := fun d => matrixSupCLM
      (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
    canonicalAffineRawArray h (fun d => Sum.elim (eK d) (eN d)) Q T c w r sets
      (rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x)) =
      fun o => jointAffineJetUnitMap s E F eN (canonicalTupleInput extra) z sets c w x r o.1 o.2 := by
  dsimp only
  rw [canonicalAffineRawArray_eq h hh]
  funext o
  exact congrFun (rawAffinePolynomialJet_eq_affine (M o.1) (s o.1) (hM o.1) (S o.1) (hS o.1) (hQ o.1)
    (eK o.1) (eN o.1) (canonicalTupleInput extra) z (sets o.1) x (hkernel o.1) T hT
    (rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x))
    (fun t k => rawCanonicalCubeTuple_rescale extra T z x t k) (c o.1) (w o.1) (r o.1)) o.2

end Erdos3

end

section

namespace Erdos3

theorem canonicalAffineRawArray_normalized {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (Q : D → ℝ) (T : SamplerTupleIndex G B h → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hT : ∀ k, T k ≠ 0)
    (c w r : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α)
    (extra : G → Option α → Z) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    canonicalAffineRawArray h e Q T c w r sets
      (rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x)) =
      fun o => booleanCoefficient (fun vertex =>
        MvPolynomial.eval (normalizedCubeTuple (canonicalTupleInput extra) z x vertex)
          (monomialArrayPolynomial (e o.1) (fun j => c o.1 j+w o.1 j*r o.1 j))) (sets o.1 o.2) := by
  rw [canonicalAffineRawArray_eq h hh]
  funext o
  unfold rawAffinePolynomialJet scaledAffinePolynomial
  have ht : rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x) =
      fun vertex k => T k*normalizedCubeTuple (canonicalTupleInput extra) z x vertex k :=
    funext (fun vertex => funext (fun k => rawCanonicalCubeTuple_rescale extra T z x vertex k))
  rw [ht]
  exact monomialArrayPolynomial_jet_rescale (e o.1) _ T _ (Q o.1) (hQ o.1) hT _

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem canonicalAffineRawArray_joint_law {D G Z α : Type*} [Fintype D]
    [Fintype α] [DecidableEq α] {B O J N : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
    (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
    (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
    (Q : D → ℝ) (hQ : ∀ d, 0 < Q d) (T : SamplerTupleIndex G B h → ℝ)
    (hT : ∀ k, T k ≠ 0)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (extra : G → Option α → Z) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ)
    (hkernel : ∀ d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
        (normalizedCubeTuple (canonicalTupleInput extra) z x) (sets d))
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d) :
    let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
      (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
    let F := fun d => matrixSupCLM
      (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
    (jointUnitCoefficientSource J N).map
      (fun r => sigmaAxisCoordinates O (canonicalAffineRawArray h (fun d => Sum.elim (eK d) (eN d))
        Q T c w r sets (rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x)))) =
      realDensityMeasure volume (jointAffineJetDensity s E F eN (canonicalTupleInput extra) z sets c w x) := by
  dsimp only
  let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
    (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
  let F := fun d => matrixSupCLM
    (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
  calc
    _ = (jointUnitCoefficientSource J N).map
        (jointAffineJetUnitMap s E F eN (canonicalTupleInput extra) z sets c w x) := by
      congr 1
      funext r
      exact congrArg (sigmaAxisCoordinates O)
        (canonicalAffineRawArray_eq_jointUnitMap h hh sets M s hM S hS Q hQ T hT eK eN extra z x hkernel c w r)
    _ = _ := jointAffineJetDensity_unit_law s E F eN (canonicalTupleInput extra) z sets c w hw R hsupport x

end Erdos3

end

section

namespace Erdos3

theorem rawCanonicalJet_eq_smallAffineArray {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w r : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α)
    (extra : G → Option α → Z) (Q : D → ℝ) (T : SamplerTupleIndex G B h → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hT : ∀ k, T k ≠ 0)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    rawCanonicalJet h (fun d b => c d (index d b)+w d (index d b)*r d (index d b)) sets
      (fun d => nonprincipalCoefficientSlots (e d) (canonicalPrincipalExponent h d))
      (fun d j => affineCoefficientAllowance (c d j) (w d j)) e
      affineAuxiliaryCoefficient (affineAuxiliaryExtra extra) Q T
      (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r d j)).coeff 0)
      t (affineAuxiliaryVariables c w z r) (jointCubeScale h (fun i => T (.inr i)) x) =
    canonicalAffineRawArray h e Q T
      (fun d j => nonprincipalDilation (e d) (canonicalPrincipalExponent h d) t j*c d j)
      (fun d j => nonprincipalDilation (e d) (canonicalPrincipalExponent h d) t j*w d j)
      r sets (rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x)) := by
  rw [rawCanonicalJet_normalized_polynomial h _ sets _ _ e _ _ Q T _ hQ hT,
    canonicalAffineRawArray_normalized h hh e Q T hQ hT]
  funext o
  congr 1
  funext vertex
  rw [rawProductArrayPolynomial_affine_auxiliary h hh e he index hindex]
  have hv : normalizedCubeTuple (canonicalTupleInput (affineAuxiliaryExtra (C := C) extra))
      (affineAuxiliaryVariables c w z r) x vertex =
      normalizedCubeTuple (canonicalTupleInput extra) z x vertex :=
    funext (fun k => normalizedCubeTuple_affineAuxiliary h extra c w z r x vertex k)
  rw [hv]

end Erdos3

end

section

namespace Erdos3

noncomputable def smallAffineSourceOutput {Ω D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (c w : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (t : ℝ)
    (z : Ω → Z → ℝ) (r : Ω → ∀ d, C d → ℝ)
    (p : Ω × (JointBlockParameter B h α → ℝ)) : (Σ d, O d) → ℝ :=
  canonicalAffineRawArray h e (Q p.1) scale
    (fun d j => nonprincipalDilation (e d) (canonicalPrincipalExponent h d) t j*c d j)
    (fun d j => nonprincipalDilation (e d) (canonicalPrincipalExponent h d) t j*w d j)
    (r p.1) sets (rawCanonicalCubeTuple extra scale (z p.1) p.2)

theorem rawSourceOutput_eq_smallAffineSource {Ω D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (t : ℝ) (z : Ω → Z → ℝ) (r : Ω → ∀ d, C d → ℝ) :
    rawSourceOutput h (fun a d b => c d (index d b)+w d (index d b)*r a d (index d b)) sets
      (fun d => nonprincipalCoefficientSlots (e d) (canonicalPrincipalExponent h d))
      (fun d j => affineCoefficientAllowance (c d j) (w d j)) e
      affineAuxiliaryCoefficient (affineAuxiliaryExtra extra) Q scale
      (fun a d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r a d j)).coeff 0)
      t (fun a => affineAuxiliaryVariables c w (z a) (r a)) =
      smallAffineSourceOutput h e c w sets extra Q scale t z r := by
  let E := jointCubeScaleHomeomorph (α := α) h (fun i => scale (.inr i)) (fun i => hscale (.inr i))
  funext p
  rcases E.surjective p.2 with ⟨x, hx⟩
  have hp : p = (p.1, jointCubeScale h (fun i => scale (.inr i)) x) := Prod.ext rfl hx.symm
  rw [hp]
  exact rawCanonicalJet_eq_smallAffineArray h hh e he index hindex c w (r p.1) sets extra
    (Q p.1) scale (hQ p.1) hscale t (z p.1) x

theorem smallAffineSourceOutput_measurable {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype Z] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ k, scale k ≠ 0) (t : ℝ)
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (r : Ω → ∀ d, C d → ℝ) (hr : ∀ d j, Measurable (fun a => r a d j)) :
    Measurable (smallAffineSourceOutput h e c w sets extra Q scale t z r) := by
  rw [← rawSourceOutput_eq_smallAffineSource h hh e he index hindex c w sets extra Q scale hQ hscale]
  apply rawSourceOutput_measurable
  · intro d b
    exact measurable_const.add (measurable_const.mul (hr d (index d b)))
  · exact hQ
  · exact hscale
  · intro d
    exact affineConstantCoefficient_measurable (e d) (c d) (w d) (fun a => r a d) (hr d)
  · exact affineAuxiliaryVariables_measurable c w z r hz hr

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def regularizedAffineIdealDensity {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → C d) (c w : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (r : ∀ d, C d → ℝ) : ((Σ d, O d) → ℝ) → ℝ :=
  regularizedImageDensity (jointBooleanSource h)
    (fun x => booleanConstantJet sets
      (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r d j)).coeff 0) +
      jointBooleanSampler h (fun d b => c d (index d b)+w d (index d b)*r d (index d b)) sets x) δ

theorem regularizedAffineIdealDensity_probability {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → C d) (c w : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (hδ : 0 < δ) (r : ∀ d, C d → ℝ) :
    (∀ x, 0 ≤ regularizedAffineIdealDensity h e index c w sets δ r x) ∧
      Integrable (regularizedAffineIdealDensity h e index c w sets δ r) ∧
      (∫ x, regularizedAffineIdealDensity h e index c w sets δ r x) = 1 :=
  regularizedImageDensity_probability (jointBooleanSource h) _
    (measurable_const.add (jointBooleanSampler_contDiff h _ sets).continuous.measurable) δ hδ

theorem regularizedAffineIdealDensity_bounds {D G α : Type*}
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → C d) (c w : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0) (hδ : 0 < δ) (r : ∀ d, C d → ℝ) :
    (∀ x, regularizedAffineIdealDensity h e index c w sets δ r x ∈
      Set.Icc (0 : ℝ) (δ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
      LipschitzWith (affineProductProfileLip (Σ d, O d) δ)
        (regularizedAffineIdealDensity h e index c w sets δ r) :=
  regularizedImageDensity_bounds (jointBooleanSource h) _
    (measurable_const.add (jointBooleanSampler_contDiff h _ sets).continuous.measurable) δ hδ

theorem regularizedAffineIdealDensity_measurable_comp {Ω D G α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → C d) (c w : ∀ d, C d → ℝ)
    (sets : ∀ d, O d → Finset α) (δ : ℝ≥0)
    (r : Ω → ∀ d, C d → ℝ) (hr : ∀ d j, Measurable (fun a => r a d j))
    (v : Ω → (Σ d, O d) → ℝ) (hv : Measurable v) :
    Measurable (fun a => regularizedAffineIdealDensity h e index c w sets δ (r a) (v a)) := by
  let : IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := jointBooleanSource_probability h
  let U := fun p : Ω × (JointBlockParameter B h α → ℝ) =>
    booleanConstantJet sets
      (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r p.1 d j)).coeff 0) +
    jointBooleanSampler h (fun d b => c d (index d b)+w d (index d b)*r p.1 d (index d b)) sets p.2
  have hb := booleanConstantJet_measurable_comp (Ω := Ω) sets
    (fun a d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r a d j)).coeff 0)
    (fun d => affineConstantCoefficient_measurable (e d) (c d) (w d) (fun a => r a d) (hr d))
  have hU : Measurable U := (hb.comp measurable_fst).add
    (jointBooleanSampler_measurable_frozen (Ω := Ω) h sets
      (fun a d b => c d (index d b)+w d (index d b)*r a d (index d b))
      (fun d b => measurable_const.add (measurable_const.mul (hr d (index d b)))))
  have hm : Measurable (fun p : Ω × (JointBlockParameter B h α → ℝ) =>
      affineProductProfile (U p) (fun _ => (δ : ℝ)) (v p.1)) :=
    affineProductProfile_measurable_center U (fun p => v p.1) (fun _ => (δ : ℝ))
      (fun i => (measurable_pi_apply i).comp hU)
      (fun i => (measurable_pi_apply i).comp (hv.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end Erdos3

end

section

namespace Erdos3

theorem smallAffineSourceOutput_zero_rescale {Ω D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (z : Ω → Z → ℝ) (r : Ω → ∀ d, C d → ℝ) (a : Ω) (x : JointBlockParameter B h α → ℝ) :
    smallAffineSourceOutput h e c w sets extra Q scale 0 z r
      (a, jointCubeScale h (fun i => scale (.inr i)) x) =
      booleanConstantJet sets
        (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r a d j)).coeff 0) +
      jointBooleanSampler h (fun d b => c d (index d b)+w d (index d b)*r a d (index d b)) sets x := by
  rw [← rawSourceOutput_eq_smallAffineSource h hh e he index hindex c w sets extra Q scale hQ hscale]
  unfold rawSourceOutput
  rw [rawCanonicalJet_rescale]
  exact canonicalScaledProductArrayJet_zero h _ sets _ _ e _ _ (Q a) scale _ (hQ a) hscale _ x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_small_affine_source_tolerance_with_scale
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    [∀ d, Fintype (J d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → J d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d → ℝ) (r : Ω → ∀ d, J d → ℝ)
    (hr : ∀ d j, Measurable (fun a => r a d j))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (e d j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) (AffineAuxiliaryIndex Z J) h c₀ C A T degree Csum Wsum ε ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d j, |r a d j| ≤ 1) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale 0 z r p))
            ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) -
          ∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale t z r p))
            ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))| ≤ ε := by
  classical
  have hprincipal : ∀ d b, Measurable (fun a => c d (index d b)+w d (index d b)*r a d (index d b)) :=
    fun d b => measurable_const.add (measurable_const.mul (hr d (index d b)))
  have hweights (d) : (∑ j ∈ nonprincipalCoefficientSlots (e d) (canonicalPrincipalExponent h d),
      |affineCoefficientAllowance (c d j) (w d j)|) ≤ Wsum :=
    (affineAllowance_nonprincipal_sum_le (e d) (canonicalPrincipalExponent h d) (c d) (w d)).trans (hwsum d)
  obtain ⟨t, ht, ht1, heq, hcomp⟩ := exists_raw_source_tolerance_with_scale (Y := Y)
    (fun a d b => c d (index d b)+w d (index d b)*r a d (index d b)) hprincipal
    (fun a => affineAuxiliaryVariables c w (z a) (r a)) (affineAuxiliaryVariables_measurable c w z r hz hr)
    sets hsets h hh hcard block hblock c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition
    (fun d => nonprincipalCoefficientSlots (e d) (canonicalPrincipalExponent h d))
    (fun d j => affineCoefficientAllowance (c d j) (w d j)) e affineAuxiliaryCoefficient
    (affineAuxiliaryExtra extra) hdegree (fun d j _ => htaildegree d j) hCsum hWsum hweights hε
  refine ⟨t, ht, ht1, heq, ?_⟩
  intro Q scale hQ hscale μ hμ hzb hrb P hP φ hφ hbound
  have haux : ∀ᵐ a ∂μ, ∀ j, |affineAuxiliaryVariables c w (z a) (r a) j| ≤ 1 := by
    filter_upwards [hzb, hrb] with a ha hR
    exact affineAuxiliaryVariables_abs_le c w (z a) (r a) ha hR
  have hlower : ∀ᵐ a ∂μ, ∀ d o,
      c₀ d ≤ |c d (index d (block d o))+w d (index d (block d o))*r a d (index d (block d o))| := by
    filter_upwards [hrb] with a ha d o
    exact (hclow d o).trans (affineParameter_abs_lower _ _ _ (ha d _))
  have hupper : ∀ᵐ a ∂μ, ∀ d o,
      |c d (index d (block d o))+w d (index d (block d o))*r a d (index d (block d o))| ≤ C d := by
    filter_upwards [hrb] with a ha d o
    exact (affineParameter_abs_upper _ _ _ (ha d _)).trans (hcup d o)
  have hsum : ∀ᵐ a ∂μ, ∀ d,
      (∑ b, |c d (index d b)+w d (index d b)*r a d (index d b)|) ≤ Csum := by
    filter_upwards [hrb] with a ha d
    exact (affinePrincipal_sum_le (index d) (c d) (w d) (r a d) (ha d)).trans (hcsum d)
  have hcst : ∀ d, Measurable (fun a =>
      (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r a d j)).coeff 0) :=
    fun d => affineConstantCoefficient_measurable (e d) (c d) (w d) (fun a => r a d) (hr d)
  have hresult := hcomp Q scale
    (fun a d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r a d j)).coeff 0)
    hQ hscale hcst μ hμ haux hlower hupper hsum P hP φ hφ hbound
  rw [rawSourceOutput_eq_smallAffineSource h hh e he index hindex c w sets extra Q scale hQ
      (fun k => (hscale k).ne') 0 z r,
    rawSourceOutput_eq_smallAffineSource h hh e he index hindex c w sets extra Q scale hQ
      (fun k => (hscale k).ne') t z r] at hresult
  exact hresult

theorem exists_small_affine_source_tolerance
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    [∀ d, Fintype (J d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → J d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d → ℝ) (r : Ω → ∀ d, J d → ℝ)
    (hr : ∀ d j, Measurable (fun a => r a d j))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (e d j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      (∀ᵐ a ∂μ, ∀ d j, |r a d j| ≤ 1) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
        |(∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale 0 z r p))
            ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) -
          ∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale t z r p))
            ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))| ≤ ε := by
  obtain ⟨t, hpos, hone, _, herr⟩ := exists_small_affine_source_tolerance_with_scale (Y := Y) h hh e he index hindex c w r hr z hz sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A T hLip hTransition extra
    hdegree htaildegree hCsum hWsum hcsum hwsum hε
  exact ⟨t, hpos, hone, herr⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem smallAffineSourceOutput_zero_integral {Ω D G Z α : Type*} [MeasurableSpace Ω]
    [Fintype D] [Fintype α] [DecidableEq α]
    {B O C : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (C d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, C d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → C d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, C d → ℝ) (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ)
    (hQ : ∀ a d, Q a d ≠ 0) (hscale : ∀ k, 0 < scale k)
    (z : Ω → Z → ℝ) (r : Ω → ∀ d, C d → ℝ) (μ : Measure Ω) [SFinite μ]
    (φ : Ω × ((Σ d, O d) → ℝ) → ℝ) :
    (∫ p, φ (p.1, smallAffineSourceOutput h e c w sets extra Q scale 0 z r p)
      ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) =
    ∫ p, φ (p.1, booleanConstantJet sets
        (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r p.1 d j)).coeff 0) +
      jointBooleanSampler h (fun d b => c d (index d b)+w d (index d b)*r p.1 d (index d b)) sets p.2)
      ∂μ.prod (jointBooleanSource h) := by
  rw [scaledJointCubeSource_prod_integral h _ (fun i => hscale (.inr i))]
  simp_rw [smallAffineSourceOutput_zero_rescale h hh e he index hindex c w sets extra Q scale hQ
    (fun k => (hscale k).ne') z r]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_regularized_affine_comparison_with_parameters
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)] [∀ d, Fintype (J d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → J d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d → ℝ) (r : Ω → ∀ d, J d → ℝ)
    (hr : ∀ d j, Measurable (fun a => r a d j))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (e d j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h c₀ C A T (ε/2) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) (AffineAuxiliaryIndex Z J) h c₀ C A T degree Csum Wsum (ε/2) ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) → (∀ᵐ a ∂μ, ∀ d j, |r a d j| ≤ 1) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ p, regularizedAffineIdealDensity h e index c w sets δ (r p.1) p.2*φ (P p) ∂μ.prod volume) -
        ∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale t z r p))
          ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))| ≤ ε := by
  obtain ⟨δ, hδ, hδ1, hδeq, hreg⟩ := exists_retained_boolean_regularization_with_radius (Ω := Ω) h hh sets hsets hcard block hblock
    c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition (half_pos hε)
  obtain ⟨t, ht, ht1, hteq, hraw⟩ := exists_small_affine_source_tolerance_with_scale (Y := Y) h hh e he index hindex c w r hr z hz
    sets hsets hcard block hblock c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A T hLip hTransition
    extra hdegree htaildegree hCsum hWsum hcsum hwsum (half_pos hε)
  refine ⟨δ, hδ, hδ1, hδeq, t, ht, ht1, hteq, ?_⟩
  intro Q scale hQ hscale μ hμ hzb hrb P hP φ hφ hbound
  let : IsProbabilityMeasure μ := hμ
  let cp := fun a d b => c d (index d b)+w d (index d b)*r a d (index d b)
  let b := fun a => booleanConstantJet sets
    (fun d => (monomialArrayPolynomial (e d) (fun j => c d j+w d j*r a d j)).coeff 0)
  have hcp : ∀ d j, Measurable (fun a => cp a d j) :=
    fun d j => measurable_const.add (measurable_const.mul (hr d (index d j)))
  have hb : Measurable b := booleanConstantJet_measurable_comp sets _
    (fun d => affineConstantCoefficient_measurable (e d) (c d) (w d) (fun a => r a d) (hr d))
  have hgood : ∀ᵐ a ∂μ, (∀ d o, c₀ d ≤ |cp a d (block d o)|) ∧ (∀ d o, |cp a d (block d o)| ≤ C d) := by
    filter_upwards [hrb] with a ha
    exact ⟨fun d o => (hclow d o).trans (affineParameter_abs_lower _ _ _ (ha d _)),
      fun d o => (affineParameter_abs_upper _ _ _ (ha d _)).trans (hcup d o)⟩
  have hreg' := hreg cp b hcp hb μ hμ hgood (fun p => φ (P p)) (hφ.comp hP) (fun p => hbound (P p))
  have hideal := smallAffineSourceOutput_zero_integral h hh e he index hindex c w sets extra Q scale
    hQ hscale z r μ (fun p => φ (P p))
  change (∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale 0 z r p))
      ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))) =
    (∫ p, φ (P (p.1, b p.1+jointBooleanSampler h (cp p.1) sets p.2)) ∂μ.prod (jointBooleanSource h)) at hideal
  rw [← hideal] at hreg'
  have hraw' := hraw Q scale hQ hscale μ hμ hzb hrb P hP φ hφ hbound
  have htri := abs_sub_le
    (∫ p, regularizedAffineIdealDensity h e index c w sets δ (r p.1) p.2*φ (P p) ∂μ.prod volume)
    (∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale 0 z r p))
      ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i))))
    (∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale t z r p))
      ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i))))
  change |(∫ p, regularizedAffineIdealDensity h e index c w sets δ (r p.1) p.2*φ (P p) ∂μ.prod volume) -
    (∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale 0 z r p))
      ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i))))| ≤ ε/2 at hreg'
  linarith

theorem exists_regularized_affine_comparison
    {Ω D G Z α Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)] [∀ d, Fintype (J d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (e : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (e d)) (index : ∀ d, B d → J d)
    (hindex : ∀ d b, e d (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d → ℝ) (r : Ω → ∀ d, J d → ℝ)
    (hr : ∀ d j, Measurable (fun a => r a d j))
    (z : Ω → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (e d j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (Q : Ω → D → ℝ) (scale : SamplerTupleIndex G B h → ℝ),
      (∀ a d, Q a d ≠ 0) → (∀ k, 0 < scale k) →
      ∀ μ : Measure Ω, IsProbabilityMeasure μ →
      (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) → (∀ᵐ a ∂μ, ∀ d j, |r a d j| ≤ 1) →
      ∀ P : Ω × ((Σ d, O d) → ℝ) → Y, Measurable P →
      ∀ φ : Y → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ p, regularizedAffineIdealDensity h e index c w sets δ (r p.1) p.2*φ (P p) ∂μ.prod volume) -
        ∫ p, φ (P (p.1, smallAffineSourceOutput h e c w sets extra Q scale t z r p))
          ∂μ.prod (scaledJointCubeSource h (fun i => scale (.inr i)))| ≤ ε := by
  obtain ⟨δ, hδ, hδ1, _, t, ht, ht1, _, herr⟩ := exists_regularized_affine_comparison_with_parameters (Ω := Ω) (Y := Y) h hh e he index hindex c w r hr z hz sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A T hLip hTransition extra
    hdegree htaildegree hCsum hWsum hcsum hwsum hε
  exact ⟨δ, hδ, hδ1, t, ht, ht1, herr⟩

end Erdos3

end

end OAI
