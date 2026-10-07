/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates

namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
variable {σ τ : Type*} {s d : ℕ}

theorem symbolicShearPrefixSubstitution_weighted_degree (p : τ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (weightedPatchVariableWeight p w i) (Sum.elim p w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (weightedPatchVariableWeight p w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

namespace PolynomialPatch
variable (A : PolynomialPatch σ s d) (p : τ → ℕ)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim p A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim p A.weight) n)

include hdegree in
theorem weightedSymbolicShearFullCenter_degree (i : Fin d) :
    A.symbolicShearFullCenter f i ∈
      weightedSupportLE (Sum.elim p A.weight) (A.weight i) := by
  apply (weightedSupportLE _ _).sub_mem (weightedSupportLE_X _ (Sum.inr i))
  apply hdegree
  apply polynomialHom_preserves_weightedDegree A.weight _ (rename Sum.inr) _
    (A.form.topResidualEquiv_degree (weightedSupportLE_X A.weight i))
  intro j
  rw [rename_X]
  exact weightedSupportLE_X _ (Sum.inr j)

noncomputable def weightedSymbolicShearForm : WeightedParameterSlots τ p d A.weight where
  center i := aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)
  degree i := weightedSupportLE_aeval _ _ _
    (symbolicShearPrefixSubstitution_weighted_degree p A.weight i)
    (A.weightedSymbolicShearFullCenter_degree p f hdegree i)

noncomputable def weightedSymbolicShearPatch : WeightedParameterPatch τ p s d where
  weight := A.weight
  weight_pos := A.weight_pos
  weight_le := A.weight_le
  weight_mono := A.weight_mono
  form := A.weightedSymbolicShearForm p f hdegree
  kernel := A.kernel

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

include hspecialize in
theorem weightedSymbolicShearForm_slots (t : τ → ℝ) :
    (A.weightedSymbolicShearForm p f hdegree).slots t =
      A.form.shearTransformedSlots A.weight_mono (e t) := by
  classical
  apply TriangularSlots.ext
  intro x i
  let y : Fin d → ℝ := fun j => if j.val < i.val then x j else 0
  have hy : ∀ j : Fin d, j < i → y j = x j := by
    intro j hj
    exact ite_eq_left hj
  have heval :
      (fun v => aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (symbolicShearPrefixSubstitution i v)) = Sum.elim t y := by
    funext v
    cases v with
    | inl a => simp [symbolicShearPrefixSubstitution]
    | inr j =>
        dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr, y]
        split_ifs with h
        · exact aeval_X _ _
        · exact map_zero _
  change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
    (aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)) = _
  rw [MvPolynomial.comp_aeval_apply, heval,
    A.symbolicShearFullCenter_eval f e hspecialize]
  exact (A.form.shearTransformedSlots A.weight_mono (e t)).lower i y x hy

include hspecialize in
theorem weightedSymbolicShearPatch_value (t : τ → ℝ) :
    (A.weightedSymbolicShearPatch p f hdegree).value t =
      ∑' b : Fin d → ℤ, A.kernel.value
        (fun i => aeval (polynomialSubstitutionPoint (e t).val.toAlgHom
          (fun j => (b j : ℝ))) (A.form.topResidualEquiv (X i))) := by
  change ((A.weightedSymbolicShearForm p f hdegree).slots t).patchValue A.kernel = _
  rw [A.weightedSymbolicShearForm_slots p f hdegree e hspecialize]
  simp only [TriangularSlots.patchValue, PolynomialSlots.shearTransformedSlots_residual]

include hspecialize in
theorem weightedSymbolicShearPatch_value_eq_observable
    (g : (τ → ℝ) → (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (he : ∀ t, e t = (polynomialShearRealAutEquiv A.weight s A.weight_le (g t))⁻¹)
    (t : τ → ℝ) :
    (A.weightedSymbolicShearPatch p f hdegree).value t =
      A.shearObservable (QuotientGroup.mk (g t)) := by
  rw [A.weightedSymbolicShearPatch_value p f hdegree e hspecialize]
  unfold shearObservable polynomialShearQuotientSum
  change _ = polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel (g t)
  rw [he t]
  rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {τ : Type*} (p : τ → ℕ) {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

noncomputable def weightedPolynomialShearOrbitSymbolicHom (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p) :
    MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ :=
  polynomialShearExpHom (polynomialSymbolicShearDerivation w
    (weightedPolynomialShearOrbitParameterCoordinates s hw p g))

theorem weightedPolynomialShearOrbitSymbolicHom_degree (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p)
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim p w) n) :
    weightedPolynomialShearOrbitSymbolicHom p hw g P ∈
      weightedSupportLE (Sum.elim p w) n :=
  polynomialSymbolicShearExp_weighted_degree p w _
    (weightedPolynomialShearOrbitParameterCoordinates_degree s hw p g) hP

theorem weightedPolynomialShearOrbitSymbolicHom_specialization (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p)
    (t : τ → ℝ) (P : MvPolynomial (τ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (weightedPolynomialShearOrbitSymbolicHom p hw g P) =
      (polynomialShearRealAutEquiv w s hw
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          p t g)).val (patchParameterSpecialization t P) :=
  weightedPolynomialShearOrbitSymbolicExp_specialization w s hw p g t P

theorem weightedPolynomialShearOrbitSymbolicHom_lower (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p)
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 0) w) n) :
    weightedPolynomialShearOrbitSymbolicHom p hw g P - P ∈
      weightedSupportLT (Sum.elim (fun _ : τ => 0) w) n :=
  polynomialShearExp_sub_lower _ hP

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

noncomputable def ofWeightedShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : WeightedParameterPatch τ p s d := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.weightedSymbolicShearPatch p (weightedPolynomialShearOrbitSymbolicHom p A.weight_le g⁻¹)
    (weightedPolynomialShearOrbitSymbolicHom_degree p A.weight_le g⁻¹)

@[simp] theorem ofWeightedShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : (A.ofWeightedShearOrbit p g).weight = A.weight := rfl

@[simp] theorem ofWeightedShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : (A.ofWeightedShearOrbit p g).kernel = A.kernel := rfl

theorem ofWeightedShearOrbit_value_real
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) (t : τ → ℝ) :
    (A.ofWeightedShearOrbit p g).value t = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        p t g)) := by
  let _ := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.weightedSymbolicShearPatch_value_eq_observable p
    (weightedPolynomialShearOrbitSymbolicHom p A.weight_le g⁻¹)
    (weightedPolynomialShearOrbitSymbolicHom_degree p A.weight_le g⁻¹)
    (fun t => polynomialShearRealAutEquiv A.weight s A.weight_le
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        p t g⁻¹))
    (weightedPolynomialShearOrbitSymbolicHom_specialization p A.weight_le g⁻¹)
    (fun t => (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
      p t g)
    (fun t => by rw [map_inv, map_inv]) t

theorem ofWeightedShearOrbit_value_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) (t : τ → ℤ) :
    (A.ofWeightedShearOrbit p g).value (fun i => (t i : ℝ)) = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
        p t g)) := by
  rw [ofWeightedShearOrbit_value_real, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

theorem exists_weighted_patch_of_shear_orbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit p) :
    ∃ B : WeightedParameterPatch τ p s d, B.weight = A.weight ∧ B.kernel = A.kernel ∧
      ∀ t : τ → ℤ, B.value (fun i => (t i : ℝ)) = A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          p t g)) :=
  ⟨A.ofWeightedShearOrbit p g, rfl, rfl, A.ofWeightedShearOrbit_value_integer p g⟩

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open VectorPolynomial

variable {X : Type*} {m n : ℕ} {J : Fin m → Type*}

noncomputable def taggedShearOrbitReindexChart (e : Fin n ≃ Sigma J) :
    X ⊕ Sigma J → MvPolynomial (X ⊕ Fin n) ℝ :=
  fun v => MvPolynomial.X (Sum.map id e.symm v)

theorem taggedShearOrbitReindexChart_degree (e : Fin n ≃ Sigma J)
    (v : X ⊕ Sigma J) :
    taggedShearOrbitReindexChart e v ∈
      weightedSupportLE (Sum.elim (fun _ : X => 1) (fun i => (e i).1.val + 1))
        (fullTaggedVariableWeight J v) := by
  have h := weightedSupportLE_X (R := ℝ)
    (Sum.elim (fun _ : X => 1) (fun i => (e i).1.val + 1)) (Sum.map id e.symm v)
  cases v with
  | inl x => exact h
  | inr a => simpa only [taggedShearOrbitReindexChart, Sum.map_inr, Sum.elim_inr,
      Equiv.apply_symm_apply] using h

namespace PolynomialPatch
variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofTaggedWeightedShearOrbit (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    WeightedParameterPatch (X ⊕ Fin n)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1)) s d :=
  A.ofWeightedShearOrbit (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1))
    ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
      (fullTaggedVariableWeight J)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1))
      (taggedShearOrbitReindexChart e) (taggedShearOrbitReindexChart_degree e) g)

@[simp] theorem ofTaggedWeightedShearOrbit_weight (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofTaggedWeightedShearOrbit e g).weight = A.weight := rfl

@[simp] theorem ofTaggedWeightedShearOrbit_kernel (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofTaggedWeightedShearOrbit e g).kernel = A.kernel := rfl

theorem ofTaggedWeightedShearOrbit_value_real (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) (x : X → ℝ) (b : Fin n → ℝ) :
    (A.ofTaggedWeightedShearOrbit e g).value (Sum.elim x b) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
          (fullTaggedVariableWeight J) (Sum.elim x (fun a => b (e.symm a))) g)) := by
  rw [ofTaggedWeightedShearOrbit, ofWeightedShearOrbit_value_real,
    NilpotentLieFiltration.polynomialOrbitRealChart_realEval]
  have h : (fun i => MvPolynomial.eval (Sum.elim x b)
      (taggedShearOrbitReindexChart e i)) = Sum.elim x (fun a => b (e.symm a)) := by
    funext v
    cases v <;> simp [taggedShearOrbitReindexChart]
  rw [h]

theorem ofTaggedWeightedShearOrbit_value_integer (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) (x : X → ℤ) (b : Fin n → ℤ) :
    (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ))) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (Sum.elim x (fun a => b (e.symm a))) g)) := by
  rw [ofTaggedWeightedShearOrbit_value_real]
  have h : Sum.elim (fun i => (x i : ℝ)) (fun a => (b (e.symm a) : ℝ)) =
      fun v => ((Sum.elim x (fun a => b (e.symm a))) v : ℝ) := by
    funext v
    cases v <;> rfl
  rw [h, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open VectorPolynomial

variable {σ X : Type*} {s d m n : ℕ} {J : Fin m → Type*}
    (A : PolynomialPatch σ s d) (e : Fin n ≃ Σ j, J j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

theorem ofTaggedWeightedShearOrbit_value_nearest (x : X → ℤ) :
    (A.ofTaggedWeightedShearOrbit e g).value
      (Sum.elim (fun i => (x i : ℝ))
        (fun i => (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c x) i : ℝ))) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c x) g)) := by
  rw [A.ofTaggedWeightedShearOrbit_value_integer,
    fullTaggedPhysicalIntegerPoint_eq_nearest e poly c x]

theorem ofTaggedWeightedShearOrbit_bufferedScalarScore
    (χ : PatchKernel n) (f : (X → ℤ) → ℝ) (lam : ℝ) (x : X → ℤ) :
    bufferedScalarScore χ (fullTaggedBufferedCoordinates e poly c)
      (fun x b => (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ)))) f lam x =
      (f x - lam) * χ.value (fun i => fullTaggedBufferedCoordinates e poly c x i -
        (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c x) i : ℝ)) *
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c x) g)) := by
  unfold bufferedScalarScore
  dsimp only
  rw [A.ofTaggedWeightedShearOrbit_value_nearest e poly c g]

theorem ofTaggedWeightedShearOrbit_bufferedMean_eq_score
    {Ω : Type*} [Fintype Ω] (law : FiniteProbabilityWeights Ω) (physical : Ω → X → ℤ)
    (χ : PatchKernel n) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    law.mean (fun u => bufferedScalarScore χ (fullTaggedBufferedCoordinates e poly c)
      (fun x b => (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ)))) f lam (physical u)) =
    (law.complexMean (fun u => ((f (physical u) - lam : ℝ) : ℂ) *
      ((χ.value (fun i => fullTaggedBufferedCoordinates e poly c (physical u) i -
        (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c (physical u)) i : ℝ)) : ℝ) : ℂ) *
      ((A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c (physical u)) g)) : ℝ) : ℂ))).re := by
  simp only [A.ofTaggedWeightedShearOrbit_bufferedScalarScore e poly c g,
    ← Complex.ofReal_mul, law.complexMean_ofReal, Complex.ofReal_re]

theorem ofTaggedWeightedShearOrbit_plateauMean_eq_score
    {Ω : Type*} [Fintype Ω] (law : FiniteProbabilityWeights Ω) (physical : Ω → X → ℤ)
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hsmall : ∀ u, law.weight u ≠ 0 → ∀ i,
      |fullTaggedBufferedCoordinates e poly c (physical u) i -
        (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c (physical u)) i : ℝ)| ≤ 1 / 8) :
    law.mean (fun u => bufferedScalarScore (majorPhasePlateauKernel n)
      (fullTaggedBufferedCoordinates e poly c)
      (fun x b => (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ)))) f lam (physical u)) =
    (law.complexMean (fun u => ((f (physical u) - lam : ℝ) : ℂ) *
      ((A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c (physical u)) g)) : ℝ) : ℂ))).re := by
  rw [A.ofTaggedWeightedShearOrbit_bufferedMean_eq_score e poly c g]
  apply congrArg Complex.re
  apply law.complexMean_congr_support
  intro u hu
  rw [majorPhasePlateauKernel_one _ (hsmall u hu)]
  simp only [Complex.ofReal_one, mul_one]

end Erdos3.PolynomialPatch

end

end OAI
