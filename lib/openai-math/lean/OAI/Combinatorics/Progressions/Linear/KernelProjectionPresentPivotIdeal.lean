import OAI.Combinatorics.Progressions.Estimates.ExternalPivotMaskSelection
import OAI.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
import OAI.Combinatorics.Progressions.Nilpotent.LocalNiltestFixedNativePartners

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct Classical

def KernelProjectionPresentPivot {J : Type*} {r : ℕ}
    (code : Fin r → Option J) := {i : Fin r // ∃ j, code i = some j}

noncomputable instance {J : Type*} {r : ℕ} (code : Fin r → Option J) :
    Fintype (KernelProjectionPresentPivot code) := inferInstanceAs (Fintype {i // ∃ j, code i = some j})

noncomputable def kernelProjectionSelectedPivot {J : Type*} {r : ℕ}
    (code : Fin r → Option J) (i : KernelProjectionPresentPivot code) : J :=
  Classical.choose i.property

theorem kernelProjectionSelectedPivot_spec {J : Type*} {r : ℕ}
    (code : Fin r → Option J) (i : KernelProjectionPresentPivot code) :
    code i.val = some (kernelProjectionSelectedPivot code i) := Classical.choose_spec i.property

theorem kernelProjectionPresentPivot_card_le {J : Type*} {r : ℕ}
    (code : Fin r → Option J) : Fintype.card (KernelProjectionPresentPivot code) ≤ r := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (fun i : KernelProjectionPresentPivot code => i.val) Subtype.val_injective

variable {L Y Ω T X J I σ Θ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d r : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : Y → ℕ}

noncomputable def kernelProjectionLocalPivotTests
    (code : Fin r → Option J) (U : J → D.Niltest w) (tests : Ω → D.Niltest w) :
    Ω → KernelProjectionPresentPivot code → D.Niltest w :=
  fun a i => (U (kernelProjectionSelectedPivot code i)).withOrbit (tests a).orbit

theorem exists_kernel_projection_fixed_native_partners
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype I] [Nonempty I]
    (code : Fin r → Option J) (U : J → D.Niltest w) (tests : Ω → D.Niltest w)
    (p : ℝ) (hU : ∀ j, (U j).ComplexityLE p)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (physical : Ω → T → X) (slices : Ω → Fin r → Finset T)
    (point : Ω → T → Y → ℤ)
    (hS : ∀ a i, (slices a i).Nonempty) {cap : ℝ}
    (hsize : ∀ a i, (Fintype.card T : ℝ) / (slices a i).card ≤ cap)
    (v e : X → ℂ) (Q : I → X → ℂ) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • Q i) + e)
    {M kappa : ℝ} (hM : 0 < M) (hkappa : 0 < kappa)
    (hc : (∑ i, ‖c i‖) ≤ M) (hmass : kappa ≤ outer.mass productive)
    (herror : (r : ℝ) * sampledSliceSeminorm outer physical
      (fun a (i : KernelProjectionPresentPivot code) => slices a i.val)
      (localNiltestPartnerWeight (kernelProjectionLocalPivotTests code U tests) point p) e ≤
        kappa * Real.exp (-2 * p) / 8)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hQ : ∀ i, Q i ∈ twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hscore : ∀ a ∈ productive, ∀ i j, code i = some j → Real.exp (-p) ≤
      ‖𝔼 t ∈ slices a i, v (physical a t) *
        ((U j).withOrbit (tests a).orbit).eval (point a t)‖) :
    ∃ (fixedTwist : KernelProjectionPresentPivot code → Θ)
      (nativeValue : KernelProjectionPresentPivot code → X → ℂ)
      (_native : ∀ i, NativeSampleModel nativeWeight degree budget sample (nativeValue i))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      (3 * kappa / 4) / (Fintype.card I : ℝ) ^ r ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ i : KernelProjectionPresentPivot code,
        Real.exp (-p) / (2 * M) ≤
        ‖𝔼 t ∈ slices a i.val,
          (star (twist (fixedTwist i) (physical a t)) * nativeValue i (physical a t)) *
            ((U (kernelProjectionSelectedPivot code i)).withOrbit (tests a).orbit).eval
              (point a t)‖ := by
  let K := KernelProjectionPresentPivot code
  have hcard : (Fintype.card K : ℝ) ≤ r := by
    exact_mod_cast kernelProjectionPresentPivot_card_le code
  have herr : (Fintype.card K : ℝ) * sampledSliceSeminorm outer physical
      (fun a (i : K) => slices a i.val)
      (localNiltestPartnerWeight (kernelProjectionLocalPivotTests code U tests) point p) e ≤
      kappa * Real.exp (-2 * p) / 8 :=
    (mul_le_mul_of_nonneg_right hcard (apply_nonneg _ _)).trans herror
  obtain ⟨fixedTwist, nativeValue, native, retained, hsub, hpos, hretained, hlocal⟩ :=
    exists_local_niltest_fixed_native_partners outer productive physical
      (fun a (i : K) => slices a i.val) (kernelProjectionLocalPivotTests code U tests)
      point p (fun _ i => hU (kernelProjectionSelectedPivot code i))
      (fun a i => hS a i.val) (fun a i => hsize a i.val)
      v e Q c hmodel hM hkappa hc hmass herr nativeWeight degree budget sample twist hQ
      (fun a ha i => hscore a ha i.val (kernelProjectionSelectedPivot code i)
        (kernelProjectionSelectedPivot_spec code i))
  refine ⟨fixedTwist, nativeValue, native, retained, hsub, hpos, ?_, hlocal⟩
  apply le_trans _ hretained
  apply div_le_div_of_nonneg_left (by positivity)
    (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)
  exact pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card I)
    (kernelProjectionPresentPivot_card_le code)

end Erdos3

end

section

namespace Erdos3
open scoped TensorProduct Classical

open RationalFilteredNilmanifold

theorem exists_external_kernel_pivot_masks
    {L σ τ X Ω J I Freq : Type*} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J] [Fintype I] [Nonempty I]
    {s d r : ℕ} (D : RationalFilteredNilmanifold L s d)
    {w : σ → ℕ} {v : τ → ℕ}
    (code : Fin r → Option Freq) (U : Freq → X → D.Niltest w)
    (representative : I → X) {p B ε δ : ℝ}
    (hcomplex : ∀ f x, (U f x).ComplexityLE p)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(U f x).observable y -
      (U f (representative i)).observable y‖ ≤ ε)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (localOrbit : Ω → D.filtration.realification.PolynomialOrbit v)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : X → ℂ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hweight : ∀ x, ‖weight x‖ ≤ B)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(localLaw a).complexMean (fun j => weight (physical a j) *
        ((U f (physical a j)).withOrbit (localOrbit a)).eval (point a j))‖) :
    ∃ (chosen : KernelProjectionPresentPivot code → I)
      (masked : KernelProjectionPresentPivot code → X → ℂ) (H' : Finset Ω),
      (∀ k x, masked k x = if externalNetIndex
        (fun x => (U (kernelProjectionSelectedPivot code k) x).observable)
        (fun i => (U (kernelProjectionSelectedPivot code k) (representative i)).observable)
        (hnet (kernelProjectionSelectedPivot code k)) x = chosen k then weight x else 0) ∧
      (∀ k x, ‖masked k x‖ ≤ B) ∧ H' ⊆ H ∧ 0 < outer.mass H' ∧
      outer.mass H / (Fintype.card I : ℝ) ^ r ≤ outer.mass H' ∧
      (∀ a k, ((U (kernelProjectionSelectedPivot code k) (representative (chosen k))).withOrbit
        (localOrbit a)).ComplexityLE p) ∧
      ∀ a ∈ H', ∀ k, δ / (2 * Fintype.card I) ≤
        ‖(localLaw a).complexMean (fun j => masked k (physical a j) *
          ((U (kernelProjectionSelectedPivot code k) (representative (chosen k))).withOrbit
            (localOrbit a)).eval (point a j))‖ := by
  let K := KernelProjectionPresentPivot code
  let functions := fun (k : K) x => (U (kernelProjectionSelectedPivot code k) x).observable
  let centers := fun (k : K) i => (U (kernelProjectionSelectedPivot code k) (representative i)).observable
  have hselected (a : Ω) (ha : a ∈ H) (k : K) : δ ≤
      ‖(localLaw a).complexMean (fun j => weight (physical a j) * functions k (physical a j)
        (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval v (point a j) (localOrbit a))))‖ :=
    hscore a ha k.val (kernelProjectionSelectedPivot code k) (kernelProjectionSelectedPivot_spec code k)
  obtain ⟨chosen, masked, H', hmask, hcap, hsub, hpos, hmass, hs⟩ :=
    exists_simultaneous_external_pivot_masks functions centers
      (fun k => hnet (kernelProjectionSelectedPivot code k)) outer H hH
      (fun a _ => localLaw a) physical
      (fun a _ j => QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval v (point a j) (localOrbit a)))
      weight hB hδ herror hweight hselected
  refine ⟨chosen, masked, H', hmask, hcap, hsub, hpos, ?_, ?_, hs⟩
  · apply le_trans _ hmass
    apply div_le_div_of_nonneg_left (outer.mass_nonneg H)
      (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)
    exact pow_le_pow_right₀
      (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card I)
      (kernelProjectionPresentPivot_card_le code)
  · intro a k
    exact hcomplex _ _

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem finiteFrequencyKernel_presentPivots
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ)
    {r : ℕ} (code : Fin r → Option J) :
    finiteFrequencyKernel P (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList =
      frequencyCodeKernel P eta code := by
  ext x
  rw [mem_finiteFrequencyKernel, mem_frequencyCodeKernel]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro h i j hij
    let k : KernelProjectionPresentPivot code := ⟨i, ⟨j, hij⟩⟩
    have hselected : kernelProjectionSelectedPivot code k = j := by
      exact Option.some.inj ((kernelProjectionSelectedPivot_spec code k).symm.trans hij)
    simpa only [hselected] using h k (Finset.mem_toList.mpr (Finset.mem_univ k))
  · intro h k _
    exact h k.val (kernelProjectionSelectedPivot code k)
      (kernelProjectionSelectedPivot_spec code k)

namespace NilpotentLieFiltration

variable {L Y : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing Y] [LieAlgebra ℚ Y] {s r : ℕ}
    (F : NilpotentLieFiltration L s) (φ : L →ₗ⁅ℚ⁆ Y)
    (eta : J → L →ₗ[ℚ] ℚ) (code : Fin r → Option J)

theorem pivotAnnihilatorIdeal_presentPivots_toSubmodule :
    (F.pivotAnnihilatorIdeal φ (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList).toSubmodule =
      frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code := by
  exact finiteFrequencyKernel_presentPivots
    (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code

theorem pivotAnnihilatorIdeal_presentPivots
    (hK : frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code ≤
      F.layer s) :
    F.pivotAnnihilatorIdeal φ (fun k => eta (kernelProjectionSelectedPivot code k))
      (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList =
      F.topSubspaceIdeal
        (frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code) hK := by
  ext x
  change x ∈ (F.pivotAnnihilatorIdeal φ
    (fun k => eta (kernelProjectionSelectedPivot code k))
    (Finset.univ : Finset (KernelProjectionPresentPivot code)).toList).toSubmodule ↔
    x ∈ frequencyCodeKernel (F.layer s ⊓ LinearMap.ker φ.toLinearMap) eta code
  rw [F.pivotAnnihilatorIdeal_presentPivots_toSubmodule φ eta code]

end NilpotentLieFiltration

end Erdos3

end

end OAI
