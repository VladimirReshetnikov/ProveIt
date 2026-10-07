import OAI.Combinatorics.Progressions.Sampling.PrecenterForecastNativeAtomDictionary

namespace OAI

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

noncomputable def externalNetMaskFamily
    {Freq X Y I : Type*} (F : Freq → X → Y → ℂ)
    (centers : Freq → I → Y → ℂ) {ε : ℝ}
    (hnet : ∀ f x, ∃ i, ∀ y, ‖F f x y - centers f i y‖ ≤ ε)
    (input : X → ℂ) : (Freq × I) → X → ℂ :=
  fun b x => if externalNetIndex (F b.1) (centers b.1) (hnet b.1) x = b.2
    then input x else 0

theorem exists_external_kernel_precenter_native_partners
    {L σ τ X Ω T I Freq NativeCoord Θ : Type*}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype T] [Fintype I] [Nonempty I]
    {s d r : ℕ} (D : RationalFilteredNilmanifold L s d)
    {w : σ → ℕ} {v : τ → ℕ}
    (U : Freq → X → D.Niltest w) (representative : I → X)
    {p B ε δ M termBound : ℝ}
    (hcomplex : ∀ f x, (U f x).ComplexityLE p)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(U f x).observable y -
      (U f (representative i)).observable y‖ ≤ ε)
    (input : X → ℂ) (models : (Freq × I) → CenteredForecastModel X)
    (nativeWeight : NativeCoord → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → NativeCoord → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, externalNetMaskFamily (fun f x => (U f x).observable)
      (fun f i => (U f (representative i)).observable) hnet input b =
        (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (hM : 0 < M) (hterm : 1 ≤ termBound)
    (code : Fin r → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights T)
    (localOrbit : Ω → D.filtration.realification.PolynomialOrbit v)
    (physical : Ω → T → X) (point : Ω → T → τ → ℤ)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ B)
    (hresidual : ∀ a ∈ H, ∀ f i,
      ‖(localLaw a).complexMean (fun t => (models (f, i)).residual (physical a t) *
        ((U f (representative i)).withOrbit (localOrbit a)).eval (point a t))‖ ≤
          (δ / (2 * Fintype.card I)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        ((U f (physical a t)).withOrbit (localOrbit a)).eval (point a t))‖) :
    ∃ (chosen : KernelProjectionPresentPivot code → I)
      (fixedTwist : KernelProjectionPresentPivot code → Θ)
      (nativeValue : KernelProjectionPresentPivot code → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r) ≤ outer.mass retained ∧
      (∀ a k, ((U (kernelProjectionSelectedPivot code k) (representative (chosen k))).withOrbit
        (localOrbit a)).ComplexityLE p) ∧
      ∀ a ∈ retained, ∀ k, (δ / (2 * Fintype.card I)) / (2 * M) ≤
        ‖(localLaw a).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            ((U (kernelProjectionSelectedPivot code k) (representative (chosen k))).withOrbit
              (localOrbit a)).eval (point a t))‖ := by
  obtain ⟨chosen, masked, H', hmask, _, hsub, hpos, hmass, hlocalComplex, hlocal⟩ :=
    exists_external_kernel_pivot_masks D code U representative hcomplex hnet
      outer H hH localLaw localOrbit physical point input hB hδ herror hinput hscore
  let selectedBranch := fun k : KernelProjectionPresentPivot code =>
    (kernelProjectionSelectedPivot code k, chosen k)
  let family := externalNetMaskFamily (fun f x => (U f x).observable)
    (fun f i => (U f (representative i)).observable) hnet input
  have hfamily (k : KernelProjectionPresentPivot code) :
      family (selectedBranch k) = masked k := by
    funext x
    exact (hmask k x).symm
  obtain ⟨fixedTwist, nativeValue, native, retained, hretSub, hretPos, hretMass, hretScore⟩ :=
    exists_precenter_forecast_finiteLaw_native_partners family models
      nativeWeight degree budget sample twist hnative hmodel hM hterm
      (div_pos hδ (by positivity)) hc hterms selectedBranch
      (kernelProjectionPresentPivot_card_le code) outer H' hpos
      (fun a _ => localLaw a) physical
      (fun a k t => ((U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).withOrbit (localOrbit a)).eval (point a t))
      (fun a ha k => hresidual a (hsub ha) _ _)
      (by intro a ha k; rw [hfamily]; exact hlocal a ha k)
  refine ⟨chosen, fixedTwist, nativeValue, native, retained,
    fun a ha => hsub (hretSub ha), hretPos, ?_, hlocalComplex, hretScore⟩
  calc
    outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r)
        = (outer.mass H / (Fintype.card I : ℝ) ^ r) / termBound ^ r := by
      rw [div_div]
    _ ≤ outer.mass H' / termBound ^ r :=
      div_le_div_of_nonneg_right hmass (pow_nonneg (by linarith) _)
    _ ≤ outer.mass retained := hretMass

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators TensorProduct Classical

theorem exists_external_kernel_precenter_native_point_partners
    {L σ X Ω T I Freq NativeCoord Θ : Type*}
    [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype T] [Fintype I] [Nonempty I]
    {s d r : ℕ} (D : RationalFilteredNilmanifold L s d)
    {w : σ → ℕ}
    (U : Freq → X → D.Niltest w) (representative : I → X)
    {p B ε δ M termBound : ℝ}
    (hcomplex : ∀ f x, (U f x).ComplexityLE p)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(U f x).observable y -
      (U f (representative i)).observable y‖ ≤ ε)
    (input : X → ℂ) (models : (Freq × I) → CenteredForecastModel X)
    (nativeWeight : NativeCoord → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → NativeCoord → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, externalNetMaskFamily (fun f x => (U f x).observable)
      (fun f i => (U f (representative i)).observable) hnet input b =
        (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (hM : 0 < M) (hterm : 1 ≤ termBound)
    (code : Fin r → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights T)
    (localPoint : Ω → T → D.Space) (physical : Ω → T → X)
    (hB : 0 ≤ B) (hδ : 0 < δ) (herror : B * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ B)
    (hresidual : ∀ a ∈ H, ∀ f i,
      ‖(localLaw a).complexMean (fun t => (models (f, i)).residual (physical a t) *
        (U f (representative i)).observable (localPoint a t))‖ ≤
          (δ / (2 * Fintype.card I)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        (U f (physical a t)).observable (localPoint a t))‖) :
    ∃ (chosen : KernelProjectionPresentPivot code → I)
      (fixedTwist : KernelProjectionPresentPivot code → Θ)
      (nativeValue : KernelProjectionPresentPivot code → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r) ≤ outer.mass retained ∧
      (∀ k, (U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).ComplexityLE p) ∧
      ∀ a ∈ retained, ∀ k, (δ / (2 * Fintype.card I)) / (2 * M) ≤
        ‖(localLaw a).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            (U (kernelProjectionSelectedPivot code k)
              (representative (chosen k))).observable (localPoint a t))‖ := by
  let K := KernelProjectionPresentPivot code
  let functions := fun (k : K) x => (U (kernelProjectionSelectedPivot code k) x).observable
  let centers := fun (k : K) i =>
    (U (kernelProjectionSelectedPivot code k) (representative i)).observable
  have hselected (a : Ω) (ha : a ∈ H) (k : K) : δ ≤
      ‖(localLaw a).complexMean (fun t => input (physical a t) *
        functions k (physical a t) (localPoint a t))‖ :=
    hscore a ha k.val (kernelProjectionSelectedPivot code k)
      (kernelProjectionSelectedPivot_spec code k)
  obtain ⟨chosen, masked, H', hmask, _, hsub, hpos, hmass, hlocal⟩ :=
    exists_simultaneous_external_pivot_masks functions centers
      (fun k => hnet (kernelProjectionSelectedPivot code k)) outer H hH
      (fun a _ => localLaw a) physical (fun a _ t => localPoint a t)
      input hB hδ herror hinput hselected
  have hmassRank : outer.mass H / (Fintype.card I : ℝ) ^ r ≤ outer.mass H' := by
    apply le_trans _ hmass
    apply div_le_div_of_nonneg_left (outer.mass_nonneg H)
      (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)
    exact pow_le_pow_right₀
      (by exact_mod_cast Fintype.card_pos : (1 : ℝ) ≤ Fintype.card I)
      (kernelProjectionPresentPivot_card_le code)
  let selectedBranch := fun k : KernelProjectionPresentPivot code =>
    (kernelProjectionSelectedPivot code k, chosen k)
  let family := externalNetMaskFamily (fun f x => (U f x).observable)
    (fun f i => (U f (representative i)).observable) hnet input
  have hfamily (k : KernelProjectionPresentPivot code) :
      family (selectedBranch k) = masked k := by
    funext x
    exact (hmask k x).symm
  obtain ⟨fixedTwist, nativeValue, native, retained, hretSub, hretPos, hretMass, hretScore⟩ :=
    exists_precenter_forecast_finiteLaw_native_partners family models
      nativeWeight degree budget sample twist hnative hmodel hM hterm
      (div_pos hδ (by positivity)) hc hterms selectedBranch
      (kernelProjectionPresentPivot_card_le code) outer H' hpos
      (fun a _ => localLaw a) physical
      (fun a k t => (U (kernelProjectionSelectedPivot code k)
        (representative (chosen k))).observable (localPoint a t))
      (fun a ha k => hresidual a (hsub ha) _ _)
      (by intro a ha k; rw [hfamily]; exact hlocal a ha k)
  refine ⟨chosen, fixedTwist, nativeValue, native, retained,
    fun a ha => hsub (hretSub ha), hretPos, ?_, fun k => hcomplex _ _, hretScore⟩
  calc
    outer.mass H / ((Fintype.card I : ℝ) ^ r * termBound ^ r)
        = (outer.mass H / (Fintype.card I : ℝ) ^ r) / termBound ^ r := by
      rw [div_div]
    _ ≤ outer.mass H' / termBound ^ r :=
      div_le_div_of_nonneg_right hmassRank (pow_nonneg (by linarith) _)
    _ ≤ outer.mass retained := hretMass

end Erdos3

end

end OAI
