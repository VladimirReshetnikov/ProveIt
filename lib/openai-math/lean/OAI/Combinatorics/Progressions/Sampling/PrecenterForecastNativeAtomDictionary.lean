/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.PrecenterForecastNativePartners

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def FiniteProbabilityWeights.sampledComplexTest
    {T X : Type*} [Fintype T] (law : FiniteProbabilityWeights T)
    (physical : T → X) (weight : T → ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun f := law.complexMean (fun t => f (physical t) * weight t)
  map_add' f g := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.add_apply, add_mul,
      mul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring

theorem exists_precenter_forecast_finiteLaw_native_partners
    {Ω T X Branch K σ Θ : Type*}
    [Fintype Ω] [Fintype T] [Fintype K]
    (input : Branch → X → ℂ) (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist)
    (hmodel : ∀ b, input b =
      (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    {M termBound delta : ℝ} {rank : ℕ}
    (hM : 0 < M) (hterm : 1 ≤ termBound) (hdelta : 0 < delta)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (selectedBranch : K → Branch) (hrank : Fintype.card K ≤ rank)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (hproductive : 0 < outer.mass productive)
    (localLaw : Ω → K → FiniteProbabilityWeights T)
    (physical : Ω → T → X) (weight : Ω → K → T → ℂ)
    (herr : ∀ a ∈ productive, ∀ k,
      ‖(localLaw a k).complexMean (fun t =>
        (models (selectedBranch k)).residual (physical a t) * weight a k t)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤
      ‖(localLaw a k).complexMean (fun t =>
        input (selectedBranch k) (physical a t) * weight a k t)‖) :
    ∃ (fixedTwist : K → Θ) (nativeValue : K → X → ℂ)
      (_native : ∀ k, NativeSampleModel nativeWeight degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      outer.mass productive / termBound ^ rank ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖(localLaw a k).complexMean (fun t =>
          (star (twist (fixedTwist k) (physical a t)) * nativeValue k (physical a t)) *
            weight a k t)‖ := by
  let selectedModel := fun k => models (selectedBranch k)
  let : ∀ k, Nonempty (Fin (selectedModel k).nterms) :=
    fun k => ⟨⟨0, (selectedModel k).positive⟩⟩
  let test := fun a k => (localLaw a k).sampledComplexTest (physical a) (weight a k)
  have heval (a) (k) (f : X → ℂ) : test a k f =
      (localLaw a k).complexMean (fun t => f (physical a t) * weight a k t) := rfl
  have hmodelComplex (k : K) : input (selectedBranch k) =
      (∑ i, ((selectedModel k).coefficient i : ℂ) • (selectedModel k).models i) +
        (selectedModel k).residual := hmodel (selectedBranch k)
  have hcComplex (k : K) : ∑ i, ‖((selectedModel k).coefficient i : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc (selectedBranch k)
  obtain ⟨partner, retained, hsub, hmass, hcorr⟩ :=
    exists_fixed_linear_model_partners_of_pointwise_error outer productive
      (fun k => input (selectedBranch k)) (fun k => (selectedModel k).residual)
      (fun k => (selectedModel k).models)
      (fun k i => ((selectedModel k).coefficient i : ℂ)) test
      hmodelComplex hdelta hM hcComplex
      (by intro a ha k; rw [heval]; exact herr a ha k)
      (by intro a ha k; rw [heval]; exact hscore a ha k)
  have hmasspos : 0 < outer.mass retained :=
    (div_pos hproductive (Finset.prod_pos (fun k _ =>
      Nat.cast_pos.mpr Fintype.card_pos))).trans_le hmass
  have hne : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmasspos
    linarith)
  obtain ⟨a₀, ha₀⟩ := hne
  have hchosen (k : K) : ∃ (t : Θ) (g : X → ℂ),
      Nonempty (NativeSampleModel nativeWeight degree budget sample g) ∧
      (selectedModel k).models (partner k) = fun x => star (twist t x) * g x := by
    rcases hnative (selectedBranch k) (partner k) with hzero | hgood
    · have hn := hcorr a₀ ha₀ k
      change delta / (2 * M) ≤ ‖test a₀ k ((models (selectedBranch k)).models (partner k))‖ at hn
      rw [hzero, map_zero, norm_zero] at hn
      have hpos : 0 < delta / (2 * M) := div_pos hdelta (by positivity)
      linarith
    · exact hgood
  choose fixedTwist nativeValue hnativeValue heq using hchosen
  refine ⟨fixedTwist, nativeValue, fun k => Classical.choice (hnativeValue k),
    retained, hsub, hmasspos, ?_, ?_⟩
  · apply le_trans _ hmass
    apply div_le_div_of_nonneg_left hproductive.le
      (Finset.prod_pos (fun k _ => Nat.cast_pos.mpr Fintype.card_pos))
    calc
      (∏ k, (Fintype.card (Fin (selectedModel k).nterms) : ℝ))
          ≤ ∏ _k : K, termBound := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro k _
        simpa only [Fintype.card_fin] using hterms (selectedBranch k)
      _ = termBound ^ Fintype.card K := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ termBound ^ rank := pow_le_pow_right₀ hterm hrank
  · intro a ha k
    have h := hcorr a ha k
    rw [heval, heq] at h
    exact h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

abbrev PrecenterForecastNativeAtomLabel {X Branch : Type*}
    (models : Branch → CenteredForecastModel X) :=
  {label : Σ b, Fin (models b).nterms // (models label.1).models label.2 ≠ 0}

noncomputable instance precenterForecastNativeAtomLabelFintype
    {X Branch : Type*} [Fintype Branch] (models : Branch → CenteredForecastModel X) :
    Fintype (PrecenterForecastNativeAtomLabel models) := by
  unfold PrecenterForecastNativeAtomLabel
  infer_instance

theorem precenterForecastNativeAtomLabel_card_le
    {X Branch : Type*} [Fintype Branch] (models : Branch → CenteredForecastModel X)
    {termBound : ℝ} (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound) :
    (Fintype.card (PrecenterForecastNativeAtomLabel models) : ℝ) ≤
      (Fintype.card Branch : ℝ) * termBound := by
  calc
    _ ≤ (Fintype.card (Σ b, Fin (models b).nterms) : ℝ) :=
      Nat.cast_le.mpr (Fintype.card_subtype_le _)
    _ = ∑ b, ((models b).nterms : ℝ) := by
      simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    _ ≤ ∑ _b : Branch, termBound := Finset.sum_le_sum (fun b _ => hterms b)
    _ = _ := by simp

structure PrecenterForecastNativeAtomDictionary
    {X Branch σ Θ : Type*} (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ) where
  twistIndex : PrecenterForecastNativeAtomLabel models → Θ
  nativeValue : PrecenterForecastNativeAtomLabel models → X → ℂ
  native : ∀ label, NativeSampleModel nativeWeight degree budget sample (nativeValue label)
  realizes : ∀ label,
    (models label.val.1).models label.val.2 =
      fun x => star (twist (twistIndex label) x) * nativeValue label x

theorem exists_precenterForecastNativeAtomDictionary
    {X Branch σ Θ : Type*} (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hnative : ∀ b i, (models b).models i ∈
      twistedNativeSampleFunctions nativeWeight degree budget sample twist) :
    Nonempty (PrecenterForecastNativeAtomDictionary models nativeWeight degree budget sample twist) := by
  have hterm (label : PrecenterForecastNativeAtomLabel models) :
      ∃ (t : Θ) (g : X → ℂ),
        Nonempty (NativeSampleModel nativeWeight degree budget sample g) ∧
        (models label.val.1).models label.val.2 = fun x => star (twist t x) * g x := by
    rcases hnative label.val.1 label.val.2 with hzero | hreal
    · exact (label.property hzero).elim
    · exact hreal
  choose twistIndex nativeValue hnativeValue hrealizes using hterm
  exact ⟨{
    twistIndex := twistIndex
    nativeValue := nativeValue
    native := fun label => Classical.choice (hnativeValue label)
    realizes := hrealizes }⟩

theorem exists_precenter_forecast_finiteLaw_native_atom_labels
    {Ω T X Branch K σ Θ : Type*}
    [Fintype Ω] [Fintype T] [Fintype K]
    (input : Branch → X → ℂ) (models : Branch → CenteredForecastModel X)
    (nativeWeight : σ → ℕ) (degree : ℕ) (budget : ℝ)
    (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (dictionary : PrecenterForecastNativeAtomDictionary models nativeWeight degree budget sample twist)
    (hmodel : ∀ b, input b =
      (∑ i, (models b).coefficient i • (models b).models i) + (models b).residual)
    {M termBound delta : ℝ} {rank : ℕ}
    (hM : 0 < M) (hterm : 1 ≤ termBound) (hdelta : 0 < delta)
    (hc : ∀ b, (∑ i, |(models b).coefficient i|) ≤ M)
    (hterms : ∀ b, ((models b).nterms : ℝ) ≤ termBound)
    (selectedBranch : K → Branch) (hrank : Fintype.card K ≤ rank)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (hproductive : 0 < outer.mass productive)
    (localLaw : Ω → K → FiniteProbabilityWeights T)
    (physical : Ω → T → X) (weight : Ω → K → T → ℂ)
    (herr : ∀ a ∈ productive, ∀ k,
      ‖(localLaw a k).complexMean (fun t =>
        (models (selectedBranch k)).residual (physical a t) * weight a k t)‖ ≤ delta / 2)
    (hscore : ∀ a ∈ productive, ∀ k, delta ≤
      ‖(localLaw a k).complexMean (fun t =>
        input (selectedBranch k) (physical a t) * weight a k t)‖) :
    ∃ (labels : K → PrecenterForecastNativeAtomLabel models) (retained : Finset Ω),
      (∀ k, (labels k).val.1 = selectedBranch k) ∧
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      outer.mass productive / termBound ^ rank ≤ outer.mass retained ∧
      ∀ a ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖(localLaw a k).complexMean (fun t =>
          (star (twist (dictionary.twistIndex (labels k)) (physical a t)) *
            dictionary.nativeValue (labels k) (physical a t)) * weight a k t)‖ := by
  let selectedModel := fun k => models (selectedBranch k)
  let : ∀ k, Nonempty (Fin (selectedModel k).nterms) :=
    fun k => ⟨⟨0, (selectedModel k).positive⟩⟩
  let test := fun a k => (localLaw a k).sampledComplexTest (physical a) (weight a k)
  have heval (a) (k) (f : X → ℂ) : test a k f =
      (localLaw a k).complexMean (fun t => f (physical a t) * weight a k t) := rfl
  have hmodelComplex (k : K) : input (selectedBranch k) =
      (∑ i, ((selectedModel k).coefficient i : ℂ) • (selectedModel k).models i) +
        (selectedModel k).residual := hmodel (selectedBranch k)
  have hcComplex (k : K) : ∑ i, ‖((selectedModel k).coefficient i : ℂ)‖ ≤ M := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hc (selectedBranch k)
  obtain ⟨partner, retained, hsub, hmass, hcorr⟩ :=
    exists_fixed_linear_model_partners_of_pointwise_error outer productive
      (fun k => input (selectedBranch k)) (fun k => (selectedModel k).residual)
      (fun k => (selectedModel k).models)
      (fun k i => ((selectedModel k).coefficient i : ℂ)) test
      hmodelComplex hdelta hM hcComplex
      (by intro a ha k; rw [heval]; exact herr a ha k)
      (by intro a ha k; rw [heval]; exact hscore a ha k)
  have hmasspos : 0 < outer.mass retained :=
    (div_pos hproductive (Finset.prod_pos (fun k _ =>
      Nat.cast_pos.mpr Fintype.card_pos))).trans_le hmass
  have hne : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmasspos
    linarith)
  obtain ⟨a₀, ha₀⟩ := hne
  have hnonzero (k : K) : (selectedModel k).models (partner k) ≠ 0 := by
    intro hzero
    have h := hcorr a₀ ha₀ k
    rw [hzero, map_zero, norm_zero] at h
    have hpos : 0 < delta / (2 * M) := div_pos hdelta (by positivity)
    linarith
  let labels : K → PrecenterForecastNativeAtomLabel models :=
    fun k => ⟨⟨selectedBranch k, partner k⟩, hnonzero k⟩
  refine ⟨labels, retained, fun _ => rfl, hsub, hmasspos, ?_, ?_⟩
  · apply le_trans _ hmass
    apply div_le_div_of_nonneg_left hproductive.le
      (Finset.prod_pos (fun k _ => Nat.cast_pos.mpr Fintype.card_pos))
    calc
      (∏ k, (Fintype.card (Fin (selectedModel k).nterms) : ℝ))
          ≤ ∏ _k : K, termBound := by
        apply Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        intro k _
        simpa only [Fintype.card_fin] using hterms (selectedBranch k)
      _ = termBound ^ Fintype.card K := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ termBound ^ rank := pow_le_pow_right₀ hterm hrank
  · intro a ha k
    have h := hcorr a ha k
    rw [heval] at h
    have heq := dictionary.realizes (labels k)
    change (selectedModel k).models (partner k) = _ at heq
    rw [heq] at h
    exact h

end Erdos3

end

end OAI
