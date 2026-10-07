import OAI.Combinatorics.Progressions.Estimates.SampledNativeModel

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_fixed_sampled_slice_model_partners
    {Ω T X K : Type*} {J : Ω → Type*} {I : K → Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype K]
    [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (weight : ∀ z, J z → T → ℂ) (selected : ∀ z, K → J z)
    (hS : ∀ z j, (slices z j).Nonempty) {cap : ℝ}
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ cap)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (v e : K → X → ℂ) (Q : ∀ k, I k → X → ℂ) (c : ∀ k, I k → ℂ)
    (hmodel : ∀ k, v k = (∑ i, c k i • Q k i) + e k)
    {delta M kappa : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : ∀ k, (∑ i, ‖c k i‖) ≤ M)
    (hproductive : kappa ≤ outer.mass productive)
    (herror : (∑ k, sampledSliceSeminorm outer physical slices weight (e k)) ≤ kappa * delta / 8)
    (hscore : ∀ z ∈ productive, ∀ k,
      delta ≤ ‖𝔼 t ∈ slices z (selected z k), v k (physical z t) * weight z (selected z k) t‖) :
    ∃ (partner : ∀ k, I k) (retained : Finset Ω),
      retained ⊆ productive ∧
      (3 * kappa / 4) / (∏ k, (Fintype.card (I k) : ℝ)) ≤ outer.mass retained ∧
      ∀ z ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖𝔼 t ∈ slices z (selected z k), Q k (partner k) (physical z t) * weight z (selected z k) t‖ := by
  let W := fun z j => normalizedSliceTest (slices z j) (weight z j)
  let test := fun z k => sampledTestLinearMap (physical z) (W z (selected z k))
  let err := fun k z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) (e k)
  have hW (z) (j) (t) : ‖W z j t‖ ≤ cap :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (hweight z j) t
  have htest (z) (_hz : z ∈ productive) (k) : ‖test z k (e k)‖ ≤ err k z := by
    change sampledSingleTestSeminorm (physical z) (W z (selected z k)) (e k) ≤ _
    dsimp only [err]
    have hb := sampledSingleTestSeminorm_bddAbove physical W hW z
    rw [Seminorm.iSup_apply hb]
    exact le_ciSup (Seminorm.bddAbove_range_iff.mp hb (e k)) (selected z k)
  have hmean : (∑ k, outer.mean (err k)) ≤ kappa * (delta / 2) / 4 := by
    change (∑ k, sampledSliceSeminorm outer physical slices weight (e k)) ≤ _
    convert herror using 1; ring
  have heval (z) (k) (f : X → ℂ) :
      test z k f = 𝔼 t ∈ slices z (selected z k), f (physical z t) * weight z (selected z k) t :=
    normalizedSliceTest_mean _ (hS z (selected z k)) _ _
  obtain ⟨partner, retained, hsub, hmass, hlocal⟩ := exists_fixed_linear_model_partners
    outer productive v e Q c test err hmodel hdelta hM hc
    (fun _ _ => apply_nonneg _ _) htest hproductive hmean
    (by intro z hz k; rw [heval]; exact hscore z hz k)
  refine ⟨partner, retained, hsub, hmass, ?_⟩
  intro z hz k
  simpa only [heval] using hlocal z hz k

theorem exists_fixed_sampled_slice_native_partners
    {Ω T X K σ Θ : Type*} {J : Ω → Type*} {I : K → Type*}
    [Fintype Ω] [Fintype T] [Nonempty T] [Fintype K]
    [∀ k, Fintype (I k)] [∀ k, Nonempty (I k)]
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (weight : ∀ z, J z → T → ℂ) (selected : ∀ z, K → J z)
    (hS : ∀ z j, (slices z j).Nonempty) {cap : ℝ}
    (hsize : ∀ z j, (Fintype.card T : ℝ) / (slices z j).card ≤ cap)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (v e : K → X → ℂ) (Q : ∀ k, I k → X → ℂ) (c : ∀ k, I k → ℂ)
    (hmodel : ∀ k, v k = (∑ i, c k i • Q k i) + e k)
    {delta M kappa : ℝ} (hdelta : 0 < delta) (hM : 0 < M)
    (hc : ∀ k, (∑ i, ‖c k i‖) ≤ M)
    (hproductive : kappa ≤ outer.mass productive)
    (herror : (∑ k, sampledSliceSeminorm outer physical slices weight (e k)) ≤ kappa * delta / 8)
    (hkappa : 0 < kappa)
    (w : σ → ℕ) (degree : ℕ) (budget : ℝ) (sample : X → σ → ℤ) (twist : Θ → X → ℂ)
    (hQ : ∀ k i, Q k i ∈ twistedNativeSampleFunctions w degree budget sample twist)
    (hscore : ∀ z ∈ productive, ∀ k,
      delta ≤ ‖𝔼 t ∈ slices z (selected z k), v k (physical z t) * weight z (selected z k) t‖) :
    ∃ (fixedTwist : K → Θ) (nativeValue : K → X → ℂ)
      (_native : ∀ k, NativeSampleModel w degree budget sample (nativeValue k))
      (retained : Finset Ω),
      retained ⊆ productive ∧ 0 < outer.mass retained ∧
      (3 * kappa / 4) / (∏ k, (Fintype.card (I k) : ℝ)) ≤ outer.mass retained ∧
      ∀ z ∈ retained, ∀ k, delta / (2 * M) ≤
        ‖𝔼 t ∈ slices z (selected z k),
          (star (twist (fixedTwist k) (physical z t)) * nativeValue k (physical z t)) *
            weight z (selected z k) t‖ := by
  obtain ⟨partner, retained, hsub, hmass, hlocal⟩ := exists_fixed_sampled_slice_model_partners
    outer productive physical slices weight selected hS hsize hweight v e Q c hmodel
    hdelta hM hc hproductive herror hscore
  have hmasspos : 0 < outer.mass retained := (div_pos
    (by positivity : 0 < 3 * kappa / 4)
    (Finset.prod_pos (fun k _ => Nat.cast_pos.mpr Fintype.card_pos))).trans_le hmass
  have hne : retained.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmasspos
    linarith)
  obtain ⟨z₀, hz₀⟩ := hne
  have hchosen (k) : ∃ (t : Θ) (g : X → ℂ),
      Nonempty (NativeSampleModel w degree budget sample g) ∧
      Q k (partner k) = fun x => star (twist t x) * g x := by
    rcases hQ k (partner k) with hzero | hnative
    · have hn := hlocal z₀ hz₀ k
      rw [hzero] at hn
      simp only [Pi.zero_apply, zero_mul] at hn
      have hpos : 0 < delta / (2 * M) := div_pos hdelta (by positivity)
      simp at hn
      linarith
    · exact hnative
  choose fixedTwist nativeValue hnative heq using hchosen
  let native := fun k => Classical.choice (hnative k)
  refine ⟨fixedTwist, nativeValue, native, retained, hsub, hmasspos, hmass, ?_⟩
  intro z hz k
  simpa only [heq k] using hlocal z hz k

end Erdos3

end

end OAI
