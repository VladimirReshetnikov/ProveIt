import OAI.Combinatorics.Progressions.Dynamics.NormalizedCoreBudget
import OAI.Combinatorics.Progressions.Estimates.RetainedShellComparison
import OAI.Combinatorics.Progressions.Estimates.ScaledConditionedComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem scaled_conditioned_error_rearrange {P a m s H E U : ℝ}
    (h : |P - a * (m * H)| ≤ m * s * (E + a * U)) :
    |P - (a * m) * H| ≤ m * s * E + a * m * s * U := by
  calc
    _ = |P - a * (m * H)| := by congr 1; ring
    _ ≤ _ := h
    _ = _ := by ring

theorem productKernel_retained_atom_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    (I : Finset ι) {r b : ℕ} (hIb : I.card ≤ b) (hr : r ≤ b - I.card)
    {κ A B M N m v τ lam ε ξ P : ℝ} (hm : 0 < m) (hv : 0 ≤ v) (hτ : 0 < τ)
    (hlam : 0 < lam) (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsmall : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i ∉ I, C i ≤ κ ^ 2)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) (hMN : M * N ≤ Real.exp P)
    (hrtail : CyclicCrootSisask.spectralIterations ξ P ≤ r)
    (x : ∀ i, X i) (y : ∀ i, Y i) (w : (∀ i, X i) → ℝ) (h g : (∀ i, Y i) → ℝ)
    (hmean : productConditionalMean μ I w x = m)
    (hHmean : productConditionalMean ν I h y ≤ lam * productConditionalMean ν I g y + lam * τ)
    (hGmean : v - τ ≤ productConditionalMean ν I g y)
    (hw : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ A ^ (2 * k))
    (hh : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν I I y h z)) ≤ B ^ (2 * k))
    (hg : ∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
      (fun z => (2 * (v + τ))⁻¹ * productSectionAverage ν I I y g z)) ≤ B ^ (2 * k))
    (hM : Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
      (fun z => m⁻¹ * productSectionAverage μ I I x w z)) ≤ M)
    (hNH : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν I I y h z)) ≤ N)
    (hNG : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
      (fun z => (2 * (v + τ))⁻¹ * productSectionAverage ν I I y g z)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w
      (fun z => h z - (1 + ε) * lam * g z) ≤
      (productCouplingAtomMass c I x y * m) * lam * (1 + 2 * ε) * τ +
        m * lam * (v + τ) * (6 + 2 * ε) * (2 : ℝ) ^ I.card * κ ^ (b - I.card) * M * N := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  let U := 2 * (κ * A ^ 2 * B ^ 2) + κ ^ r * M * N
  let E := (2 : ℝ) ^ I.card * (κ ^ (b - I.card) * M * N)
  have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans hM
  have hN0 : 0 ≤ N := (Real.sqrt_nonneg _).trans hNH
  have hcore := normalized_core_error_budget hξ hξ1 hκ0 hκhalf hM0 hN0 hMN hrtail hlow
  have hU : 4 * U ≤ ξ := hcore.2
  have hU' : 2 * U ≤ ξ := by linarith
  have hH := productKernel_scaled_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hm (by positivity : 0 < 4 * lam * (v + τ)) hκ0 (by linarith) hcap hcore.1
    x y w h hw hh hM hNH
  have hG := productKernel_scaled_conditioned_mean_comparison μ ν K C hC hbound hK I hIb hr
    hm (by positivity : 0 < 2 * (v + τ)) hκ0 (by linarith) hcap hcore.1
    x y w g hw hg hM hNG
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w h -
    productCouplingAtomMass c I x y * (productConditionalMean μ I w x * productConditionalMean ν I h y)| ≤
      m * (4 * lam * (v + τ)) * (E + productCouplingAtomMass c I x y * U) at hH
  change |productAtomTruncatedPairing c (lowDegreeCoordinateSets ι b) I x y w g -
    productCouplingAtomMass c I x y * (productConditionalMean μ I w x * productConditionalMean ν I g y)| ≤
      m * (2 * (v + τ)) * (E + productCouplingAtomMass c I x y * U) at hG
  rw [hmean] at hH hG
  have hret := retained_atom_from_normalized_errors
    (productCouplingAtomMass_nonneg c I x y) hm.le hlam.le hv hτ.le hε
    (scaled_conditioned_error_rearrange hH) (scaled_conditioned_error_rearrange hG)
    hU hU' hHmean hGmean hsmall
  rw [productAtomTruncatedPairing_sub_smul_right]
  exact hret.trans_eq (by dsimp only [E]; ring)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem CylinderRemovalChain.kernel_total_pairing_le {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (ν : ∀ i, FiniteProbabilityWeights (Y i))
    (K : ∀ i, X i → FiniteProbabilityWeights (Y i)) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i (f : Y i → ℝ), (ν i).mean f = 0 →
      (μ i).mean (fun x => (K i x).mean f ^ 2) ≤ C i * (ν i).mean (fun y => f y ^ 2))
    (hK : ∀ i (f : Y i → ℝ), (μ i).mean (fun x => (K i x).mean f) = (ν i).mean f)
    {base : ∀ i, X i} {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {L τ : ℝ} {j r b : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F L τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (baseY : ∀ i, Y i)
    (hw : ∀ z, w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    {κ A B M N v lam ε ξ P Q η shell H G : ℝ}
    (hM0 : 0 ≤ M) (hN0 : 0 ≤ N) (hv : 0 ≤ v) (hτ : 0 < τ) (hlam : 0 < lam)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hsmall : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * A ^ 2 * B ^ 2 ≤ ξ / 16) (hMN : M * N ≤ Real.exp P)
    (hrtail : CyclicCrootSisask.spectralIterations ξ P ≤ r) (hrb : j + r ≤ b)
    (hη : 0 ≤ η)
    (hclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η (2 * b))
    (herr : 2 * η * ((lowDegreeCoordinateSets ι b).card : ℝ) ^ 2 * (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (h g : (∀ i, Y i) → ℝ)
    (hh : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) h) ≤ H)
    (hg : Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b) g) ≤ G)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell Q ≤ b)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, Y i) : ℝ) *
        (cf.1.mass μ base (observedProductDensity μ p F cf.2) * lam * (v + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * M * N))).sum ≤ Real.exp Q)
    (hpieces : ∀ cf ∈ cs.zip (removedCylinderWeights F w cs),
      let m := cf.1.mass μ base (observedProductDensity μ p F cf.2)
      let x := cf.1.assignment base
      let W := observedProductDensity μ p F cf.2
      (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy μ (Finset.univ.powersetCard k)
        (fun z => m⁻¹ * productSectionAverage μ cf.1.1 cf.1.1 x W z)) ≤ A ^ (2 * k)) ∧
      Real.sqrt (productANOVAEnergy μ (lowDegreeCoordinateSets ι b)
        (fun z => m⁻¹ * productSectionAverage μ cf.1.1 cf.1.1 x W z)) ≤ M ∧
      ∀ z : ∀ i : cf.1.1, Y i,
        let y := productSubtypePoint cf.1.1 z baseY
        productConditionalMean ν cf.1.1 h y ≤ lam * productConditionalMean ν cf.1.1 g y + lam * τ ∧
        v - τ ≤ productConditionalMean ν cf.1.1 g y ∧
        (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
          (fun a => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y h a)) ≤ B ^ (2 * k)) ∧
        (∀ k, 1 ≤ k → k ≤ r → Real.sqrt (productANOVAEnergy ν (Finset.univ.powersetCard k)
          (fun a => (2 * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y g a)) ≤ B ^ (2 * k)) ∧
        Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
          (fun a => (4 * lam * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y h a)) ≤ N ∧
        Real.sqrt (productANOVAEnergy ν (lowDegreeCoordinateSets ι b)
          (fun a => (2 * (v + τ))⁻¹ * productSectionAverage ν cf.1.1 cf.1.1 y g a)) ≤ N) :
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets ι b) (observedProductDensity μ p F w)
      (fun z => h z - (1 + ε) * lam * g z) ≤
      lam * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (H + (1 + ε) * lam * G) := by
  dsimp only
  let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (K i) (hK i)
  let pref := fun (d : ProductCylinder X) (f : Ω → ℝ) (_z : ∀ i : d.1, Y i) =>
    d.mass μ base (observedProductDensity μ p F f) * lam * (v + τ) * (6 + 2 * ε) *
      (2 : ℝ) ^ d.1.card * M * N
  apply CylinderRemovalChain.total_pairing_with_shell_budget c hchain hμ _ baseY hw hrem hmass
    hη (by positivity) (by positivity) hκ0 hκhalf hshell
    (fun S hS => (mem_lowDegreeCoordinateSets ι b S).mp hS) hclose herr h g hh hg pref
  · intro cf hcf z
    have hm := hτ.trans (hchain.removed_size_mass cf hcf).2
    dsimp only [pref]
    positivity
  · simpa only [pref, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hbudget
  · exact hb
  · intro cf hcf z
    obtain ⟨hsize, hmass'⟩ := hchain.removed_size_mass cf hcf
    obtain ⟨hwl, hwm, hsite⟩ := hpieces cf hcf
    obtain ⟨hHm, hGm, hhl, hgl, hhn, hgn⟩ := hsite z
    have hp := productKernel_retained_atom_comparison μ ν K C hC hbound hK cf.1.1
      (by omega) (by omega) (hτ.trans hmass') hv hτ hlam hε hξ hξ1 hsmall hκ0 hκhalf
      (fun i _ => hcap i) hlow hMN hrtail (cf.1.assignment base)
      (productSubtypePoint cf.1.1 z baseY) (observedProductDensity μ p F cf.2) h g rfl
      hHm hGm hwl hhl hgl hwm hhn hgn
    exact hp.trans_eq (by dsimp only [pref]; ring)

end Erdos3

end

end OAI
