import OAI.Combinatorics.Progressions.Dynamics.CylinderShellCountBudget
import OAI.Combinatorics.Progressions.Estimates.CylinderUniformSections
import OAI.Combinatorics.Progressions.Estimates.StableSiteSectionLengths
import OAI.Combinatorics.Progressions.Linear.KernelCylinderTotal

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem stable_residue_kernel_total {Ω ι σ : Type*}
    [Fintype Ω]
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    {X : {i // i ∉ K} → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (sourceBase : ∀ i, X i)
    (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    {regK κ ε ξ shell Q : ℝ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ sourceBase p F regK τ j r w rem cs)
    (hμ : ∀ i x, 0 < (μ i).weight x) (hregK : 1 ≤ regK)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1) (hmass : p.mean rem ≤ τ)
    (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)
    (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)
    (hM : 0 < M) (hpair : Pairwise (fun i k => (q i).Coprime (q k)))
    (hcop : ∀ i ∉ K, M.Coprime (q i)) (u : ResiduePrimeCoordinateCell lo N M a q K base)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hlevel : 0 < level) (hτ : 0 < τ) (hδ : δ ≤ τ / 8) (hinc : inc ≤ level * τ / 8)
    (hη0 : 0 ≤ η) (hη : η < 1) (hητ : η ≤ τ / 8) (hηlevel : η ≤ level * τ / 8)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hlower : Real.exp (-L) ≤ level) (hτinv : τ⁻¹ ≤ Real.exp T)
    (hlog : L + T + 2 ≤ P) (hrP : ((j + r : ℕ) : ℝ) ≤ P)
    (hmoment : 2 ≤ moment) (heven : Even moment) (hPq : P ≤ (moment : ℝ)) (hqP : (moment : ℝ) ≤ P + 2)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))
    (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)
    (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)
    (hsourceclose : ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))
    (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)
    (kernel : ∀ i : {i // i ∉ K}, X i → FiniteProbabilityWeights (σ → ZMod (q i.val)))
    (C : {i // i ∉ K} → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ,
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f = 0 →
      (μ i).mean (fun x => (kernel i x).mean f ^ 2) ≤ C i *
        (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean (fun y => f y ^ 2))
    (hK : ∀ i : {i // i ∉ K}, ∀ f : (σ → ZMod (q i.val)) → ℝ, (μ i).mean (fun x => (kernel i x).mean f) =
      (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val) i).mean f)
    (hε : 0 ≤ ε) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hslack : ξ * (2 + ε) ≤ ε)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hcap : ∀ i, C i ≤ κ ^ 2)
    (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)
    (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r) (hrb : j + r ≤ b)
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell Q ≤ b)
    (hbudget : ((cs.zip (removedCylinderWeights F w cs)).map (fun cf =>
      (Fintype.card (∀ i : cf.1.1, σ → ZMod (q i.val.val)) : ℝ) *
        (cf.1.mass μ sourceBase (observedProductDensity μ p F cf.2) * level *
          ((residuePrimeCoordinateMean g lo N M a q K base).re + τ) * (6 + 2 * ε) *
          (2 : ℝ) ^ cf.1.1.card * (3 * τ⁻¹) * (3 * Real.exp (L + T))))).sum ≤ Real.exp Q) :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  dsimp only
  let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
  have hsite := stable_site_uniform_sections hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc
    hη0 hη hητ hηlevel hL hT hlower hτinv hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram
  have hv := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  have hP : 0 ≤ P := (Nat.cast_nonneg (j + r)).trans hrP
  have hrP' : (r : ℝ) ≤ P := by
    have h : (r : ℝ) ≤ ((j + r : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left r j
    exact h.trans hrP
  have hlog' : Real.log (2 + τ⁻¹) ≤ P :=
    (log_two_add_le_of_le_exp (inv_nonneg.mpr hτ.le) hT hτinv).trans (by linarith)
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hsampleSmall := approxMoment_small_of_exponential (Fintype.card {i // i ∉ K}) r moment τ⁻¹ P
    hP (inv_nonneg.mpr hτ.le) houtside (hτinv.trans (Real.exp_le_exp.mpr (by linarith))) hrP' hqP hηsmall
  have horder : j + r * (moment + 1) ≤ (j + r) * (moment + 1) := by nlinarith
  have hsample := hchain.uniform_section_bounds hμ hregK hτ hη0 hη.le hmoment heven hrP' hlog' hPq hqP
    hsampleSmall (ProductMarginalsClose.mono μ hsourceclose
      (max_le (horder.trans (le_max_left _ _)) (le_max_right _ _))) hgram hw
  have hne := residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u
  have hHnorm := residuePrimeDensity_norm_le_three lo N (M.lcm (∏ i ∈ K, q i))
    (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (h z).re) hh
    hη0 hη.le (lowDegreeCoordinateSets {i // i ∉ K} b)
    (fun S hS => (mem_lowDegreeCoordinateSets _ b S).mp hS)
    (ProductMarginalsClose.mono ν hclose (by omega)) hgram
  have hGnorm := residuePrimeDensity_norm_le_three lo N (M.lcm (∏ i ∈ K, q i))
    (fun k => (u.val k).val) hne (fun i : {i // i ∉ K} => q i.val) (fun z => (g z).re) hg
    hη0 hη.le (lowDegreeCoordinateSets {i // i ∉ K} b)
    (fun S hS => (mem_lowDegreeCoordinateSets _ b S).mp hS)
    (ProductMarginalsClose.mono ν hclose (by omega)) hgram
  apply CylinderRemovalChain.kernel_total_pairing_le μ ν kernel C hC hbound hK hchain hμ siteBase
    (fun z => (hw z).2) hrem hmass (by positivity) (by positivity) hv hτ hlevel hε hξ hξ1 hslack
    hκ0 hκhalf hcap hlow (uniform_section_norm_product_le_exp hτ hτinv) hrtail hrb hη0
    (ProductMarginalsClose.mono μ hsourceclose (by omega)) hresGram
    _ _ hHnorm hGnorm hshell hb hbudget
  intro cf hcf
  obtain ⟨hwl, hwn⟩ := hsample cf hcf
  refine ⟨fun k _ hk => hwl k hk, hwn, ?_⟩
  intro z
  obtain ⟨hHm, hGm, hhl, hgl, hhn, hgn⟩ := hsite cf.1.1 (hchain.removed_size_mass cf hcf).1
    (productSubtypePoint cf.1.1 z siteBase)
  exact ⟨hHm, hGm, fun k _ hk => hhl k hk, fun k _ hk => hgl k hk, hhn, hgn⟩

end Erdos3

end

end OAI
