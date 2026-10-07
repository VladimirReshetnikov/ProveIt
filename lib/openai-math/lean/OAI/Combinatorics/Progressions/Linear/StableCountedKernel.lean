import OAI.Combinatorics.Progressions.Lattices.ResidueBaselineBounds
import OAI.Combinatorics.Progressions.Lattices.StableResidueKernelTotal

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem stable_residue_counted_kernel_total {Ω ι σ : Type*}
    [Fintype Ω]
    [Fintype ι] [LinearOrder ι] [Fintype σ] [DecidableEq σ]
    {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
    [∀ i, NeZero (q i)] {j r b moment : ℕ} {level inc δ η τ L T P : ℝ} {K : Finset ι}
    {base : ∀ i, σ → ZMod (q i)}
    {X : {i // i ∉ K} → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (μ : ∀ i, FiniteProbabilityWeights (X i)) (p : FiniteProbabilityWeights Ω)
    (F : Ω → ∀ i, X i) (sourceBase : ∀ i, X i)
    (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))
    {regK κ ε ξ shell sourceLog siteLog : ℝ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
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
    (hshell : 0 < shell) (hb : j + CyclicCrootSisask.spectralIterations shell ((j : ℝ) * (P + sourceLog + siteLog + 2) + ε + L + 2 * T + 10) ≤ b)
    (hlevel2 : level ≤ 2) (hτ1 : τ ≤ 1)
    (hsourceLog : 0 ≤ sourceLog) (hsiteLog : 0 ≤ siteLog)
    (hsourceAlphabet : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp sourceLog)
    (hsiteAlphabet : ∀ i : {i // i ∉ K}, (Fintype.card (σ → ZMod (q i.val)) : ℝ) ≤ Real.exp siteLog) :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let ν := primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    let c := fun i => FiniteProbabilityCoupling.ofKernel (μ i) (ν i) (kernel i) (hK i)
    productTruncatedPairing c (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  have hP : 0 ≤ P := (Nat.cast_nonneg (j + r)).trans hrP
  have houtside : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcount
  have hv0 := residuePrimeCoordinateMean_re_nonneg g lo N M a q K base (fun z hz => (hg z hz).1)
  have hv1 := residuePrimeCoordinateMean_re_le_one g lo N M a q K base hg
  have hbudget := hchain.shell_prefactor_le_exp (Y := fun i : {i // i ∉ K} => σ → ZMod (q i.val)) (L := L)
    hμ hw hτ hτ1 hη.le (ProductMarginalsClose.mono μ hsourceclose (by omega))
    hP hsourceLog hsiteLog houtside hsourceAlphabet hsiteAlphabet hlevel.le hlevel2 hv0 hv1 hε hτinv
  exact stable_residue_kernel_total μ p F sourceBase siteBase hchain hμ hregK hw hrem hmass
    hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv
    hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram hsourceclose hresGram
    kernel C hC hbound hK hε hξ hξ1 hslack hκ0 hκhalf hcap hlow hrtail hrb hshell hb hbudget

end Erdos3

end

end OAI
