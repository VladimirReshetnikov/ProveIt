import OAI.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
import OAI.Combinatorics.Progressions.Linear.StableCountedKernel

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*}

variable [Fintype J]

variable [Fintype Ω]

variable [Fintype ι]

variable [LinearOrder ι]

variable [Fintype σ]

variable {h g : (σ → ℤ) → ℂ}

variable {lo a : σ → ℤ}

variable {N : σ → ℕ}

variable {M : ℕ}

variable {q : ι → ℕ}

variable [∀ i, NeZero (q i)]

variable {j r b moment : ℕ}

variable {level inc δ η τ L T P : ℝ}

variable {K : Finset ι}

variable {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {regK κ ε ξ shell modLog : ℝ}

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F regK τ j r w rem cs)

variable (hregK : 1 ≤ regK)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ τ)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q (j + r) δ K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q (j + r) level inc δ K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hlevel : 0 < level)

variable (hτ : 0 < τ)

variable (hδ : δ ≤ τ / 8)

variable (hinc : inc ≤ level * τ / 8)

variable (hη0 : 0 ≤ η)

variable (hη : η < 1)

variable (hητ : η ≤ τ / 8)

variable (hηlevel : η ≤ level * τ / 8)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hτinv : τ⁻¹ ≤ Real.exp T)

variable (hlog : L + T + 2 ≤ P)

variable (hrP : ((j + r : ℕ) : ℝ) ≤ P)

variable (hmoment : 2 ≤ moment)

variable (heven : Even moment)

variable (hPq : P ≤ (moment : ℝ))

variable (hqP : (moment : ℝ) ≤ P + 2)

variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)

variable (hηsmall : η ≤ (1 / 2) * Real.exp (-((P + 3) ^ 3)))

variable (herror : ∀ S : Finset {i // i ∉ K}, S.card ≤ j + r →
      2 * (∑ k, ((∏ i ∈ S, q i.val : ℕ) : ℝ) /
        residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val)) ≤ η)

variable (hclose : ProductMarginalsClose (primeCoordinateReference (σ := σ) (fun i : {i // i ∉ K} => q i.val))
      (residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i)) (fun k => (u.val k).val)
        (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
        (fun i : {i // i ∉ K} => q i.val) (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))

variable (hgram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ 1)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) η
      (max ((j + r) * (moment + 1)) (2 * b + j)))

variable (hresGram : 2 * η * ((lowDegreeCoordinateSets {i // i ∉ K} b).card : ℝ) ^ 2 *
      (4 : ℝ) ^ b * (1 + η) ^ 2 ≤ τ)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hlarge : ∀ i ∉ K, (prime i : ℝ)⁻¹ ≤ κ)

variable (hε : 0 ≤ ε)

variable (hξ : 0 < ξ)

variable (hξ1 : ξ ≤ 1)

variable (hslack : ξ * (2 + ε) ≤ ε)

variable (hκ0 : 0 ≤ κ)

variable (hκhalf : κ ≤ 1 / 2)

variable (hlow : κ * (8 * (1 + regK) * (P + 2)) ^ 2 * (16 * (P + 2)) ^ 2 ≤ ξ / 16)

variable (hrtail : CyclicCrootSisask.spectralIterations ξ (L + 2 * T + 4) ≤ r)

variable (hrb : j + r ≤ b)

variable (hshell : 0 < shell)

variable (hb : j + CyclicCrootSisask.spectralIterations shell ((j : ℝ) * (P + ((Fintype.card (Option J × σ) : ℝ) * modLog) + ((Fintype.card σ : ℝ) * modLog) + 2) + ε + L + 2 * T + 10) ≤ b)

variable (hlevel2 : level ≤ 2)

variable (hτ1 : τ ≤ 1)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

include p F sourceBase siteBase hchain hregK hw hrem hmass hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram hsourceclose hresGram prime power hprime hpower hJ hlarge hε hξ hξ1 hslack hκ0 hκhalf hlow hrtail hrb hshell hb hlevel2 hτ1 hmodLog hmoduli

theorem stable_residue_affine_total :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} b) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * τ + shell / 16 + Real.sqrt (3 * τ) * (3 + (1 + ε) * level * 3) := by
  let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
  have hμ : ∀ i x, 0 < (μ i).weight x := primeCoordinateReference_weight_pos _
  have hsourceAlphabet : ∀ i : {i // i ∉ K},
      (Fintype.card (Option J × σ → ZMod (q i.val)) : ℝ) ≤
        Real.exp ((Fintype.card (Option J × σ) : ℝ) * modLog) :=
    fun i => by
      simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using
        (residue_function_alphabet_card_le_exp (I := Option J × σ) (q := q i.val) (hmoduli i.val i.property))
  have hsiteAlphabet : ∀ i : {i // i ∉ K}, (Fintype.card (σ → ZMod (q i.val)) : ℝ) ≤
      Real.exp ((Fintype.card σ : ℝ) * modLog) :=
    fun i => by
      simpa only [Fintype.card_fun, ZMod.card, Nat.cast_pow] using
        (residue_function_alphabet_card_le_exp (I := σ) (q := q i.val) (hmoduli i.val i.property))
  have result := stable_residue_counted_kernel_total (Ω := Ω) (ι := ι) (σ := σ)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (j := j) (r := r) (b := b) (moment := moment) (level := level) (inc := inc)
    (δ := δ) (η := η) (τ := τ) (L := L) (T := T) (P := P) (K := K) (base := base)
    (X := fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val))
    (regK := regK) (κ := κ) (ε := ε) (ξ := ξ) (shell := shell)
    (sourceLog := (Fintype.card (Option J × σ) : ℝ) * modLog)
    (siteLog := (Fintype.card σ : ℝ) * modLog) (w := w) (rem := rem) (cs := cs)
    μ p F sourceBase siteBase hchain hμ hregK hw hrem hmass
    hstable hupper hM hpair hcop u hg hh hlevel hτ hδ hinc hη0 hη hητ hηlevel hL hT hlower hτinv
    hlog hrP hmoment heven hPq hqP hcount hηsmall herror hclose hgram hsourceclose hresGram
    (fun i => affineSampleKernel (J := J) (I := σ) (q := q i.val)) (fun _ => κ ^ 2)
    (fun _ => sq_nonneg _) (fun i f hf => affineSampleKernel_centered_sq_of_inverse_le
      (hprime i.val) (hpower i.val) hJ hκ0 (hlarge i.val i.property) f hf)
    (fun i f => affineSampleKernel_preserves_mean (J := J) (I := σ) (q := q i.val) f)
    hε hξ hξ1 hslack hκ0 hκhalf (fun _ => le_rfl) hlow hrtail hrb hshell hb hlevel2 hτ1
    (by positivity) (by positivity) hsourceAlphabet hsiteAlphabet
  exact result

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def affineComparisonDegree (sourceDim siteDim : ℕ) (ε L T C shell modLog : ℝ) : ℕ :=
  let j := affineRemovalDepth T
  let r := affineComparisonTail ε L T
  let P := affineComparisonScale ε L T C
  affineFinalDegree j r shell
    ((j : ℝ) * (P + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2) + ε + L + 2 * T + 10)

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w rem : Ω → ℝ}

variable {cs : List (ProductCylinder (fun i : {i // i ∉ K} => Option J × σ → ZMod (q i.val)))}

variable (hchain : CylinderRemovalChain (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) sourceBase p F (2 : ℝ) (Real.exp (-T)) (affineRemovalDepth T) (affineComparisonTail ε L T) w rem cs)

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hrem : ∀ z, 0 ≤ rem z ∧ rem z ≤ 1)

variable (hmass : p.mean rem ≤ (Real.exp (-T)))

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include p F sourceBase siteBase hchain hw hrem hmass hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_residue_affine_total :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  have hscale := affineComparisonScale_bounds (ε := ε) hL hT hC
  have hlargeStep := affineMandatoryPrimes_outside_inverse (ι := ι) (ξ := (ε / (2 + ε))) (P := (affineComparisonScale ε L T C))
    prime hscale.1 K
  have hlarge := hlargeStep hmandatory
  have hmom := affineComparisonMoment_bounds hscale.1
  have hcnt : (Fintype.card ι : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) := affineComparisonScale_count (ι := ι) (ε := ε) hL hT hC hcount
  have hcnt' : (Fintype.card {i // i ∉ K} : ℝ) ≤ Real.exp (affineComparisonScale ε L T C) :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hcnt
  have htol := affineComparisonTolerance_bounds hT hlower
  have heta := affineComparisonAccuracy_bounds (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) hscale.1 hL hT hlower
  have hgram := affineComparisonAccuracy_gram (ι := {i // i ∉ K}) (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) hscale.1 hL hT hcnt'
  have hxi := retained_core_allowance_spec hε
  have hκ := affineComparisonContraction_bounds hxi.1 hscale.1
  have hdeg := affineFinalDegree_bounds (affineRemovalDepth T) (affineComparisonTail ε L T) shell
    (((affineRemovalDepth T) : ℝ) * ((affineComparisonScale ε L T C) + (Fintype.card (Option J × σ) : ℝ) * modLog +
      (Fintype.card σ : ℝ) * modLog + 2) + ε + L + 2 * T + 10)
  have hs0 := retained_residue_marginals_of_lengths (ι := ι) (σ := σ)
    lo N M a q hM hpair K base hcop u
  have hs1 := hs0 (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T))) modLog dimLog
    (affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T) (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T)
  have hs2 := hs1 hmodLog heta.2.1.le
  have he : Real.exp (-affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T) ≤ (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T) := by
    unfold affineComparisonAccuracy
    exact le_rfl
  have hs3 := hs2 he
  have hs4 := hs3 hmoduli hdim
  have hsite := hs4 hlength
  have hrank : (affineRemovalDepth T) + (affineComparisonTail ε L T) ≤ max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) := by
    have hmul : (affineRemovalDepth T) + (affineComparisonTail ε L T) ≤ ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1) := by
      calc
        (affineRemovalDepth T) + (affineComparisonTail ε L T) = ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * 1 := (Nat.mul_one _).symm
        _ ≤ ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1) := Nat.mul_le_mul_left _ (by omega)
    exact hmul.trans (le_max_left _ _)
  have hc0 := stable_residue_affine_total (Ω := Ω) (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (j := (affineRemovalDepth T)) (r := (affineComparisonTail ε L T)) (b := (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)) (moment := (affineComparisonMoment (affineComparisonScale ε L T C))) (level := level) (inc := (affineIncrementTolerance L T))
    (δ := (affineStabilityTolerance T)) (η := (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T)) (τ := (Real.exp (-T))) (L := L) (T := T) (P := (affineComparisonScale ε L T C)) (K := K) (base := base)
    (regK := 2) (κ := (affineComparisonContraction (ε / (2 + ε)) (affineComparisonScale ε L T C))) (ε := ε) (ξ := (ε / (2 + ε))) (shell := shell) (modLog := modLog)
    (w := w) (rem := rem) (cs := cs)
    p F sourceBase siteBase hchain (by norm_num) hw hrem hmass hstable hupper hM hpair hcop u hg hh
  have hc1 := hc0 htol.2.2.2.1 htol.1 htol.2.2.2.2.2.1 htol.2.2.2.2.2.2.2
    heta.1.le heta.2.1 heta.2.2.1 heta.2.2.2.1 hL hT hlower htol.2.2.1
  have hc2 := hc1 hscale.2.1 hscale.2.2.1 hmom.1 hmom.2.1 hmom.2.2.1 hmom.2.2.2 hcnt heta.2.2.2.2
  have hc3 := hc2 (fun S hS => hsite.2 S (hS.trans hrank)) hsite.1 (hgram.trans htol.2.1) hsourceclose hgram
  have hc4a := hc3 prime power
  have hc4b := hc4a hprime hpower hJ
  have hc4 := hc4b hlarge
  have hc5 := hc4 hε.le hxi.1 hxi.2.1 hxi.2.2 hκ.1.le hκ.2.1 hκ.2.2
  have htail : CyclicCrootSisask.spectralIterations (ε / (2 + ε)) (L + 2 * T + 4) ≤ (affineComparisonTail ε L T) := by
    unfold affineComparisonTail
    exact le_rfl
  have hc6 := hc5 htail
    hdeg.1 hshell hdeg.2 hlevel2 htol.2.1 hmodLog hmoduli
  exact hc6

end

end Erdos3

end

section

namespace Erdos3

theorem affineComparisonAccuracyLog_mono_degree {b B : ℕ} {P L T : ℝ}
    (hb : b ≤ B) (hP : 0 ≤ P) :
    affineComparisonAccuracyLog b P L T ≤ affineComparisonAccuracyLog B P L T := by
  unfold affineComparisonAccuracyLog
  gcongr

theorem affineComparisonAccuracy_antitone_degree {b B : ℕ} {P L T : ℝ}
    (hb : b ≤ B) (hP : 0 ≤ P) :
    affineComparisonAccuracy B P L T ≤ affineComparisonAccuracy b P L T := by
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (affineComparisonAccuracyLog_mono_degree hb hP)

noncomputable def affineComparisonRequiredOrder (b : ℕ) (ε L T C : ℝ) : ℕ :=
  max ((affineRemovalDepth T + affineComparisonTail ε L T) *
    (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
    (2 * b + affineRemovalDepth T)

noncomputable def affineComparisonLengthLog (b : ℕ) (ε L T C modLog dimLog : ℝ) : ℝ :=
  modLog * (affineComparisonRequiredOrder b ε L T C : ℕ) +
    affineComparisonAccuracyLog b (affineComparisonScale ε L T C) L T + dimLog + 1

theorem affineComparisonRequiredOrder_mono {b B : ℕ} (hb : b ≤ B) (ε L T C : ℝ) :
    affineComparisonRequiredOrder b ε L T C ≤ affineComparisonRequiredOrder B ε L T C := by
  unfold affineComparisonRequiredOrder
  omega

theorem affineComparisonRequiredOrder_two_mul (b : ℕ) (ε L T C : ℝ) :
    2 * b ≤ affineComparisonRequiredOrder b ε L T C := by
  unfold affineComparisonRequiredOrder
  omega

theorem affineComparisonLengthLog_mono_degree {b B : ℕ} {ε L T C modLog dimLog : ℝ}
    (hb : b ≤ B) (hP : 0 ≤ affineComparisonScale ε L T C) (hmodLog : 0 ≤ modLog) :
    affineComparisonLengthLog b ε L T C modLog dimLog ≤
      affineComparisonLengthLog B ε L T C modLog dimLog := by
  unfold affineComparisonLengthLog
  have ho : (affineComparisonRequiredOrder b ε L T C : ℝ) ≤
      (affineComparisonRequiredOrder B ε L T C : ℝ) := by
    exact_mod_cast affineComparisonRequiredOrder_mono hb ε L T C
  have ha := affineComparisonAccuracyLog_mono_degree (L := L) (T := T) hb hP
  have hm := mul_le_mul_of_nonneg_left ho hmodLog
  linarith

theorem affineComparisonLengthLog_initial {ε L T C modLog dimLog : ℝ} (B : ℕ)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hmodLog : 0 ≤ modLog) :
    modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 + dimLog + 1 ≤
      affineComparisonLengthLog B ε L T C modLog dimLog := by
  have ho : ((2 * B : ℕ) : ℝ) ≤ (affineComparisonRequiredOrder B ε L T C : ℝ) := by
    exact_mod_cast affineComparisonRequiredOrder_two_mul B ε L T C
  have ha : affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 ≤
      affineComparisonAccuracyLog B (affineComparisonScale ε L T C) L T := by
    unfold affineComparisonAccuracyLog
    linarith
  have hm := mul_le_mul_of_nonneg_left ho hmodLog
  change _ ≤ _
  dsimp only [affineComparisonLengthLog]
  linarith

theorem affineGlobalCutoff_outside {A B n b : ℕ} (hn : n ≤ A) (hB : A + b ≤ B) :
    b ≤ B - n ∧ B - n ≤ B ∧ n ≤ B := by omega

theorem CyclicCrootSisask.spectralIterations_mono_budget {shell P Q : ℝ} (hPQ : P ≤ Q) :
    CyclicCrootSisask.spectralIterations shell P ≤ CyclicCrootSisask.spectralIterations shell Q := by
  unfold CyclicCrootSisask.spectralIterations
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem affineGlobalCutoff_initial {n A B : ℕ} {V W shell : ℝ}
    (hn : n ≤ A) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hB : A + CyclicCrootSisask.spectralIterations shell ((A : ℝ) * (V + W + 1) + 4) ≤ B) :
    n + CyclicCrootSisask.spectralIterations shell ((n : ℝ) * (V + W + 1) + 4) ≤ B := by
  have hn' : (n : ℝ) ≤ A := by exact_mod_cast hn
  have hp : (n : ℝ) * (V + W + 1) + 4 ≤ (A : ℝ) * (V + W + 1) + 4 := by gcongr
  have hs := CyclicCrootSisask.spectralIterations_mono_budget (shell := shell) hp
  omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (p : FiniteProbabilityWeights Ω)

variable (F : Ω → ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (sourceBase : ∀ i : {i // i ∉ K}, Option J × σ → ZMod (q i.val))

variable (siteBase : ∀ i : {i // i ∉ K}, σ → ZMod (q i.val))

variable {w : Ω → ℝ}

variable (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1)

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T))))

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include p F sourceBase siteBase hw hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_affine_from_source_marginals :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let j := affineRemovalDepth T
  let r := affineComparisonTail ε L T
  let P := affineComparisonScale ε L T C
  let b := affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog
  let η := affineComparisonAccuracy b P L T
  let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
  have hscale := affineComparisonScale_bounds (ε := ε) hL hT hC
  have heta := affineComparisonAccuracy_bounds b hscale.1 hL hT hlower
  have hrank : j + r ≤ max ((j + r) * (affineComparisonMoment P + 1)) (2 * b + j) := by
    have hm : j + r ≤ (j + r) * (affineComparisonMoment P + 1) := by
      calc
        j + r = (j + r) * 1 := (Nat.mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    exact hm.trans (le_max_left _ _)
  obtain ⟨rem, cs, hchain, _, hmass, hrem⟩ :=
    exists_finite_cylinder_removal μ (primeCoordinateReference_weight_pos _)
      sourceBase p F 2 (Real.exp (-T)) η j r (by norm_num) (Real.exp_pos _).le heta.2.1.le
      (affineRemovalDepth_cutoff T) (ProductMarginalsClose.mono μ hsourceclose hrank)
      w (fun z => (hw z).1) (fun z => (hw z).2)
  have hc := chosen_stable_residue_affine_total (Ω := Ω) (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (ε := ε) (L := L) (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base) (w := w) (rem := rem) (cs := cs)
    p F sourceBase siteBase hchain hw hrem hmass hstable hupper hM hpair hcop u hg hh
  exact hc hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2
    hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem affineComparisonLengthLog_nonneg {ε L T C modLog dimLog : ℝ} (B : ℕ)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmodLog : 0 ≤ modLog) (hdim : 0 ≤ dimLog) :
    0 ≤ affineComparisonLengthLog B ε L T C modLog dimLog := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  unfold affineComparisonLengthLog affineComparisonAccuracyLog
  positivity

theorem affineComparisonLengthLog_base_order {A B : ℕ} {ε L T C modLog dimLog : ℝ}
    (hAB : A ≤ B) (hmodLog : 0 ≤ modLog) :
    modLog * A + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) L T + dimLog + 1 ≤
      affineComparisonLengthLog B ε L T C modLog dimLog := by
  have horder := affineComparisonRequiredOrder_two_mul B ε L T C
  have hnat : A ≤ affineComparisonRequiredOrder B ε L T C := by omega
  have hreal : (A : ℝ) ≤ (affineComparisonRequiredOrder B ε L T C : ℝ) := by exact_mod_cast hnat
  have hm := mul_le_mul_of_nonneg_left hreal hmodLog
  unfold affineComparisonLengthLog
  linarith

theorem residuePrime_retained_length_uniform {ι : Type*} [DecidableEq ι]
    (q : ι → ℕ) (hqpos : ∀ i, 0 < q i) (M : ℕ) (hM : 0 < M)
    (K : Finset ι) {A : ℕ} (hK : K.card ≤ A)
    {periodLog modLog targetLog : ℝ} (hmodLog : 0 ≤ modLog) (htarget : 0 ≤ targetLog)
    (hperiod : (M : ℝ) ≤ Real.exp periodLog) (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (lo anchor : ℤ) (N : ℕ)
    (hside : Real.exp (periodLog + modLog * A + targetLog + 2) ≤ (N : ℝ)) :
    Real.exp targetLog ≤ (residueIndexLength lo (lo + N) (M.lcm (∏ i ∈ K, q i)) anchor : ℝ) := by
  have hm := residuePrimeModulus_le_exp q hqpos K M hM periodLog modLog (A : ℝ)
    hmodLog hperiod hmoduli (by exact_mod_cast hK)
  have hpos : 0 < M.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hM.ne' (Finset.prod_pos (fun i _ => hqpos i)).ne')
  exact residueIndexLength_large_of_exp lo anchor N _ _ targetLog hpos htarget hm hside

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceNonempty : Nonempty (IntegerResidueBox sourceLo
  (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA))
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
    (fun _ => (sourceM : ℤ)) sourceA,
  0 ≤ w (fun k => (z k).val) ∧ w (fun k => (z k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) sourceM (sourceA k) : ℝ))

include hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceNonempty w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem residue_source_stable_affine_comparison :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)) (residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA sourceNonempty
        (fun i : {i // i ∉ K} => q i.val) w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let P := affineComparisonScale ε L T C
  let b := affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog
  let η := affineComparisonAccuracy b P L T
  let R := max ((affineRemovalDepth T + affineComparisonTail ε L T) * (affineComparisonMoment P + 1))
    (2 * b + affineRemovalDepth T)
  let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
  let p := @FiniteProbabilityWeights.uniform
    (IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA) _ sourceNonempty
  let F := fun z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
      (fun _ => (sourceM : ℤ)) sourceA =>
    primeCoordinateObservation (fun i : {i // i ∉ K} => q i.val) (fun k => (z k).val)
  have hscale := affineComparisonScale_bounds (ε := ε) hL hT hC
  have heta := affineComparisonAccuracy_bounds b hscale.1 hL hT hlower
  have hpair' : Pairwise (fun i k : {i // i ∉ K} => (q i.val).Coprime (q k.val)) :=
    fun i k hik => hpair (fun heq => hik (Subtype.ext heq))
  have hsrc0 := residuePrimeDensity_close_of_lengths (ι := {i // i ∉ K}) (σ := Option J × σ)
    sourceLo sourceN sourceM sourceA sourceNonempty (fun i : {i // i ∉ K} => q i.val)
    hsourceM (fun i => hsourceCop i.val i.property) hpair'
    R modLog sourceDimLog (affineComparisonAccuracyLog b P L T) η
  have he : Real.exp (-affineComparisonAccuracyLog b P L T) ≤ η := by
    unfold η affineComparisonAccuracy
    exact le_rfl
  have hsrc1 := hsrc0 hmodLog heta.2.1.le he
  have hsrc := hsrc1 (fun i => hmoduli i.val i.property) hsourceDim hsourceLength
  change ProductMarginalsClose μ (observedProductDensity μ p F (fun _ => 1)) η R at hsrc
  have hc := chosen_stable_affine_from_source_marginals
    (Ω := IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k) (fun _ => (sourceM : ℤ)) sourceA)
    (ι := ι) (σ := σ) (J := J) (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (ε := ε) (L := L) (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base) (w := fun z => w (fun k => (z k).val))
    p F (fun _ _ => 0) (fun _ _ => 0) hw hstable hupper hM hpair hcop u hg hh hL hT hlower
  exact hc hsrc prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC
    hcount hmandatory dimLog hdim hlength

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem unconditioned_affine_cell_bounds {ι σ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (1 : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (hpair : Pairwise (fun i j => (q i).Coprime (q j)))
    {A B : ℕ} (hAB : A ≤ B) {ε L T C modLog dimLog : ℝ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmodLog : 0 ≤ modLog) (hdimLog : 0 ≤ dimLog)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hside : ∀ k, Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog dimLog + 2) ≤ (N k : ℝ)) :
    ProductMarginalsClose (primeCoordinateReference (σ := σ) q)
      (residuePrimeCoordinateDensity lo N 1 a hne q (fun _ => 1))
      (affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) A ∧
    (∀ (K : Finset ι), K.card ≤ A → ∀ base : ∀ i, σ → ZMod (q i),
      Nonempty (ResiduePrimeCoordinateCell lo N 1 a q K base)) ∧
    (∀ (K : Finset ι), K.card ≤ A → ∀ (base : ∀ i, σ → ZMod (q i))
      (u : ResiduePrimeCoordinateCell lo N 1 a q K base) (k : σ),
      Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
        (residueIndexLength (lo k) (lo k + N k) (Nat.lcm 1 (∏ i ∈ K, q i)) ((u.val k).val) : ℝ)) := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have heta := affineComparisonAccuracy_bounds (level := Real.exp (-L)) B hP hL hT le_rfl
  have hlog := affineComparisonLengthLog_nonneg (ε := ε) B hL hT hC hmodLog hdimLog
  have hret (K : Finset ι) (hK : K.card ≤ A) (anchor : ℤ) (k : σ) :
      Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
        (residueIndexLength (lo k) (lo k + N k) (Nat.lcm 1 (∏ i ∈ K, q i)) anchor : ℝ) := by
    apply residuePrime_retained_length_uniform q (fun i => Nat.pos_of_ne_zero (NeZero.ne (q i))) 1
      (by decide) K hK hmodLog hlog (periodLog := 0) (by simp) hmoduli
    simpa only [zero_add] using hside k
  have hbase (k : σ) :
      Real.exp (modLog * A + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
        (residueIndexLength (lo k) (lo k + N k) 1 (a k) : ℝ) := by
    apply (Real.exp_le_exp.mpr (affineComparisonLengthLog_base_order hAB hmodLog)).trans
    simpa using hret ∅ (by simp) (a k) k
  have hclose := residuePrimeDensity_close_of_lengths lo N 1 a hne q (by decide) (by simp) hpair
    A modLog dimLog (affineComparisonAccuracyLog B (affineComparisonScale ε L T C) L T)
    (affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) hmodLog heta.2.1.le
    (by exact le_rfl) hmoduli hdim hbase
  refine ⟨hclose, ?_, ?_⟩
  · intro K hK base
    exact residuePrimeCoordinateCell_nonempty_of_marginals lo N 1 a hne q hclose heta.2.1 K hK base
  · intro K hK base u k
    exact hret K hK ((u.val k).val) k

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (hpair : Pairwise (fun i k => (q i).Coprime (q k)))

variable (hcop : ∀ i ∉ K, M.Coprime (q i))

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (hmandatory : affineMandatoryPrimes prime (ε / (2 + ε)) (affineComparisonScale ε L T C) ⊆ K)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i))
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

include hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem conditioned_source_stable_affine_comparison :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let e := residuePrimeCoordinateCell_lcmEquiv sourceLo sourceN sourceM sourceA q hpair K sourceBase sourceCell
  have hQ : 0 < sourceM.lcm (∏ i ∈ K, q i) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hsourceM.ne'
      (Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (NeZero.ne (q i)))).ne')
  have hQcop : ∀ i ∉ K, (sourceM.lcm (∏ k ∈ K, q k)).Coprime (q i) :=
    fun i hi => selectedCombined_coprime_outside q hpair sourceM K hsourceCop i hi
  have hw' (z : IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
      (fun _ => (sourceM.lcm (∏ i ∈ K, q i) : ℤ)) (fun k => (sourceCell.val k).val)) :
      0 ≤ w (fun k => (z k).val) ∧ w (fun k => (z k).val) ≤ 1 :=
    hw (e.symm z)
  have result := residue_source_stable_affine_comparison (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (ε := ε) (L := L) (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base)
    (hstable := hstable) (hupper := hupper) (hM := hM) (hpair := hpair) (hcop := hcop)
    (u := u) (hg := hg) (hh := hh) (hL := hL) (hT := hT) (hlower := hlower)
    (prime := prime) (power := power) (hprime := hprime) (hpower := hpower) (hJ := hJ)
    (hshell := hshell) (hlevel2 := hlevel2) (hmodLog := hmodLog) (hmoduli := hmoduli)
    (hε := hε) (hC := hC) (hcount := hcount) (hmandatory := hmandatory)
    (dimLog := dimLog) (hdim := hdim) (hlength := hlength)
    (sourceLo := sourceLo) (sourceN := sourceN) (sourceM := sourceM.lcm (∏ i ∈ K, q i))
    (sourceA := fun k => (sourceCell.val k).val)
    (sourceNonempty := residuePrimeCoordinateCell_lcm_nonempty sourceLo sourceN sourceM sourceA q hpair K sourceBase sourceCell)
    (w := w) (hw := hw') (hsourceM := hQ) (hsourceCop := hQcop)
    (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim) (hsourceLength := hsourceLength)
  have hsrc := residueCellOutsideDensity_lcm sourceLo sourceN sourceM sourceA q hpair K sourceBase sourceCell w
  have hsiteH := residueCellOutsideDensity_lcm lo N M a q hpair K base u (fun x => (h x).re)
  have hsiteG := residueCellOutsideDensity_lcm lo N M a q hpair K base u (fun x => (g x).re)
  have htest := congrArg₂
    (fun f g : (∀ i : {i // i ∉ K}, σ → ZMod (q i.val)) → ℝ =>
      fun z => f z - (1 + ε) * level * g z) hsiteH hsiteG
  have heq := congrArg₂
    (affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K}
        (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)))
    hsrc htest
  exact heq.trans_le result

end

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}

variable (hstable : ResiduePrimeCoordinateStable g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) (affineStabilityTolerance T) K base)

variable (hupper : PrimeRefinementUpperBound h g lo N M a q ((affineRemovalDepth T) + (affineComparisonTail ε L T)) level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)

variable (hM : 0 < M)

variable (u : ResiduePrimeCoordinateCell lo N M a q K base)

variable (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)

variable (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)

variable (hL : 0 ≤ L)

variable (hT : 0 ≤ T)

variable (hlower : Real.exp (-L) ≤ level)

variable (prime power : ι → ℕ)

variable (hprime : ∀ i, (prime i).Prime)

variable (hpower : ∀ i, q i = prime i ^ power i)

variable (hJ : 2 ≤ Fintype.card J)

variable (hshell : 0 < shell)

variable (hlevel2 : level ≤ 2)

variable (hmodLog : 0 ≤ modLog)

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

variable (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ) (sourceM : ℕ)
variable (sourceBase : ∀ i, Option J × σ → ZMod (q i))
variable (sourceCell : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase)
variable (w : (Option J × σ → ℤ) → ℝ)
variable (hw : ∀ z : ResiduePrimeCoordinateCell sourceLo sourceN sourceM sourceA q K sourceBase,
  0 ≤ w (fun k => (z.val k).val) ∧ w (fun k => (z.val k).val) ≤ 1)
variable (hsourceM : 0 < sourceM)
variable (sourceDimLog : ℝ)
variable (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
variable (hsourceLength : ∀ k, Real.exp (modLog *
    (max ((affineRemovalDepth T + affineComparisonTail ε L T) *
      (affineComparisonMoment (affineComparisonScale ε L T C) + 1))
      (2 * affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (hmask : affineInitialPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M ⊆ K)

include hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem initial_masked_affine_comparison :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  have hpair : Pairwise (fun i k => (q i).Coprime (q k)) := by
    intro i k hik
    rw [hpower i, hpower k]
    exact selectedPrimePowers_pairwise_coprime prime power hprime hinj hik
  have hboth := affineInitialPrimeMask_outside_coprime (ι := ι) prime power hprime
    (ξ := ε / (2 + ε)) (P := affineComparisonScale ε L T C) (sourceM := sourceM) (siteM := M) K hmask
  have hcop : ∀ i ∉ K, M.Coprime (q i) := by
    intro i hi
    rw [hpower i]
    exact (hboth i hi).2
  have hsourceCop : ∀ i ∉ K, sourceM.Coprime (q i) := by
    intro i hi
    rw [hpower i]
    exact (hboth i hi).1
  have hmandatory :=
    (affineInitialPrimeMask_contains prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M).1.trans hmask
  exact conditioned_source_stable_affine_comparison
    (ι := ι) (σ := σ) (J := J) (h := h)
    (g := g) (lo := lo) (a := a) (N := N)
    (M := M) (q := q) (ε := ε) (L := L)
    (T := T) (C := C) (shell := shell) (modLog := modLog)
    (level := level) (K := K) (base := base) (hstable := hstable)
    (hupper := hupper) (hM := hM) (hpair := hpair) (hcop := hcop)
    (u := u) (hg := hg) (hh := hh) (hL := hL)
    (hT := hT) (hlower := hlower) (prime := prime) (power := power)
    (hprime := hprime) (hpower := hpower) (hJ := hJ) (hshell := hshell)
    (hlevel2 := hlevel2) (hmodLog := hmodLog) (hmoduli := hmoduli) (hε := hε)
    (hC := hC) (hcount := hcount) (hmandatory := hmandatory) (dimLog := dimLog)
    (hdim := hdim) (hlength := hlength) (sourceLo := sourceLo) (sourceN := sourceN)
    (sourceM := sourceM) (sourceA := sourceA) (sourceBase := sourceBase) (sourceCell := sourceCell)
    (w := w) (hw := hw) (hsourceM := hsourceM) (hsourceCop := hsourceCop)
    (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim) (hsourceLength := hsourceLength)

end

end Erdos3

end

end OAI
