import OAI.Combinatorics.Progressions.Lattices.InitialMaskedAffineComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {Ω ι σ J : Type*} [Fintype J] [Fintype Ω] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

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

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))))

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
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include hb p F sourceBase siteBase hchain hw hrem hmass hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_residue_affine_total_at_degree :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (observedProductDensity μ p F w)
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
  have heta := affineComparisonAccuracy_bounds (b) hscale.1 hL hT hlower
  have hgram := affineComparisonAccuracy_gram (ι := {i // i ∉ K}) (b) hscale.1 hL hT hcnt'
  have hxi := retained_core_allowance_spec hε
  have hκ := affineComparisonContraction_bounds hxi.1 hscale.1
  have hdeg := affineFinalDegree_bounds (affineRemovalDepth T) (affineComparisonTail ε L T) shell
    (((affineRemovalDepth T) : ℝ) * ((affineComparisonScale ε L T C) + (Fintype.card (Option J × σ) : ℝ) * modLog +
      (Fintype.card σ : ℝ) * modLog + 2) + ε + L + 2 * T + 10)
  have hs0 := retained_residue_marginals_of_lengths (ι := ι) (σ := σ)
    lo N M a q hM hpair K base hcop u
  have hs1 := hs0 (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))) modLog dimLog
    (affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
  have hs2 := hs1 hmodLog heta.2.1.le
  have he : Real.exp (-affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T) ≤ (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T) := by
    unfold affineComparisonAccuracy
    exact le_rfl
  have hs3 := hs2 he
  have hs4 := hs3 hmoduli hdim
  have hsite := hs4 hlength
  have hrank : (affineRemovalDepth T) + (affineComparisonTail ε L T) ≤ max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) := by
    have hmul : (affineRemovalDepth T) + (affineComparisonTail ε L T) ≤ ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1) := by
      calc
        (affineRemovalDepth T) + (affineComparisonTail ε L T) = ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * 1 := (Nat.mul_one _).symm
        _ ≤ ((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1) := Nat.mul_le_mul_left _ (by omega)
    exact hmul.trans (le_max_left _ _)
  have hc0 := stable_residue_affine_total (Ω := Ω) (ι := ι) (σ := σ) (J := J)
    (h := h) (g := g) (lo := lo) (a := a) (N := N) (M := M) (q := q)
    (j := (affineRemovalDepth T)) (r := (affineComparisonTail ε L T)) (b := (b)) (moment := (affineComparisonMoment (affineComparisonScale ε L T C))) (level := level) (inc := (affineIncrementTolerance L T))
    (δ := (affineStabilityTolerance T)) (η := (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)) (τ := (Real.exp (-T))) (L := L) (T := T) (P := (affineComparisonScale ε L T C)) (K := K) (base := base)
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
    (hdeg.1.trans hb) hshell (hdeg.2.trans hb) hlevel2 htol.2.1 hmodLog hmoduli
  exact hc6

end

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
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

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

variable (hsourceclose : ProductMarginalsClose (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) (observedProductDensity (primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)) p F (fun _ => 1)) (affineComparisonAccuracy (b) (affineComparisonScale ε L T C) L T)
      (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T))))

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
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
    (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ))

include hb p F sourceBase siteBase hw hstable hupper hM hpair hcop u hg hh hL hT hlower hsourceclose prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength

theorem chosen_stable_affine_from_source_marginals_at_degree :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    let μ := primeCoordinateReference (σ := Option J × σ) (fun i : {i // i ∉ K} => q i.val)
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (observedProductDensity μ p F w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let j := affineRemovalDepth T
  let r := affineComparisonTail ε L T
  let P := affineComparisonScale ε L T C
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
  have hc := chosen_stable_residue_affine_total_at_degree (b := b) (hb := hb) (Ω := Ω) (ι := ι) (σ := σ) (J := J)
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

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

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
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
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
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) sourceM (sourceA k) : ℝ))

include hb hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceNonempty w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem residue_source_stable_affine_comparison_at_degree :
    let density := fun f => residuePrimeCoordinateDensity lo N (M.lcm (∏ i ∈ K, q i))
      (fun k => (u.val k).val) (residuePrimeCoordinateCell_lcm_nonempty lo N M a q hpair K base u)
      (fun i : {i // i ∉ K} => q i.val) f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA sourceNonempty
        (fun i : {i // i ∉ K} => q i.val) w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  let P := affineComparisonScale ε L T C
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
  have hc := chosen_stable_affine_from_source_marginals_at_degree (b := b) (hb := hb)
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

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

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
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
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
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

include hb hstable hupper hM hpair hcop u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount hmandatory dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM hsourceCop sourceDimLog hsourceDim hsourceLength

theorem conditioned_source_stable_affine_comparison_at_degree :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
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
  have result := residue_source_stable_affine_comparison_at_degree (b := b) (hb := hb) (ι := ι) (σ := σ) (J := J)
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
        (b)))
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
variable {b : ℕ}
variable (hb : affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ b)

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
variable (hlength : ∀ k, Real.exp (modLog * (max (((affineRemovalDepth T) + (affineComparisonTail ε L T)) * ((affineComparisonMoment (affineComparisonScale ε L T C)) + 1)) (2 * (b) + (affineRemovalDepth T)) : ℕ) +
    affineComparisonAccuracyLog (b) (affineComparisonScale ε L T C) L T + dimLog + 1) ≤
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
      (2 * b + affineRemovalDepth T) : ℕ) +
    affineComparisonAccuracyLog
      (b)
      (affineComparisonScale ε L T C) L T + sourceDimLog + 1) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (hmask : affineInitialPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M ⊆ K)

include hb hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem initial_masked_affine_comparison_at_degree :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (b)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
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
  exact conditioned_source_stable_affine_comparison_at_degree (b := b) (hb := hb)
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
