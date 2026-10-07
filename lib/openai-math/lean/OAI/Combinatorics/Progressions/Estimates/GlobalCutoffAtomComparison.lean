import OAI.Combinatorics.Progressions.Lattices.AffineMaskedInitialShell
import OAI.Combinatorics.Progressions.Lattices.GlobalCutoffAffineComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

section

variable {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
variable {h g : (σ → ℤ) → ℂ} {lo a : σ → ℤ} {N : σ → ℕ} {M : ℕ} {q : ι → ℕ}
variable [∀ i, NeZero (q i)]
variable {ε L T C shell modLog level : ℝ} {K : Finset ι} {base : ∀ i, σ → ZMod (q i)}
variable {A B : ℕ}
variable (hKcard : K.card ≤ A)
variable (hB : A + affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C shell modLog ≤ B)

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

variable (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)

variable (hε : 0 < ε)
variable (hC : 0 ≤ C)
variable (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
variable (dimLog : ℝ)
variable (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
variable (hlength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog dimLog) ≤
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
variable (hsourceLength : ∀ k, Real.exp (affineComparisonLengthLog B ε L T C modLog sourceDimLog) ≤
    (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ))

variable (hinj : Function.Injective prime)
variable (D : ℕ) (parameterA : J → ℤ)
variable (hmask : affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M D ⊆ K)
variable (hBinitial : A + CyclicCrootSisask.spectralIterations shell
  ((A : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B)

include D parameterA hBinitial hKcard hB hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem global_cutoff_initial_atom_comparison :
    let c := affinePeriodProductCoupling (σ := σ) q D parameterA
    let source := residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ q w
    let site := fun f => residuePrimeCoordinateDensity lo N M a ⟨u.val⟩ q f
    let factor := productCouplingAtomMass c K sourceBase base *
      (residuePrimeCoordinateMassRatio sourceLo sourceN sourceM sourceA q K sourceBase *
        residuePrimeCoordinateMassRatio lo N M a q K base)
    productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source
      (fun z => site (fun x => (h x).re) z - (1 + ε) * level * site (fun x => (g x).re) z) ≤
      factor * (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
        Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (shell / 16) := by
  let c := affinePeriodProductCoupling (σ := σ) q D parameterA
  let source := residuePrimeCoordinateDensity sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ q w
  let site := fun f => residuePrimeCoordinateDensity lo N M a ⟨u.val⟩ q f
  let sourceOut := residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w
  let siteOut := fun f => residueCellOutsideDensity lo N M a q K base u f
  let full := fun f => productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source (site f)
  let core := fun f => affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
    (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)) sourceOut (siteOut f)
  let ratioX := residuePrimeCoordinateMassRatio sourceLo sourceN sourceM sourceA q K sourceBase
  let ratioY := residuePrimeCoordinateMassRatio lo N M a q K base
  let mass := productCouplingAtomMass c K sourceBase base
  let factor := mass * (ratioX * ratioY)
  let coeff := (1 + ε) * level
  let R := level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
    Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hcountP := affineComparisonScale_count (ι := ι) (ε := ε) hL hT hC hcount
  have hxi := (retained_core_allowance_spec hε).1
  have hmaskBase := (affineSamplerPrimeMask_contains prime (ε / (2 + ε))
    (affineComparisonScale ε L T C) sourceM M D).1.trans hmask
  have hlocal := global_cutoff_masked_affine_comparison (hKcard := hKcard) (hB := hB)
    (ι := ι) (σ := σ) (J := J) (h := h) (g := g) (lo := lo) (a := a) (N := N)
    (M := M) (q := q) (ε := ε) (L := L) (T := T) (C := C) (shell := shell)
    (modLog := modLog) (level := level) (K := K) (base := base)
    (hstable := hstable) (hupper := hupper) (hM := hM) (u := u) (hg := hg) (hh := hh)
    (hL := hL) (hT := hT) (hlower := hlower) (prime := prime) (power := power)
    (hprime := hprime) (hpower := hpower) (hJ := hJ) (hshell := hshell) (hlevel2 := hlevel2)
    (hmodLog := hmodLog) (hmoduli := fun i _ => hmoduli i) (hε := hε) (hC := hC) (hcount := hcount)
    (dimLog := dimLog) (hdim := hdim) (hlength := hlength)
    (sourceLo := sourceLo) (sourceA := sourceA) (sourceN := sourceN) (sourceM := sourceM)
    (sourceBase := sourceBase) (sourceCell := sourceCell) (w := w) (hw := hw)
    (hsourceM := hsourceM) (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim)
    (hsourceLength := hsourceLength) (hinj := hinj) (hmask := hmaskBase)
  dsimp only at hlocal
  simp only [affineResidueTruncatedPairing, productTruncatedPairing_sub_smul_right] at hlocal
  change core (fun x => (h x).re) - coeff * core (fun x => (g x).re) ≤ R at hlocal
  have hlengthInitial (k : σ) :
      Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 + dimLog + 1) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_initial (ε := ε) (C := C) B hL hT hmodLog)).trans (hlength k)
  have hsourceLengthInitial (k : Option J × σ) :
      Real.exp (modLog * (2 * B : ℕ) + affineComparisonAccuracyLog B (affineComparisonScale ε L T C) 0 0 + sourceDimLog + 1) ≤
      (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_initial (ε := ε) (C := C) B hL hT hmodLog)).trans (hsourceLength k)
  have hcut := affineGlobalCutoff_initial hKcard
    (by positivity : 0 ≤ (Fintype.card (Option J × σ) : ℝ) * modLog)
    (by positivity : 0 ≤ (Fintype.card σ : ℝ) * modLog) hBinitial
  have herror (f : (σ → ℤ) → ℝ)
      (hf : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1) :
      |full f - factor * core f| ≤ shell / 16 := by
    have hcell (z : ResiduePrimeCoordinateCell lo N M a q K base) :
        0 ≤ f (fun k => (z.val k).val) ∧ f (fun k => (z.val k).val) ≤ 1 := by
      apply hf
      apply (mem_translatedIntegerBox lo N _).mpr
      intro k
      exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (z.val k).property).1)
    have hs := affine_masked_initial_conditioning_shell_small
      sourceLo sourceN sourceM sourceA ⟨sourceCell.val⟩ lo N M a ⟨u.val⟩ q K sourceBase base sourceCell u
      D parameterA prime power hprime hpower hinj hJ w f B hsourceM hM hw hcell
      (affineComparisonScale ε L T C) modLog sourceDimLog dimLog hP hmodLog
      (ε / (2 + ε)) hxi hmask hcountP hmoduli hsourceDim hdim
      hsourceLengthInitial hlengthInitial shell hshell hcut
    change |full f - mass * (ratioX * ratioY * core f)| ≤ shell / 16 at hs
    simpa only [factor, mul_assoc] using hs
  have hH := (abs_le.mp (herror (fun x => (h x).re) hh)).2
  have hG := (abs_le.mp (herror (fun x => (g x).re) hg)).1
  have hcoeff : 0 ≤ coeff := mul_nonneg (by linarith only [hε]) ((Real.exp_pos (-L)).le.trans hlower)
  have hfactor : 0 ≤ factor := mul_nonneg (productCouplingAtomMass_nonneg c K sourceBase base)
    (mul_nonneg (residuePrimeCoordinateMassRatio_pos sourceLo sourceN sourceM sourceA q K sourceBase sourceCell).le
      (residuePrimeCoordinateMassRatio_pos lo N M a q K base u).le)
  have hG' := mul_le_mul_of_nonneg_left hG hcoeff
  have hlocal' := mul_le_mul_of_nonneg_left hlocal hfactor
  change productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) K sourceBase base source
    (fun z => site (fun x => (h x).re) z - coeff * site (fun x => (g x).re) z) ≤ factor * R + (1 + coeff) * (shell / 16)
  rw [productAtomTruncatedPairing_sub_smul_right]
  change full (fun x => (h x).re) - coeff * full (fun x => (g x).re) ≤ factor * R + (1 + coeff) * (shell / 16)
  nlinarith only [hH, hG', hlocal']

end

end Erdos3

end

end OAI
