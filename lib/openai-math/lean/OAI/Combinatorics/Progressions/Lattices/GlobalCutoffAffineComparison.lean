import OAI.Combinatorics.Progressions.Polynomial.InitialMaskedAffineComparisonAtDegree

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

variable (hmoduli : ∀ i ∉ K, (q i : ℝ) ≤ Real.exp modLog)

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
variable (hmask : affineInitialPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) sourceM M ⊆ K)

include hKcard hB hstable hupper hM u hg hh hL hT hlower prime power hprime hpower hJ hshell hlevel2 hmodLog hmoduli hε hC hcount dimLog hdim hlength sourceLo sourceA sourceN sourceM sourceBase sourceCell w hw hsourceM sourceDimLog hsourceDim hsourceLength hinj hmask

theorem global_cutoff_masked_affine_comparison :
    let density := fun f => residueCellOutsideDensity lo N M a q K base u f
    affineResidueTruncatedPairing (J := J) (σ := σ) (fun i : {i // i ∉ K} => q i.val)
      (lowDegreeCoordinateSets {i // i ∉ K} (B - K.card)) (residueCellOutsideDensity sourceLo sourceN sourceM sourceA q K sourceBase sourceCell w)
      (fun z => density (fun x => (h x).re) z - (1 + ε) * level * density (fun x => (g x).re) z) ≤
      level * (1 + 2 * ε) * (Real.exp (-T)) + shell / 16 + Real.sqrt (3 * (Real.exp (-T))) * (3 + (1 + ε) * level * 3) := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hdegree := affineGlobalCutoff_outside hKcard hB
  have hlength' (k : σ) : Real.exp (affineComparisonLengthLog (B - K.card) ε L T C modLog dimLog) ≤
      (residueIndexLength (lo k) (lo k + N k) (M.lcm (∏ i ∈ K, q i)) ((u.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_mono_degree hdegree.2.1 hP hmodLog)).trans (hlength k)
  have hsourceLength' (k : Option J × σ) :
      Real.exp (affineComparisonLengthLog (B - K.card) ε L T C modLog sourceDimLog) ≤
      (residueIndexLength (sourceLo k) (sourceLo k + sourceN k) (sourceM.lcm (∏ i ∈ K, q i)) ((sourceCell.val k).val) : ℝ) :=
    (Real.exp_le_exp.mpr (affineComparisonLengthLog_mono_degree hdegree.2.1 hP hmodLog)).trans (hsourceLength k)
  exact initial_masked_affine_comparison_at_degree (b := B - K.card) (hb := hdegree.1)
    (ι := ι) (σ := σ) (J := J) (h := h) (g := g) (lo := lo) (a := a) (N := N)
    (M := M) (q := q) (ε := ε) (L := L) (T := T) (C := C) (shell := shell)
    (modLog := modLog) (level := level) (K := K) (base := base)
    (hstable := hstable) (hupper := hupper) (hM := hM) (u := u) (hg := hg) (hh := hh)
    (hL := hL) (hT := hT) (hlower := hlower) (prime := prime) (power := power)
    (hprime := hprime) (hpower := hpower) (hJ := hJ) (hshell := hshell) (hlevel2 := hlevel2)
    (hmodLog := hmodLog) (hmoduli := hmoduli) (hε := hε) (hC := hC) (hcount := hcount)
    (dimLog := dimLog) (hdim := hdim) (hlength := hlength')
    (sourceLo := sourceLo) (sourceA := sourceA) (sourceN := sourceN) (sourceM := sourceM)
    (sourceBase := sourceBase) (sourceCell := sourceCell) (w := w) (hw := hw)
    (hsourceM := hsourceM) (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim)
    (hsourceLength := hsourceLength') (hinj := hinj) (hmask := hmask)

end

end Erdos3

end

end OAI
