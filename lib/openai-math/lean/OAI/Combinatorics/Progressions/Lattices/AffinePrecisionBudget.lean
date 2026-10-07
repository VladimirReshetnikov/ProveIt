import OAI.Combinatorics.Progressions.Estimates.AdaptiveRatioNormalization
import OAI.Combinatorics.Progressions.Estimates.GlobalCutoffAtomComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_adaptive_affine_comparison
    {ι σ J : Type*} [Fintype J] [Fintype ι] [LinearOrder ι] [Fintype σ]
    {q : ι → ℕ} [∀ i, NeZero (q i)]
    (lo a : σ → ℤ) (N : σ → ℕ)
    (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (1 : ℤ)) a))
    (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ)
    (hneSource : Nonempty (IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
      (fun _ => (1 : ℤ)) sourceA))
    (h g : (σ → ℤ) → ℂ) (w : (Option J × σ → ℤ) → ℝ)
    (hg : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (g z).re ∧ (g z).re ≤ 1)
    (hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1)
    (hw : ∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ w z ∧ w z ≤ 1)
    {ε L T C shell totalShell modLog level dimLog sourceDimLog : ℝ}
    (hε : 0 < ε) (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hshell : 0 < shell) (hlower : Real.exp (-L) ≤ level) (hlevel2 : level ≤ 2)
    (hmodLog : 0 ≤ modLog) (hdimLog : 0 ≤ dimLog) (hsourceDimLog : 0 ≤ sourceDimLog)
    (hmoduli : ∀ i, (q i : ℝ) ≤ Real.exp modLog)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp C)
    (hdim : (Fintype.card σ : ℝ) ≤ Real.exp dimLog)
    (hsourceDim : (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog)
    (prime power : ι → ℕ) (hprime : ∀ i, (prime i).Prime)
    (hpower : ∀ i, q i = prime i ^ power i) (hinj : Function.Injective prime)
    (hJ : 2 ≤ Fintype.card J) (D : ℕ) (parameterA : J → ℤ)
    (tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i)))
    (baseX : ∀ i, Option J × σ → ZMod (q i)) (baseY : ∀ i, σ → ZMod (q i))
    {d A B : ℕ}
    (htree : CoordinateDecisionTree.Valid (fun K base =>
      affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D ⊆ K ∧
      ResiduePrimeCoordinateStable g lo N 1 a q (affineRemovalDepth T + affineComparisonTail ε L T)
        (affineStabilityTolerance T) K base ∧
      PrimeRefinementUpperBound h g lo N 1 a q (affineRemovalDepth T + affineComparisonTail ε L T)
        level (affineIncrementTolerance L T) (affineStabilityTolerance T) K base)
      ∅ baseY tree d)
    (hA : d ≤ A)
    (hB : A + affineComparisonDegree (Fintype.card (Option J × σ)) (Fintype.card σ)
      ε L T C shell modLog ≤ B)
    (hBinitial : A + CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * ((Fintype.card (Option J × σ) : ℝ) * modLog +
        (Fintype.card σ : ℝ) * modLog + 1) + 4) ≤ B)
    (hside : ∀ k, Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog dimLog + 2) ≤ (N k : ℝ))
    (hsourceSide : ∀ k, Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog sourceDimLog + 2) ≤ (sourceN k : ℝ))
    (hallocation : Real.exp ((A : ℝ) * (affineComparisonScale ε L T C +
      (Fintype.card (Option J × σ) : ℝ) * modLog + (Fintype.card σ : ℝ) * modLog + 1)) * shell ≤ totalShell) :
    productTruncatedPairing (affinePeriodProductCoupling (σ := σ) q D parameterA)
      (lowDegreeCoordinateSets ι B)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 sourceA hneSource q w)
      (fun z => residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (h x).re) z -
        (1 + ε) * level * residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (g x).re) z) ≤
      (1 + affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) *
      (1 + affineComparisonAccuracy B (affineComparisonScale ε L T C) L T) *
        (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
          Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (totalShell / 16) := by
  have hpair : Pairwise (fun i k => (q i).Coprime (q k)) := by
    intro i k hik
    rw [hpower i, hpower k]
    exact selectedPrimePowers_pairwise_coprime prime power hprime hinj hik
  have hAB : A ≤ B := (Nat.le_add_right _ _).trans hB
  have hsite := unconditioned_affine_cell_bounds lo N a hne q hpair hAB hL hT hC
    hmodLog hdimLog hmoduli hdim hside
  have hsource := unconditioned_affine_cell_bounds sourceLo sourceN sourceA hneSource q hpair hAB
    hL hT hC hmodLog hsourceDimLog hmoduli hsourceDim hsourceSide
  let c := affinePeriodProductCoupling (σ := σ) q D parameterA
  let source := residuePrimeCoordinateDensity sourceLo sourceN 1 sourceA hneSource q w
  let target := fun z => residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (h x).re) z -
    (1 + ε) * level * residuePrimeCoordinateDensity lo N 1 a hne q (fun x => (g x).re) z
  let eta := affineComparisonAccuracy B (affineComparisonScale ε L T C) L T
  let R := level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
    Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)
  let coeff := 1 + (1 + ε) * level
  let pairs := CoordinateDecisionTree.leafSourceAssignments (fun i => Option J × σ → ZMod (q i)) tree ∅ baseY
  let ratioX := fun z : Σ leaf : ProductCylinder (fun i => σ → ZMod (q i)),
      ∀ i : leaf.1, Option J × σ → ZMod (q i.val) =>
    residuePrimeCoordinateMassRatio sourceLo sourceN 1 sourceA q z.1.1 (productSubtypePoint z.1.1 z.2 baseX)
  let ratioY := fun z : Σ leaf : ProductCylinder (fun i => σ → ZMod (q i)),
      ∀ i : leaf.1, Option J × σ → ZMod (q i.val) =>
    residuePrimeCoordinateMassRatio lo N 1 a q z.1.1 (z.1.assignment baseY)
  have hA' : (∅ : Finset ι).card + d ≤ A := by simpa using hA
  have hleaf (z) (hz : z ∈ pairs) : z.1 ∈ CoordinateDecisionTree.leafCylinders tree ∅ baseY :=
    (CoordinateDecisionTree.mem_leafSourceAssignments (fun i => Option J × σ → ZMod (q i)) tree ∅ baseY z).mp hz
  have hsize (z) (hz : z ∈ pairs) : z.1.1.card ≤ A :=
    (htree.leaf_card_le z.1 (hleaf z hz)).trans hA'
  have hratioX (z) (hz : z ∈ pairs) : |ratioX z - 1| ≤ eta :=
    residuePrimeCoordinateMassRatio_close_of_marginals sourceLo sourceN 1 sourceA hneSource q
      hsource.1 z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX)
  have hratioY (z) (hz : z ∈ pairs) : |ratioY z - 1| ≤ eta :=
    residuePrimeCoordinateMassRatio_close_of_marginals lo N 1 a hne q
      hsite.1 z.1.1 (hsize z hz) (z.1.assignment baseY)
  have hbound (z) (hz : z ∈ pairs) :
      productAtomTruncatedPairing c (lowDegreeCoordinateSets ι B) z.1.1
        (productSubtypePoint z.1.1 z.2 baseX) (z.1.assignment baseY) source target ≤
      adaptiveLeafPairMass c baseX baseY z * (ratioX z * ratioY z) * R + coeff * (shell / 16) := by
    have hcert := htree.leaf_good z.1 (hleaf z hz)
    let u := (hsite.2.1 z.1.1 (hsize z hz) (z.1.assignment baseY)).some
    let uX := (hsource.2.1 z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX)).some
    have hwX (v : ResiduePrimeCoordinateCell sourceLo sourceN 1 sourceA q z.1.1
        (productSubtypePoint z.1.1 z.2 baseX)) :
        0 ≤ w (fun k => (v.val k).val) ∧ w (fun k => (v.val k).val) ≤ 1 := by
      apply hw
      apply (mem_translatedIntegerBox sourceLo sourceN _).mpr
      intro k
      exact Finset.mem_Ico.mp ((Finset.mem_filter.mp (v.val k).property).1)
    have ha := global_cutoff_initial_atom_comparison
      (hKcard := hsize z hz) (hB := hB) (hstable := hcert.2.1) (hupper := hcert.2.2)
      (hM := by decide) (u := u) (hg := hg) (hh := hh) (hL := hL) (hT := hT)
      (hlower := hlower) (prime := prime) (power := power) (hprime := hprime) (hpower := hpower)
      (hJ := hJ) (hshell := hshell) (hlevel2 := hlevel2) (hmodLog := hmodLog) (hmoduli := hmoduli)
      (hε := hε) (hC := hC) (hcount := hcount) (dimLog := dimLog) (hdim := hdim)
      (hlength := hsite.2.2 z.1.1 (hsize z hz) (z.1.assignment baseY) u)
      (sourceLo := sourceLo) (sourceA := sourceA) (sourceN := sourceN) (sourceM := 1)
      (sourceBase := productSubtypePoint z.1.1 z.2 baseX) (sourceCell := uX) (w := w) (hw := hwX)
      (hsourceM := by decide) (sourceDimLog := sourceDimLog) (hsourceDim := hsourceDim)
      (hsourceLength := hsource.2.2 z.1.1 (hsize z hz) (productSubtypePoint z.1.1 z.2 baseX) uX)
      (hinj := hinj) (D := D) (parameterA := parameterA) (hmask := hcert.1) (hBinitial := hBinitial)
    exact ha
  have hlevel : 0 ≤ level := (Real.exp_pos (-L)).le.trans hlower
  have hcoeff : 0 ≤ coeff := by dsimp only [coeff]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hcountP := affineComparisonScale_count (ι := ι) (ε := ε) hL hT hC hcount
  have hcard := affine_leaf_source_assignments_card_le_exp (J := J) q htree hA' hP hmodLog hcountP hmoduli
  have herror : (∑ _z ∈ pairs, coeff * (shell / 16)) ≤ coeff * (totalShell / 16) := by
    have hpay := (mul_le_mul_of_nonneg_right hcard hshell.le).trans hallocation
    have hscale := mul_le_mul_of_nonneg_left hpay (div_nonneg hcoeff (by norm_num : (0 : ℝ) ≤ 16))
    calc
      _ = ((pairs.card : ℝ) * shell) * (coeff / 16) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ totalShell * (coeff / 16) := by nlinarith only [hscale]
      _ = _ := by ring
  exact productTruncatedPairing_leaf_normalized_bound c tree (lowDegreeCoordinateSets ι B)
    baseX baseY source target ratioX ratioY (fun _ => coeff * (shell / 16)) hR hratioX hratioY hbound herror

end Erdos3

end

section

namespace Erdos3

theorem normalized_affine_error_le {ε T level eta shell totalShell : ℝ}
    (hε : 0 ≤ ε) (hT : 0 ≤ T) (hlevel : 0 ≤ level) (hlevel2 : level ≤ 2)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hshell : 0 ≤ shell) (htotal : shell ≤ totalShell) :
    (1 + eta) * (1 + eta) *
        (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
          Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
      (1 + (1 + ε) * level) * (totalShell / 16) ≤
    100 * (1 + ε) * Real.exp (-T / 2) + (1 + ε) * totalShell := by
  have he : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have he0 : 0 < Real.exp (-T) := Real.exp_pos _
  have htotal0 : 0 ≤ totalShell := hshell.trans htotal
  have hdecay : Real.exp (-T) ≤ Real.exp (-T / 2) := Real.exp_le_exp.mpr (by linarith)
  have hsquare : (Real.exp (-T / 2)) ^ 2 = Real.exp (-T) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqrt : Real.sqrt (3 * Real.exp (-T)) ≤ 2 * Real.exp (-T / 2) := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * Real.exp (-T / 2))).mpr
    nlinarith only [hsquare, he0]
  have hfirstCoeff : level * (1 + 2 * ε) ≤ 4 * (1 + ε) := by nlinarith
  have hfirst := mul_le_mul hfirstCoeff hdecay he0.le (by positivity : 0 ≤ 4 * (1 + ε))
  have htailCoeff : 3 + (1 + ε) * level * 3 ≤ 9 * (1 + ε) := by nlinarith
  have htail := mul_le_mul hsqrt htailCoeff
    (by positivity : 0 ≤ 3 + (1 + ε) * level * 3)
    (by positivity : 0 ≤ 2 * Real.exp (-T / 2))
  have hmain : level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
      Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3) ≤
      22 * (1 + ε) * Real.exp (-T / 2) + shell / 16 := by nlinarith only [hfirst, htail]
  have hmain0 : 0 ≤ level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
      Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3) := by positivity
  have hfactor : (1 + eta) * (1 + eta) ≤ 4 := by nlinarith
  have hcoeff : 1 + (1 + ε) * level ≤ 3 * (1 + ε) := by nlinarith
  have herr := mul_le_mul_of_nonneg_right hcoeff (div_nonneg htotal0 (by norm_num : (0 : ℝ) ≤ 16))
  have hrest : shell / 4 + 3 * (1 + ε) * (totalShell / 16) ≤ (1 + ε) * totalShell := by
    nlinarith only [htotal, htotal0, mul_nonneg hε htotal0]
  calc
    _ ≤ 4 * (level * (1 + 2 * ε) * Real.exp (-T) + shell / 16 +
        Real.sqrt (3 * Real.exp (-T)) * (3 + (1 + ε) * level * 3)) +
        3 * (1 + ε) * (totalShell / 16) :=
      add_le_add (mul_le_mul_of_nonneg_right hfactor hmain0) herr
    _ ≤ 4 * (22 * (1 + ε) * Real.exp (-T / 2) + shell / 16) +
        3 * (1 + ε) * (totalShell / 16) := by
      linarith only [hmain]
    _ ≤ _ := by nlinarith only [hrest, mul_nonneg (by linarith : 0 ≤ 1 + ε) he.le]

theorem affine_error_envelope_at_precision {ε Q : ℝ} (hε : 0 ≤ ε) :
    100 * (1 + ε) * Real.exp (-(2 * (Q + Real.log (400 * (1 + ε)))) / 2) +
      (1 + ε) * (Real.exp (-Q) / (4 * (1 + ε))) = Real.exp (-Q) / 2 := by
  have ha : 0 < 1 + ε := by linarith
  have hc : 0 < 400 * (1 + ε) := by positivity
  have harg : -(2 * (Q + Real.log (400 * (1 + ε)))) / 2 =
      -Q - Real.log (400 * (1 + ε)) := by ring
  rw [harg, Real.exp_sub, Real.exp_log hc]
  field_simp
  ring

end Erdos3

end

section

namespace Erdos3

noncomputable def affineStabilityInputBudget (p ε L T C modLog parameterLog : ℝ) : ℝ :=
  max p (max (T + 4) (max modLog
    (max (affineComparisonPrimeThreshold (ε / (2 + ε)) (affineComparisonScale ε L T C) + 2 + 2 * parameterLog)
      ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ))))

theorem affineStabilityInputBudget_bounds (p ε L T C modLog parameterLog : ℝ) :
    p ≤ affineStabilityInputBudget p ε L T C modLog parameterLog ∧
    T + 4 ≤ affineStabilityInputBudget p ε L T C modLog parameterLog ∧
    modLog ≤ affineStabilityInputBudget p ε L T C modLog parameterLog ∧
    affineComparisonPrimeThreshold (ε / (2 + ε)) (affineComparisonScale ε L T C) + 2 + 2 * parameterLog ≤
      affineStabilityInputBudget p ε L T C modLog parameterLog ∧
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤
      affineStabilityInputBudget p ε L T C modLog parameterLog := by
  unfold affineStabilityInputBudget
  refine ⟨le_max_left _ _, ?_, ?_, ?_, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · exact (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))

theorem affineStabilityInputBudget_mask {ι : Type*} [Fintype ι]
    (prime : ι → ℕ) (hprime : ∀ i, (prime i).Prime) (hinj : Function.Injective prime)
    (p ε modLog : ℝ) {L T C parameterLog : ℝ} {D : ℕ}
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hD : 0 < D)
    (hparameter : (D : ℝ) ≤ Real.exp parameterLog) :
    ((affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D).card : ℝ) ≤
      affineStabilityInputBudget p ε L T C modLog parameterLog := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have hm := affineSamplerPrimeMask_card_le (ξ := ε / (2 + ε)) prime hprime hinj hP
    (sourceM := 1) (siteM := 1) (sourceLog := 0) (siteLog := 0)
    (by decide) (by decide) hD (by simp) (by simp) hparameter
  have hm' : ((affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D).card : ℝ) ≤
      affineComparisonPrimeThreshold (ε / (2 + ε)) (affineComparisonScale ε L T C) + 2 + 2 * parameterLog := by
    simpa only [mul_zero, add_zero] using hm
  exact hm'.trans (affineStabilityInputBudget_bounds p ε L T C modLog parameterLog).2.2.2.1

noncomputable def affineReferenceTargetTime (ε Q : ℝ) : ℝ :=
  2 * (Q + Real.log (400 * (1 + ε)))

noncomputable def affineReferenceTargetShell (ε Q : ℝ) : ℝ :=
  Real.exp (-Q) / (4 * (1 + ε))

theorem affineReferenceTargetTime_nonneg {ε Q : ℝ} (hε : 0 ≤ ε) (hQ : 0 ≤ Q) :
    0 ≤ affineReferenceTargetTime ε Q := by
  have hlog : 0 ≤ Real.log (400 * (1 + ε)) := Real.log_nonneg (by linarith)
  unfold affineReferenceTargetTime
  positivity

theorem affineReferenceTargetShell_pos {ε : ℝ} (Q : ℝ) (hε : 0 ≤ ε) :
    0 < affineReferenceTargetShell ε Q := by
  unfold affineReferenceTargetShell
  positivity

theorem affine_error_envelope_le_precision {ε Q T totalShell : ℝ} (hε : 0 ≤ ε)
    (hT : affineReferenceTargetTime ε Q ≤ T)
    (hshell : totalShell ≤ affineReferenceTargetShell ε Q) :
    100 * (1 + ε) * Real.exp (-T / 2) + (1 + ε) * totalShell ≤ Real.exp (-Q) / 2 := by
  have ht : Real.exp (-T / 2) ≤ Real.exp (-affineReferenceTargetTime ε Q / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hfirst := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 100 * (1 + ε))
  have hsecond := mul_le_mul_of_nonneg_left hshell (by linarith : 0 ≤ 1 + ε)
  exact (add_le_add hfirst hsecond).trans_eq (affine_error_envelope_at_precision hε)

theorem affine_error_envelope_lt_target {ε Q T totalShell : ℝ} (hε : 0 ≤ ε)
    (hT : affineReferenceTargetTime ε Q ≤ T)
    (hshell : totalShell ≤ affineReferenceTargetShell ε Q) :
    100 * (1 + ε) * Real.exp (-T / 2) + (1 + ε) * totalShell < Real.exp (-Q) := by
  have h := affine_error_envelope_le_precision hε hT hshell
  linarith [Real.exp_pos (-Q)]

end Erdos3

end

end OAI
