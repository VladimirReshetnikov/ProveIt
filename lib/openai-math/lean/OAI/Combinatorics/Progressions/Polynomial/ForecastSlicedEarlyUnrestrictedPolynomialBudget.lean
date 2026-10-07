import OAI.Combinatorics.Progressions.Sampling.ForecastSlicedPrimitiveCutoffBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators

@[gcongr] private theorem majorArcBiasLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcBiasLog n p ≤ majorArcBiasLog n p₂ := by
  unfold majorArcBiasLog
  gcongr

@[gcongr] private theorem majorArcLocalizationLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcLocalizationLog n p ≤ majorArcLocalizationLog n p₂ := by
  unfold majorArcLocalizationLog
  gcongr

@[gcongr] private theorem majorArcLengthLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcLengthLog n p ≤ majorArcLengthLog n p₂ := by
  unfold majorArcLengthLog
  gcongr

@[gcongr] private theorem majorArcErrorLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    majorArcErrorLog n p ≤ majorArcErrorLog n p₂ := by
  unfold majorArcErrorLog
  gcongr

@[gcongr] private theorem majorArcCoverLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    majorArcCoverLog n j p v ≤ majorArcCoverLog n j p₂ v₂ := by
  unfold majorArcCoverLog
  gcongr

@[gcongr] private theorem positiveModerateLengthLog_mono_budget (n : ℕ) {p p₂ : ℝ}
    (hp : p ≤ p₂) :
    positiveModerateLengthLog n p ≤ positiveModerateLengthLog n p₂ := by
  unfold positiveModerateLengthLog
  gcongr

@[gcongr] private theorem positiveModerateCoverLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    positiveModerateCoverLog n j p v ≤ positiveModerateCoverLog n j p₂ v₂ := by
  unfold positiveModerateCoverLog
  gcongr

@[gcongr] private theorem positiveModerateSpectrumLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    positiveModerateSpectrumLog n j p v ≤ positiveModerateSpectrumLog n j p₂ v₂ := by
  unfold positiveModerateSpectrumLog
  gcongr

@[gcongr] private theorem positiveModerateAccuracyLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    positiveModerateAccuracyLog n j t p v w ≤ positiveModerateAccuracyLog n j t p₂ v₂ w₂ := by
  unfold positiveModerateAccuracyLog
  gcongr

@[gcongr] private theorem positiveRetainedBiasLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedBiasLog n j t p v w E ≤ positiveRetainedBiasLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedBiasLog
  gcongr

@[gcongr] private theorem positiveSpectrumCardLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveSpectrumCardLog n j t p v w E ≤ positiveSpectrumCardLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveSpectrumCardLog
  gcongr

@[gcongr] private theorem positiveRetainedFrequencyLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedFrequencyLog n j t p v w E ≤ positiveRetainedFrequencyLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedFrequencyLog
  gcongr

@[gcongr] private theorem positiveRetainedDenominatorLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedDenominatorLog n j t p v w E ≤ positiveRetainedDenominatorLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedDenominatorLog
  gcongr

@[gcongr] private theorem positiveRetainedComplexityLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    positiveRetainedComplexityLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p₂ v₂ w₂ E₂ := by
  unfold positiveRetainedComplexityLog
  gcongr

@[gcongr] private theorem majorArcSpectrumLog_mono_budget (n j : ℕ) {p v p₂ v₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) :
    majorArcSpectrumLog n j p v ≤ majorArcSpectrumLog n j p₂ v₂ := by
  unfold majorArcSpectrumLog
  gcongr

@[gcongr] private theorem uniformBlockAccuracyLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    uniformBlockAccuracyLog n j t p v w ≤ uniformBlockAccuracyLog n j t p₂ v₂ w₂ := by
  unfold uniformBlockAccuracyLog
  gcongr

@[gcongr] private theorem uniformSpectrumSizeLog_mono_budget (n j t : ℕ) {p v w p₂ v₂ w₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) :
    uniformSpectrumSizeLog n j t p v w ≤ uniformSpectrumSizeLog n j t p₂ v₂ w₂ := by
  unfold uniformSpectrumSizeLog
  gcongr

@[gcongr] private theorem uniformRetainedBiasLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedBiasLog n j t p v w E ≤ uniformRetainedBiasLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedBiasLog
  gcongr

@[gcongr] private theorem uniformSpectrumCardLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformSpectrumCardLog n j t p v w E ≤ uniformSpectrumCardLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformSpectrumCardLog
  gcongr

@[gcongr] private theorem uniformRetainedFrequencyLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedFrequencyLog n j t p v w E ≤ uniformRetainedFrequencyLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedFrequencyLog
  gcongr

@[gcongr] private theorem uniformRetainedDenominatorLog_mono_budget (n j t : ℕ) {p v w E p₂ v₂ w₂ E₂ : ℝ}
    (hp : p ≤ p₂) (hv : v ≤ v₂) (hw : w ≤ w₂) (hE : E ≤ E₂) :
    uniformRetainedDenominatorLog n j t p v w E ≤ uniformRetainedDenominatorLog n j t p₂ v₂ w₂ E₂ := by
  unfold uniformRetainedDenominatorLog
  gcongr

theorem slicedGridSiteLog_mono (n d ta ti : ℕ) {D p E D' p' E' : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (_hE : 0 ≤ E)
    (hDD : D ≤ D') (hpp : p ≤ p') (hEE : E ≤ E') :
    slicedGridSiteLog n d ta ti D p E ≤ slicedGridSiteLog n d ta ti D' p' E' := by
  unfold slicedGridSiteLog
  gcongr
  linarith

theorem slicedGridSiteLog_eval (n d ta ti : ℕ) (D p E : Polynomial ℕ) (x : ℝ) :
    (slicedGridSiteLog n d ta ti D p E).eval₂ (Nat.castRingHom ℝ) x =
      slicedGridSiteLog n d ta ti (D.eval₂ (Nat.castRingHom ℝ) x)
        (p.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [slicedGridSiteLog, positiveRetainedComplexityLog, positiveRetainedDenominatorLog, positiveSpectrumCardLog, positiveRetainedFrequencyLog, positiveRetainedBiasLog, positiveModerateAccuracyLog, positiveModerateSpectrumLog, positiveModerateCoverLog, positiveModerateLengthLog, uniformSpectrumCardLog, uniformRetainedFrequencyLog, uniformRetainedDenominatorLog, uniformRetainedBiasLog, uniformSpectrumSizeLog, uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog, majorArcErrorLog, majorArcLengthLog, majorArcLocalizationLog, majorArcBiasLog, Polynomial.eval₂_pow]

theorem exists_slicedGridSiteLog_uniform_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ E → ∀ j : Fin m,
      slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
        ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p E ≤
        (D + p + E + A) ^ A := by
  classical
  let Lj := fun (j : Fin m) (D p E : Polynomial ℕ) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p E
  let poly := ∑ j : Fin m, Lj j Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p E hD hp hE j
  let R := D + p + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply (slicedGridSiteLog_mono _ _ _ _ hD hp hE
    (by dsimp [R]; linarith : D ≤ R) (by dsimp [R]; linarith : p ≤ R)
    (by dsimp [R]; linarith : E ≤ R)).trans
  apply le_trans ?_ (hbound R hR)
  have heval (j : Fin m) : (Lj j Polynomial.X Polynomial.X Polynomial.X).eval₂ (Nat.castRingHom ℝ) R =
      slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
        ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
        ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) R R R := by
    simp only [Lj, slicedGridSiteLog_eval, Polynomial.eval₂_X]
  simp only [poly, Polynomial.eval₂_finsetSum, heval]
  apply Finset.single_le_sum ?_ (Finset.mem_univ j)
  intro i _
  exact (slicedGridSiteLog_bounds _ _ _ _ hR hR hR).1

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem slicedFixedZeroGeometryLog_mono
    {D v w vq vchild D' v' w' vq' vchild' : ℝ}
    (hD0 : 0 ≤ D) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w)
    (hvq0 : 0 ≤ vq) (hvc0 : 0 ≤ vchild)
    (hD : D ≤ D') (hv : v ≤ v') (hw : w ≤ w')
    (hvq : vq ≤ vq') (hvc : vchild ≤ vchild') :
    slicedFixedZeroGeometryLog D v w vq vchild ≤
      slicedFixedZeroGeometryLog D' v' w' vq' vchild' := by
  have hD'0 : 0 ≤ D' := hD0.trans hD
  unfold slicedFixedZeroGeometryLog slicedGridGeometryLog
  gcongr

theorem slicedFixedZeroGeometryLog_eval₂
    (D v w vq vchild : Polynomial ℕ) (x : ℝ) :
    (slicedFixedZeroGeometryLog D v w vq vchild).eval₂ (Nat.castRingHom ℝ) x =
      slicedFixedZeroGeometryLog (D.eval₂ (Nat.castRingHom ℝ) x)
        (v.eval₂ (Nat.castRingHom ℝ) x) (w.eval₂ (Nat.castRingHom ℝ) x)
        (vq.eval₂ (Nat.castRingHom ℝ) x) (vchild.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [slicedFixedZeroGeometryLog, slicedGridGeometryLog, Polynomial.eval₂_pow]

end Erdos3.VectorPolynomial

namespace Erdos3

theorem uniformProductAccuracyLog_mono {D T E D' T' E' : ℝ}
    (hD0 : 0 ≤ D) (hT0 : 0 ≤ T)
    (hD : D ≤ D') (hT : T ≤ T') (hE : E ≤ E') :
    uniformProductAccuracyLog D T E ≤ uniformProductAccuracyLog D' T' E' := by
  have hD'0 : 0 ≤ D' := hD0.trans hD
  unfold uniformProductAccuracyLog
  gcongr

theorem uniformProductAccuracyLog_eval₂ (D T E : Polynomial ℕ) (x : ℝ) :
    (uniformProductAccuracyLog D T E).eval₂ (Nat.castRingHom ℝ) x =
      uniformProductAccuracyLog (D.eval₂ (Nat.castRingHom ℝ) x)
        (T.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp [uniformProductAccuracyLog]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def slicedFixedUniformSitePolynomial (m : ℕ) (p E : Polynomial ℕ) : Polynomial ℕ :=
  p + E + 1 + ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E

theorem slicedFixedUniformSitePolynomial_eval (m : ℕ) (p E : Polynomial ℕ) (x : ℝ) :
    (slicedFixedUniformSitePolynomial m p E).eval₂ (Nat.castRingHom ℝ) x =
      slicedFixedUniformSiteLog m (p.eval₂ (Nat.castRingHom ℝ) x) (E.eval₂ (Nat.castRingHom ℝ) x) := by
  simp only [slicedFixedUniformSitePolynomial, slicedFixedUniformSiteLog,
    Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_finsetSum, slicedGridSiteLog_eval]

theorem slicedFixedUniformSiteLog_mono (m : ℕ) {p E p' E' : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hpp : p ≤ p') (hEE : E ≤ E') :
    slicedFixedUniformSiteLog m p E ≤ slicedFixedUniformSiteLog m p' E' := by
  unfold slicedFixedUniformSiteLog
  apply add_le_add (add_le_add (add_le_add hpp hEE) le_rfl)
  apply Finset.sum_le_sum
  intro j _
  exact slicedGridSiteLog_mono _ _ _ _ zero_le_one hp hE le_rfl hpp hEE

theorem exists_slicedFixedUniform_polynomial_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {D p E v w vq vchild : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ E → 0 ≤ v → 0 ≤ w → 0 ≤ vq → 0 ≤ vchild →
      let pAll := p + slicedFixedZeroGeometryLog D v w vq vchild
      let capLog := slicedFixedUniformSiteLog m pAll 0
      let Eprod := slicedFixedUniformAccuracyLog m D pAll E
      let Q := slicedFixedUniformSiteLog m pAll Eprod
      let O := siteExponentialOutputLog 1 Q
      let budget := (D + p + E + v + w + vq + vchild + C) ^ C
      pAll ≤ budget ∧ capLog ≤ budget ∧ Eprod ≤ budget ∧ Q ≤ budget ∧ O ≤ budget := by
  classical
  let Pall : Polynomial ℕ := Polynomial.X +
    slicedFixedZeroGeometryLog Polynomial.X Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  let Pcap := slicedFixedUniformSitePolynomial m Pall 0
  let Pacc := uniformProductAccuracyLog Polynomial.X Pcap Polynomial.X + 1
  let Pq := slicedFixedUniformSitePolynomial m Pall Pacc
  let Po := siteExponentialOutputLog 1 Pq
  let Ptotal := Pall + Pcap + Pacc + Pq + Po
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget Ptotal
  refine ⟨C, hC, ?_⟩
  intro D p E v w vq vchild hD hp hE hv hw hvq hvc pAll capLog Eprod Q O budget
  let R := D + p + E + v + w + vq + vchild
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hER : E ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hwR : w ≤ R := by dsimp [R]; linarith
  have hvqR : vq ≤ R := by dsimp [R]; linarith
  have hvcR : vchild ≤ R := by dsimp [R]; linarith
  have hpAll : 0 ≤ pAll := add_nonneg hp (slicedFixedZeroGeometryLog_nonneg hD hv hw hvq hvc)
  have hcap : 0 ≤ capLog := slicedFixedUniformSiteLog_nonneg m hpAll le_rfl
  have hacc : 0 ≤ Eprod := by
    exact add_nonneg (uniformProductAccuracyLog_nonneg hD hcap hE) zero_le_one
  have hq : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hpAll hacc
  have ho : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hq
  have hAll : pAll ≤ Pall.eval₂ (Nat.castRingHom ℝ) R := by
    simp only [Pall, Polynomial.eval₂_add, Polynomial.eval₂_X, slicedFixedZeroGeometryLog_eval₂]
    exact add_le_add hpR (slicedFixedZeroGeometryLog_mono hD hv hw hvq hvc hDR hvR hwR hvqR hvcR)
  have hCap : capLog ≤ Pcap.eval₂ (Nat.castRingHom ℝ) R := by
    simp only [Pcap, slicedFixedUniformSitePolynomial_eval, Polynomial.eval₂_zero]
    exact slicedFixedUniformSiteLog_mono m hpAll (le_refl (0 : ℝ)) hAll le_rfl
  have hAcc : Eprod ≤ Pacc.eval₂ (Nat.castRingHom ℝ) R := by
    simp only [Pacc, Polynomial.eval₂_add, uniformProductAccuracyLog_eval₂, Polynomial.eval₂_X,
      Polynomial.eval₂_one]
    exact add_le_add (uniformProductAccuracyLog_mono hD hcap hDR hCap hER) le_rfl
  have hQ : Q ≤ Pq.eval₂ (Nat.castRingHom ℝ) R := by
    rw [show Pq = slicedFixedUniformSitePolynomial m Pall Pacc from rfl,
      slicedFixedUniformSitePolynomial_eval]
    exact slicedFixedUniformSiteLog_mono m hpAll hacc hAll hAcc
  have hO : O ≤ Po.eval₂ (Nat.castRingHom ℝ) R := by
    change siteExponentialOutputLog 1 Q ≤ (siteExponentialOutputLog 1 Pq).eval₂ (Nat.castRingHom ℝ) R
    simp only [siteExponentialOutputLog, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_natCast, Polynomial.eval₂_ofNat]
    gcongr
  have hsum : pAll + capLog + Eprod + Q + O ≤ Ptotal.eval₂ (Nat.castRingHom ℝ) R := by
    simp only [Ptotal, Polynomial.eval₂_add]
    exact add_le_add (add_le_add (add_le_add (add_le_add hAll hCap) hAcc) hQ) hO
  have hfinal : pAll + capLog + Eprod + Q + O ≤ budget := hsum.trans (hbound R hR)
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem exists_slicedFixedUniform_tail_polynomial_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {D p v w vchild : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ w → 0 ≤ vchild →
      slicedFixedUniformSiteLog m (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0 ≤
        (D + p + v + w + vchild + C) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_slicedFixedUniform_polynomial_budget m
  refine ⟨C, hC, ?_⟩
  intro D p v w vchild hD hp hv hw hvc
  have h := hbound hD hp (le_refl (0 : ℝ)) hv hw (le_refl (0 : ℝ)) hvc
  simpa only [add_zero] using h.2.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def forecastSlicedEarlyDiagonalBudget (m : ℕ) (r : ℝ) : ℝ :=
  let pTailAll := r + slicedFixedZeroGeometryLog r r r 0 r
  let tailLog := slicedFixedUniformSiteLog m pTailAll 0
  let Pin := r * tailLog
  let Pdec := (r + r) * (r + 2) * modularRankChargeFactor m
  let V := Pin + Pdec + (r + r) + 3
  let Esite := r + r + 1 + r * V
  let pAll := (r + V) + slicedFixedZeroGeometryLog r r r V r
  let Eprod := slicedFixedUniformAccuracyLog m r pAll Esite
  let Q := slicedFixedUniformSiteLog m pAll Eprod
  let O := siteExponentialOutputLog 1 Q
  let Pperiod := V + r * O
  let Pfactor := r + r + O + 1 + r
  let Pnative := Pperiod + Pfactor + r + r + 1
  let Pmass := r + r * V + r * O + 1
  let Pcap := r + Pin + Pdec + 1
  Pnative + Pmass + Pcap

noncomputable def forecastSlicedEarlyPolynomial (m : ℕ) : Polynomial ℕ :=
  let r : Polynomial ℕ := Polynomial.X
  let pTailAll := r + slicedFixedZeroGeometryLog r r r 0 r
  let tailLog := slicedFixedUniformSitePolynomial m pTailAll 0
  let Pin := r * tailLog
  let Pdec := (r + r) * (r + 2) * Polynomial.C (modularRankChargeFactor m)
  let V := Pin + Pdec + (r + r) + 3
  let Esite := r + r + 1 + r * V
  let pAll := (r + V) + slicedFixedZeroGeometryLog r r r V r
  let Eprod := uniformProductAccuracyLog r (slicedFixedUniformSitePolynomial m pAll 0) Esite + 1
  let Q := slicedFixedUniformSitePolynomial m pAll Eprod
  let O := siteExponentialOutputLog 1 Q
  let Pperiod := V + r * O
  let Pfactor := r + r + O + 1 + r
  let Pnative := Pperiod + Pfactor + r + r + 1
  let Pmass := r + r * V + r * O + 1
  let Pcap := r + Pin + Pdec + 1
  Pnative + Pmass + Pcap

theorem forecastSlicedEarlyPolynomial_eval (m : ℕ) (r : ℝ) :
    (forecastSlicedEarlyPolynomial m).eval₂ (Nat.castRingHom ℝ) r =
      forecastSlicedEarlyDiagonalBudget m r := by
  have hcast (k : ℕ) : (Nat.castRingHom ℝ) k = (k : ℝ) := rfl
  simp only [forecastSlicedEarlyPolynomial, forecastSlicedEarlyDiagonalBudget,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_zero, Polynomial.eval₂_one, Polynomial.eval₂_ofNat,
    slicedFixedZeroGeometryLog_eval₂, slicedFixedUniformSitePolynomial_eval,
    uniformProductAccuracyLog_eval₂, slicedFixedUniformAccuracyLog,
    siteExponentialOutputLog, hcast, Polynomial.eval₂_natCast]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial

theorem forecastSlicedEarlyLogs_le_diagonal (m Dmod d : ℕ) {r : ℝ} (hr : 0 ≤ r)
    {D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D ∧ D ≤ r)
    (htail : 0 ≤ ptail ∧ ptail ≤ r)
    (hv : 0 ≤ v ∧ v ≤ r)
    (hw : 0 ≤ w ∧ w ≤ r)
    (hchild : 0 ≤ vchild ∧ vchild ≤ r)
    (hsm : 0 ≤ Psm ∧ Psm ≤ r)
    (hlip : 0 ≤ Plip ∧ Plip ≤ r)
    (hbad : 0 ≤ Pbad ∧ Pbad ≤ r)
    (hpres : 0 ≤ Ppres ∧ Ppres ≤ r)
    (hE : 0 ≤ E ∧ E ≤ r)
    (hspatial : 0 ≤ Pspatial ∧ Pspatial ≤ r)
    (hcoord : 0 ≤ Pcoord ∧ Pcoord ≤ r)
    (hcut : 0 ≤ Pcut ∧ Pcut ≤ r)
    (hDmod : (Dmod : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let psite := ptail + V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pnative ∧ 0 ≤ Pmass ∧ 0 ≤ Pcap ∧
      Pnative + Pmass + Pcap ≤ forecastSlicedEarlyDiagonalBudget m r := by
  intro pTailAll tailLog Pin Pdec V Esite psite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap
  have hDNonneg := hD.1
  have htailNonneg := htail.1
  have hvNonneg := hv.1
  have hwNonneg := hw.1
  have hchildNonneg := hchild.1
  have hsmNonneg := hsm.1
  have hlipNonneg := hlip.1
  have hbadNonneg := hbad.1
  have hpresNonneg := hpres.1
  have hENonneg := hE.1
  have hspatialNonneg := hspatial.1
  have hcoordNonneg := hcoord.1
  have hcutNonneg := hcut.1
  let rTail := r + slicedFixedZeroGeometryLog r r r 0 r
  let rLog := slicedFixedUniformSiteLog m rTail 0
  let rIn := r * rLog
  let rDec := (r + r) * (r + 2) * modularRankChargeFactor m
  let rV := rIn + rDec + (r + r) + 3
  let rEsite := r + r + 1 + r * rV
  let rAll := (r + rV) + slicedFixedZeroGeometryLog r r r rV r
  let rProd := slicedFixedUniformAccuracyLog m r rAll rEsite
  let rQ := slicedFixedUniformSiteLog m rAll rProd
  let rO := siteExponentialOutputLog 1 rQ
  let rPeriod := rV + r * rO
  let rFactor := r + r + rO + 1 + r
  let rNative := rPeriod + rFactor + r + r + 1
  let rMass := r + r * rV + r * rO + 1
  let rCap := r + rIn + rDec + 1
  have htail0 : 0 ≤ pTailAll := add_nonneg htail.1
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 (le_refl 0) hchild.1)
  have hlog0 : 0 ≤ tailLog := slicedFixedUniformSiteLog_nonneg m htail0 (le_refl 0)
  have hin0 : 0 ≤ Pin := mul_nonneg hD.1 hlog0
  have hdec0 : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hEs0 : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hsite0 : 0 ≤ psite := add_nonneg htail.1 hV0
  have hAll0 : 0 ≤ pAll := add_nonneg hsite0
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 hV0 hchild.1)
  have hcap0 : 0 ≤ slicedFixedUniformSiteLog m pAll 0 := slicedFixedUniformSiteLog_nonneg m hAll0 (le_refl 0)
  have hprod0 : 0 ≤ Eprod := add_nonneg
    (uniformProductAccuracyLog_nonneg hD.1 hcap0 hEs0) zero_le_one
  have hQ0 : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hAll0 hprod0
  have hO0 : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hQ0
  have hperiod0 : 0 ≤ Pperiod := add_nonneg hV0 (mul_nonneg hD.1 hO0)
  have hfactor0 : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hnative0 : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  have hmass0 : 0 ≤ Pmass := by dsimp only [Pmass]; positivity
  have hcapFin0 : 0 ≤ Pcap := by dsimp only [Pcap]; positivity
  have htailR : pTailAll ≤ rTail := add_le_add htail.2
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 (le_refl 0) hchild.1
      hD.2 hv.2 hw.2 le_rfl hchild.2)
  have hlogR : tailLog ≤ rLog := slicedFixedUniformSiteLog_mono m htail0 (le_refl 0) htailR le_rfl
  have hinR : Pin ≤ rIn := mul_le_mul hD.2 hlogR hlog0 hr
  have hdecR : Pdec ≤ rDec := by
    dsimp only [Pdec, rDec]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (add_le_add hbad.2 hpres.2) (add_le_add (hDmod.trans hD.2) le_rfl)
        (by positivity) (by positivity)) (Nat.cast_nonneg _)
  have hVR : V ≤ rV := add_le_add
    (add_le_add (add_le_add hinR hdecR) (add_le_add hE.2 hsm.2)) le_rfl
  have hrV : 0 ≤ rV := hV0.trans hVR
  have hEsR : Esite ≤ rEsite := add_le_add
    (add_le_add (add_le_add hE.2 hsm.2) le_rfl)
    (mul_le_mul (hd.trans hD.2) hVR hV0 hr)
  have hAllR : pAll ≤ rAll := add_le_add (add_le_add htail.2 hVR)
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 hV0 hchild.1
      hD.2 hv.2 hw.2 hVR hchild.2)
  have hprodR : Eprod ≤ rProd := add_le_add
    (uniformProductAccuracyLog_mono hD.1 hcap0 hD.2
      (slicedFixedUniformSiteLog_mono m hAll0 (le_refl 0) hAllR le_rfl) hEsR) le_rfl
  have hQR : Q ≤ rQ := slicedFixedUniformSiteLog_mono m hAll0 hprod0 hAllR hprodR
  have hOR : O ≤ rO := by
    dsimp only [O, rO, siteExponentialOutputLog]
    gcongr
  have hrO : 0 ≤ rO := hO0.trans hOR
  have hperiodR : Pperiod ≤ rPeriod := add_le_add hVR (mul_le_mul hD.2 hOR hO0 hr)
  have hfactorR : Pfactor ≤ rFactor := add_le_add
    (add_le_add (add_le_add (add_le_add hlip.2 hD.2) hOR) le_rfl) hspatial.2
  have hnativeR : Pnative ≤ rNative := add_le_add
    (add_le_add (add_le_add (add_le_add hperiodR hfactorR) hcoord.2) hcut.2) le_rfl
  have hmassR : Pmass ≤ rMass := add_le_add
    (add_le_add (add_le_add hsm.2 (mul_le_mul (hd.trans hD.2) hVR hV0 hr))
      (mul_le_mul hD.2 hOR hO0 hr)) le_rfl
  have hcapR : Pcap ≤ rCap := add_le_add (add_le_add (add_le_add hsm.2 hinR) hdecR) le_rfl
  refine ⟨hnative0, hmass0, hcapFin0, ?_⟩
  change Pnative + Pmass + Pcap ≤ rNative + rMass + rCap
  exact add_le_add (add_le_add hnativeR hmassR) hcapR

theorem exists_forecastSlicedEarly_polynomial_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Dmod d : ℕ)
      {D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ},
      0 ≤ D → 0 ≤ ptail → 0 ≤ v → 0 ≤ w → 0 ≤ vchild →
      0 ≤ Psm → 0 ≤ Plip → 0 ≤ Pbad → 0 ≤ Ppres → 0 ≤ E →
      0 ≤ Pspatial → 0 ≤ Pcoord → 0 ≤ Pcut →
      (Dmod : ℝ) ≤ D → (d : ℝ) ≤ D →
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let psite := ptail + V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    let budget := (D + ptail + v + w + vchild + Psm + Plip + Pbad + Ppres + E + Pspatial + Pcoord + Pcut + C) ^ C
    Pnative ≤ budget ∧ Pmass ≤ budget ∧ Pcap ≤ budget := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (forecastSlicedEarlyPolynomial m)
  refine ⟨C, hC, ?_⟩
  intro Dmod d D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut
    hD htail hv hw hchild hsm hlip hbad hpres hE hspatial hcoord hcut hDmod hd
    pTailAll tailLog Pin Pdec V Esite psite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap budget
  let r := D + ptail + v + w + vchild + Psm + Plip + Pbad + Ppres + E + Pspatial + Pcoord + Pcut
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hdiag := forecastSlicedEarlyLogs_le_diagonal m Dmod d hr
    ⟨hD, by dsimp [r]; linarith⟩
    ⟨htail, by dsimp [r]; linarith⟩
    ⟨hv, by dsimp [r]; linarith⟩
    ⟨hw, by dsimp [r]; linarith⟩
    ⟨hchild, by dsimp [r]; linarith⟩
    ⟨hsm, by dsimp [r]; linarith⟩
    ⟨hlip, by dsimp [r]; linarith⟩
    ⟨hbad, by dsimp [r]; linarith⟩
    ⟨hpres, by dsimp [r]; linarith⟩
    ⟨hE, by dsimp [r]; linarith⟩
    ⟨hspatial, by dsimp [r]; linarith⟩
    ⟨hcoord, by dsimp [r]; linarith⟩
    ⟨hcut, by dsimp [r]; linarith⟩
    hDmod hd
  have heval : forecastSlicedEarlyDiagonalBudget m r ≤ budget := by
    rw [← forecastSlicedEarlyPolynomial_eval]
    exact hbound r hr
  have hfinal : Pnative + Pmass + Pcap ≤ budget := hdiag.2.2.2.trans heval
  have hn : 0 ≤ Pnative := hdiag.1
  have hm : 0 ≤ Pmass := hdiag.2.1
  have hc : 0 ≤ Pcap := hdiag.2.2.1
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

theorem forecastSlicedEarlyLogs_le_diagonal_of_dimensions (m Dmod d : ℕ) {r : ℝ} (hr : 0 ≤ r)
    {D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D ∧ D ≤ r)
    (htail : 0 ≤ ptail ∧ ptail ≤ r)
    (hv : 0 ≤ v ∧ v ≤ r)
    (hw : 0 ≤ w ∧ w ≤ r)
    (hchild : 0 ≤ vchild ∧ vchild ≤ r)
    (hsm : 0 ≤ Psm ∧ Psm ≤ r)
    (hlip : 0 ≤ Plip ∧ Plip ≤ r)
    (hbad : 0 ≤ Pbad ∧ Pbad ≤ r)
    (hpres : 0 ≤ Ppres ∧ Ppres ≤ r)
    (hE : 0 ≤ E ∧ E ≤ r)
    (hspatial : 0 ≤ Pspatial ∧ Pspatial ≤ r)
    (hcoord : 0 ≤ Pcoord ∧ Pcoord ≤ r)
    (hcut : 0 ≤ Pcut ∧ Pcut ≤ r)
    (hDmod : (Dmod : ℝ) ≤ r) (hd : (d : ℝ) ≤ r) :
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let psite := ptail + V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pnative ∧ 0 ≤ Pmass ∧ 0 ≤ Pcap ∧
      Pnative + Pmass + Pcap ≤ forecastSlicedEarlyDiagonalBudget m r := by
  intro pTailAll tailLog Pin Pdec V Esite psite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap
  have hDNonneg := hD.1
  have htailNonneg := htail.1
  have hvNonneg := hv.1
  have hwNonneg := hw.1
  have hchildNonneg := hchild.1
  have hsmNonneg := hsm.1
  have hlipNonneg := hlip.1
  have hbadNonneg := hbad.1
  have hpresNonneg := hpres.1
  have hENonneg := hE.1
  have hspatialNonneg := hspatial.1
  have hcoordNonneg := hcoord.1
  have hcutNonneg := hcut.1
  let rTail := r + slicedFixedZeroGeometryLog r r r 0 r
  let rLog := slicedFixedUniformSiteLog m rTail 0
  let rIn := r * rLog
  let rDec := (r + r) * (r + 2) * modularRankChargeFactor m
  let rV := rIn + rDec + (r + r) + 3
  let rEsite := r + r + 1 + r * rV
  let rAll := (r + rV) + slicedFixedZeroGeometryLog r r r rV r
  let rProd := slicedFixedUniformAccuracyLog m r rAll rEsite
  let rQ := slicedFixedUniformSiteLog m rAll rProd
  let rO := siteExponentialOutputLog 1 rQ
  let rPeriod := rV + r * rO
  let rFactor := r + r + rO + 1 + r
  let rNative := rPeriod + rFactor + r + r + 1
  let rMass := r + r * rV + r * rO + 1
  let rCap := r + rIn + rDec + 1
  have htail0 : 0 ≤ pTailAll := add_nonneg htail.1
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 (le_refl 0) hchild.1)
  have hlog0 : 0 ≤ tailLog := slicedFixedUniformSiteLog_nonneg m htail0 (le_refl 0)
  have hin0 : 0 ≤ Pin := mul_nonneg hD.1 hlog0
  have hdec0 : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hEs0 : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hsite0 : 0 ≤ psite := add_nonneg htail.1 hV0
  have hAll0 : 0 ≤ pAll := add_nonneg hsite0
    (slicedFixedZeroGeometryLog_nonneg hD.1 hv.1 hw.1 hV0 hchild.1)
  have hcap0 : 0 ≤ slicedFixedUniformSiteLog m pAll 0 := slicedFixedUniformSiteLog_nonneg m hAll0 (le_refl 0)
  have hprod0 : 0 ≤ Eprod := add_nonneg
    (uniformProductAccuracyLog_nonneg hD.1 hcap0 hEs0) zero_le_one
  have hQ0 : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hAll0 hprod0
  have hO0 : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hQ0
  have hperiod0 : 0 ≤ Pperiod := add_nonneg hV0 (mul_nonneg hD.1 hO0)
  have hfactor0 : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hnative0 : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  have hmass0 : 0 ≤ Pmass := by dsimp only [Pmass]; positivity
  have hcapFin0 : 0 ≤ Pcap := by dsimp only [Pcap]; positivity
  have htailR : pTailAll ≤ rTail := add_le_add htail.2
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 (le_refl 0) hchild.1
      hD.2 hv.2 hw.2 le_rfl hchild.2)
  have hlogR : tailLog ≤ rLog := slicedFixedUniformSiteLog_mono m htail0 (le_refl 0) htailR le_rfl
  have hinR : Pin ≤ rIn := mul_le_mul hD.2 hlogR hlog0 hr
  have hdecR : Pdec ≤ rDec := by
    dsimp only [Pdec, rDec]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (add_le_add hbad.2 hpres.2) (add_le_add hDmod le_rfl)
        (by positivity) (by positivity)) (Nat.cast_nonneg _)
  have hVR : V ≤ rV := add_le_add
    (add_le_add (add_le_add hinR hdecR) (add_le_add hE.2 hsm.2)) le_rfl
  have hrV : 0 ≤ rV := hV0.trans hVR
  have hEsR : Esite ≤ rEsite := add_le_add
    (add_le_add (add_le_add hE.2 hsm.2) le_rfl)
    (mul_le_mul hd hVR hV0 hr)
  have hAllR : pAll ≤ rAll := add_le_add (add_le_add htail.2 hVR)
    (slicedFixedZeroGeometryLog_mono hD.1 hv.1 hw.1 hV0 hchild.1
      hD.2 hv.2 hw.2 hVR hchild.2)
  have hprodR : Eprod ≤ rProd := add_le_add
    (uniformProductAccuracyLog_mono hD.1 hcap0 hD.2
      (slicedFixedUniformSiteLog_mono m hAll0 (le_refl 0) hAllR le_rfl) hEsR) le_rfl
  have hQR : Q ≤ rQ := slicedFixedUniformSiteLog_mono m hAll0 hprod0 hAllR hprodR
  have hOR : O ≤ rO := by
    dsimp only [O, rO, siteExponentialOutputLog]
    gcongr
  have hrO : 0 ≤ rO := hO0.trans hOR
  have hperiodR : Pperiod ≤ rPeriod := add_le_add hVR (mul_le_mul hD.2 hOR hO0 hr)
  have hfactorR : Pfactor ≤ rFactor := add_le_add
    (add_le_add (add_le_add (add_le_add hlip.2 hD.2) hOR) le_rfl) hspatial.2
  have hnativeR : Pnative ≤ rNative := add_le_add
    (add_le_add (add_le_add (add_le_add hperiodR hfactorR) hcoord.2) hcut.2) le_rfl
  have hmassR : Pmass ≤ rMass := add_le_add
    (add_le_add (add_le_add hsm.2 (mul_le_mul hd hVR hV0 hr))
      (mul_le_mul hD.2 hOR hO0 hr)) le_rfl
  have hcapR : Pcap ≤ rCap := add_le_add (add_le_add (add_le_add hsm.2 hinR) hdecR) le_rfl
  refine ⟨hnative0, hmass0, hcapFin0, ?_⟩
  change Pnative + Pmass + Pcap ≤ rNative + rMass + rCap
  exact add_le_add (add_le_add hnativeR hmassR) hcapR

theorem exists_forecastSlicedEarly_unrestricted_polynomial_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (Dmod d : ℕ)
      {D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ},
      0 ≤ D → 0 ≤ ptail → 0 ≤ v → 0 ≤ w → 0 ≤ vchild →
      0 ≤ Psm → 0 ≤ Plip → 0 ≤ Pbad → 0 ≤ Ppres → 0 ≤ E →
      0 ≤ Pspatial → 0 ≤ Pcoord → 0 ≤ Pcut →
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let psite := ptail + V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    let budget := (D + (Dmod : ℝ) + (d : ℝ) + ptail + v + w + vchild + Psm + Plip + Pbad + Ppres + E + Pspatial + Pcoord + Pcut + C) ^ C
    Pnative ≤ budget ∧ Pmass ≤ budget ∧ Pcap ≤ budget := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (forecastSlicedEarlyPolynomial m)
  refine ⟨C, hC, ?_⟩
  intro Dmod d D ptail v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut
    hD htail hv hw hchild hsm hlip hbad hpres hE hspatial hcoord hcut
    pTailAll tailLog Pin Pdec V Esite psite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap budget
  let r := D + (Dmod : ℝ) + (d : ℝ) + ptail + v + w + vchild + Psm + Plip + Pbad + Ppres + E + Pspatial + Pcoord + Pcut
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hDmod0 : (0 : ℝ) ≤ Dmod := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hdiag := forecastSlicedEarlyLogs_le_diagonal_of_dimensions m Dmod d hr
    ⟨hD, by dsimp [r]; linarith⟩
    ⟨htail, by dsimp [r]; linarith⟩
    ⟨hv, by dsimp [r]; linarith⟩
    ⟨hw, by dsimp [r]; linarith⟩
    ⟨hchild, by dsimp [r]; linarith⟩
    ⟨hsm, by dsimp [r]; linarith⟩
    ⟨hlip, by dsimp [r]; linarith⟩
    ⟨hbad, by dsimp [r]; linarith⟩
    ⟨hpres, by dsimp [r]; linarith⟩
    ⟨hE, by dsimp [r]; linarith⟩
    ⟨hspatial, by dsimp [r]; linarith⟩
    ⟨hcoord, by dsimp [r]; linarith⟩
    ⟨hcut, by dsimp [r]; linarith⟩
    (by dsimp [r]; linarith)
    (by dsimp [r]; linarith)
  have heval : forecastSlicedEarlyDiagonalBudget m r ≤ budget := by
    rw [← forecastSlicedEarlyPolynomial_eval]
    exact hbound r hr
  have hfinal : Pnative + Pmass + Pcap ≤ budget := hdiag.2.2.2.trans heval
  have hn : 0 ≤ Pnative := hdiag.1
  have hm : 0 ≤ Pmass := hdiag.2.1
  have hc : 0 ≤ Pcap := hdiag.2.2.1
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
