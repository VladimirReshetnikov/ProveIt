import OAI.Combinatorics.Progressions.Polynomial.ForecastSlicedEarlyUnrestrictedPolynomialBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

noncomputable def allocatedSlicedGridResourceLog {A : Type*} [Semiring A]
    (m dim : ℕ) (D p v E : A) : A :=
  let L := fun (j : Fin m) (e : A) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p e
  let Cp := ∑ j, (L j 0 + D * (v + 1))
  let E' := uniformProductAccuracyLog D Cp E + D * (v + 1) + 1
  ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j E') + (D + 1) * (v + 1))

theorem allocatedSlicedGridResourceLog_nonneg (m dim : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedSlicedGridResourceLog m dim D p v E := by
  unfold allocatedSlicedGridResourceLog
  dsimp only
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · apply siteExponentialOutputLog_nonneg
    apply (slicedGridSiteLog_bounds _ _ _ _ hD hp ?_).1
    apply add_nonneg _ zero_le_one
    apply add_nonneg _ (by positivity)
    apply uniformProductAccuracyLog_nonneg hD _ hE
    exact Finset.sum_nonneg (fun i _ =>
      add_nonneg (slicedGridSiteLog_bounds _ _ _ _ hD hp (le_refl 0)).1 (by positivity))
  · positivity

theorem exists_allocatedSlicedGridResource_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v E : ℝ}, 0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ E →
      allocatedSlicedGridResourceLog m dim D p v E ≤ (D + p + v + E + A) ^ A := by
  obtain ⟨b, hb, hsite⟩ := exists_slicedGridSiteLog_uniform_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let Cp : Polynomial ℕ := (m : Polynomial ℕ) * ((X + Polynomial.C b) ^ b + X * (X + 1))
  let Epoly := uniformProductAccuracyLog X Cp X + X * (X + 1) + 1
  let poly : Polynomial ℕ := (m : Polynomial ℕ) *
    (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) ((2 * X + Epoly + Polynomial.C b) ^ b) + (X + 1) ^ 2)
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v E hD hp hv hE
  let R := D + p + v + E
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hER : E ≤ R := by dsimp [R]; linarith
  let L := fun (j : Fin m) (e : ℝ) => slicedGridSiteLog j.val
    (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
    ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card)
    ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) D p e
  have hL0 (j : Fin m) : L j 0 ≤ (R + b) ^ b :=
    (hsite hD hp (le_refl (0 : ℝ)) j).trans
      (pow_le_pow_left₀ (by positivity) (by dsimp [R]; linarith) b)
  let Cbound := (m : ℝ) * ((R + b) ^ b + R * (R + 1))
  have hCb : 0 ≤ Cbound := by dsimp [Cbound]; positivity
  have hCp0 : 0 ≤ ∑ j : Fin m, (L j 0 + D * (v + 1)) :=
    Finset.sum_nonneg (fun j _ => add_nonneg (slicedGridSiteLog_bounds _ _ _ _ hD hp (le_refl 0)).1 (by positivity))
  have hCp : (∑ j : Fin m, (L j 0 + D * (v + 1))) ≤ Cbound := by
    calc
      _ ≤ ∑ _j : Fin m, ((R + b) ^ b + R * (R + 1)) := Finset.sum_le_sum (fun j _ => by
        apply add_le_add (hL0 j)
        exact mul_le_mul hDR (add_le_add hvR le_rfl) (by positivity) hR)
      _ = _ := by simp [Cbound, mul_add]
  let E' := uniformProductAccuracyLog D (∑ j, (L j 0 + D * (v + 1))) E + D * (v + 1) + 1
  let Ebound := uniformProductAccuracyLog R Cbound R + R * (R + 1) + 1
  have hE' : 0 ≤ E' := by
    dsimp only [E']
    exact add_nonneg (add_nonneg (uniformProductAccuracyLog_nonneg hD hCp0 hE) (by positivity)) zero_le_one
  have hEb : 0 ≤ Ebound := by
    dsimp only [Ebound]
    exact add_nonneg (add_nonneg (uniformProductAccuracyLog_nonneg hR hCb hR) (by positivity)) zero_le_one
  have hEbound : E' ≤ Ebound := by
    dsimp only [E', Ebound, uniformProductAccuracyLog]
    gcongr
  have hL (j : Fin m) : L j E' ≤ (2 * R + Ebound + b) ^ b :=
    (hsite hD hp hE' j).trans (pow_le_pow_left₀ (by positivity)
      (by linarith only [hDR, hpR, hEbound]) b)
  have htotal : allocatedSlicedGridResourceLog m dim D p v E ≤
      (m : ℝ) * (siteExponentialOutputLog (Fintype.card (Finset (Fin dim)))
        ((2 * R + Ebound + b) ^ b) + (R + 1) ^ 2) := by
    change (∑ j : Fin m, (siteExponentialOutputLog _ (L j E') + (D + 1) * (v + 1))) ≤ _
    calc
      _ ≤ ∑ _j : Fin m, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim)))
          ((2 * R + Ebound + b) ^ b) + (R + 1) ^ 2) := Finset.sum_le_sum (fun j _ => by
        apply add_le_add
        · unfold siteExponentialOutputLog
          gcongr
          all_goals exact hL j
        · rw [pow_two]
          exact mul_le_mul (add_le_add hDR le_rfl) (add_le_add hvR le_rfl) (by positivity) (by positivity))
      _ = _ := by simp [mul_add]
  apply htotal.trans
  simpa [poly, X, Epoly, Cp, Ebound, Cbound, uniformProductAccuracyLog,
    siteExponentialOutputLog, Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

end OAI
