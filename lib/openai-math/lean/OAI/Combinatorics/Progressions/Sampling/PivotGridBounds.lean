import OAI.Combinatorics.Progressions.Estimates.PivotStageBoundary

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem rootGrid_volume (r q l : ℕ) :
    positiveGridVolume (Fin.cons r (fun _ : Fin l => q)) = r * q ^ l := by
  simp [positiveGridVolume, Fin.prod_univ_succ]

theorem pivotRootFactor_mean_grid {R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (hunit : ∀ j, IsUnit (slope - v j)) (f : R → ℝ) :
    (𝔼 z : Fin l → Fin q → R, 𝔼 w, pivotRootFactor v slope f z w) =
      positiveGridMean (Fin.cons 1 (fun _ : Fin l => q)) (fun _ => f) := by
  rw [← scaledRootGrid_mean 1 q l (fun j => slope - v j) hunit (fun _ _ => f)]
  apply Finset.expect_congr rfl
  intro z _
  symm
  rw [expect_fin_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.prod_univ_zero, mul_one,
    Fintype.expect_const, pivotRootFactor]

theorem pivot_boolean_product_mean_grid {R : Type*} [CommRing R] [Fintype R] {l q : ℕ}
    (v : Fin l → R) (slope : R) (hunit : ∀ j, IsUnit (slope - v j)) (f : R → ℝ)
    (choice : (Fin l → Fin q) → Bool) :
    (𝔼 z : Fin l → Fin q → R, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
      if choice beta then
        f (u + ∑ j, (slope - v j) * z j (beta j)) *
        f (w + ∑ j, (slope - v j) * z j (beta j)) else 1) =
      positiveGridMean (Fin.cons 2 (fun _ : Fin l => q))
        (fun beta x => if choice (fun j => beta j.succ) then f x else 1) := by
  rw [← scaledRootGrid_mean 2 q l (fun j => slope - v j) hunit
    (fun _ beta x => if choice beta then f x else 1)]
  apply Finset.expect_congr rfl
  intro z _
  symm
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro u _
  rw [expect_fin_cons]
  apply Finset.expect_congr rfl
  intro w _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.prod_univ_zero, mul_one,
    Fintype.expect_const]
  apply Finset.prod_congr rfl
  intro beta _
  by_cases h : choice beta
  · simp only [h, ite_true]
  · simp only [h, Bool.false_eq_true, ite_false, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_pivot_grid_bounds (s : ℕ) {delta C0 : ℝ} (hdelta : 0 < delta) (hC0 : 1 ≤ C0) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ {N l q : ℕ} [NeZero N] {p xi : ℝ}, 2 ≤ p → 0 < xi → xi ≤ xi0 →
      Odd N → Real.exp ((p + 2) ^ C) ≤ N → l ≤ s → 1 ≤ q → (q : ℝ) ≤ C0 * p →
      ∀ (v : Fin l → ZMod N) (slope : ZMod N), (∀ j, IsUnit (slope - v j)) →
      ∀ f : ZMod N → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C)
        (Real.exp (-((p + 2) ^ C))) f (fun _ => 1 + xi) →
      (𝔼 z : Fin l → Fin q → ZMod N, 𝔼 w, pivotRootFactor v slope f z w) ≤
        (1 + delta) ^ (q ^ l) ∧
      ∀ choice : (Fin l → Fin q) → Bool,
        (𝔼 z : Fin l → Fin q → ZMod N, 𝔼 u, 𝔼 w, ∏ beta : Fin l → Fin q,
          if choice beta then
            f (u + ∑ j, (slope - v j) * z j (beta j)) *
            f (w + ∑ j, (slope - v j) * z j (beta j)) else 1) ≤
          (1 + delta) ^ (2 * q ^ l) := by
  obtain ⟨C, hC, xi0, hxi0, hgrid⟩ := exists_positiveGrid_family_counting s hdelta hC0
  refine ⟨C, hC, xi0, hxi0, ?_⟩
  intro N l q _ p xi hp hxi hxib hodd hN hl hq hqcap v slope hunit f hf hcompare
  have hrootcap : (2 : ℝ) ≤ C0 * p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC0) (show 0 ≤ p by linarith)]
  have hshape (r : ℕ) (hr : 1 ≤ r) (hr2 : r ≤ 2) :
      ∀ i : Fin (l + 1), 1 ≤ (Fin.cons r (fun _ : Fin l => q) : Fin (l + 1) → ℕ) i ∧
        (((Fin.cons r (fun _ : Fin l => q) : Fin (l + 1) → ℕ) i : ℕ) : ℝ) ≤ C0 * p := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact ⟨hr, (show (r : ℝ) ≤ 2 by exact_mod_cast hr2).trans hrootcap⟩
    · exact ⟨hq, hqcap⟩
  have hbound (r : ℕ) (hr : 1 ≤ r) (hr2 : r ≤ 2)
      (ch : PositiveGridVertex (Fin.cons r (fun _ : Fin l => q)) → Option Unit) :
      positiveGridMean (Fin.cons r (fun _ : Fin l => q))
        (fun beta x => (ch beta).elim 1 (fun _ => f x)) ≤ (1 + delta) ^ (r * q ^ l) := by
    have h := hgrid hp hxi hxib hodd hN (show 1 ≤ l + 1 by omega)
      (show l + 1 ≤ s + 1 by omega) (Fin.cons r (fun _ : Fin l => q)) (hshape r hr hr2)
      (fun _ : Unit => f) (fun _ => hf) (fun _ => @hcompare) ch
    simpa only [rootGrid_volume] using h
  constructor
  · rw [pivotRootFactor_mean_grid v slope hunit]
    simpa only [Option.elim_some, one_mul] using hbound 1 (by omega) (by omega) (fun _ => some ())
  · intro choice
    rw [pivot_boolean_product_mean_grid v slope hunit f choice]
    let ch : PositiveGridVertex (Fin.cons 2 (fun _ : Fin l => q)) → Option Unit :=
      fun beta => if choice (fun j => beta j.succ) then some () else none
    have h := hbound 2 (by omega) (by omega) ch
    have heq : (fun beta x => (ch beta).elim 1 (fun _ => f x)) =
        (fun (beta : PositiveGridVertex (Fin.cons 2 (fun _ : Fin l => q))) x =>
          if choice (fun j => beta j.succ) then f x else 1) := by
      funext beta x
      dsimp only [ch]
      split_ifs <;> rfl
    rw [heq] at h
    exact h

end Erdos3

end

end OAI
