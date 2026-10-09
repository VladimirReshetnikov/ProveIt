import GowersSzemeredi.Proofs16ModelTestCells
import GowersSzemeredi.Proofs16ColumnWordRepresentations

/-! A cell refinement excludes detected models from arbitrary even
alternating column lists, with five cells per pair of entries. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem same_cell_even_anchor_bound {N Q : Nat} [NeZero N] [NeZero Q]
    (gamma : ZMod N) (f : ZMod N → ZMod N) (c : Fin Q) (k : Nat)
    (as : List (ZMod N)) (hlen : as.length = 2*k)
    (hcell : ∀ x ∈ as, dirichletCell Q (gamma*f x) = c) :
    centeredAbs (gamma*columnAnchorEval f as)*Q ≤ k*N := by
  induction k generalizing as with
  | zero =>
    have he : as = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    simp [he,columnAnchorEval,centeredAbs]
  | succ k ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      cases as with
      | nil => simp at hlen; omega
      | cons b bs =>
        have hbs : bs.length = 2*k := by simp only [List.length_cons] at hlen; omega
        have ht := ih bs hbs (fun x hx => hcell x (by simp [hx]))
        have hc := dirichletCell_close ((hcell a (by simp)).trans (hcell b (by simp)).symm)
        have he : gamma*columnAnchorEval f (a::b::bs) =
            (gamma*f a-gamma*f b)+gamma*columnAnchorEval f bs := by
          simp only [columnAnchorEval]
          ring
        rw [he]
        calc _ ≤ (centeredAbs (gamma*f a-gamma*f b)+centeredAbs (gamma*columnAnchorEval f bs))*Q :=
            Nat.mul_le_mul_right _ (centeredAbs_add_le _ _)
          _ = centeredAbs (gamma*f a-gamma*f b)*Q+centeredAbs (gamma*columnAnchorEval f bs)*Q := by ring
          _ ≤ N+k*N := Nat.add_le_add hc.le ht
          _ = (k+1)*N := by ring

theorem same_cell_even_not_separates {N k : Nat} [NeZero N] [NeZero k]
    (gamma : ZMod N) (f : ZMod N → ZMod N) (c : Fin (5*k))
    (as : List (ZMod N)) (hlen : as.length = 2*k)
    (hcell : ∀ x ∈ as, dirichletCell (5*k) (gamma*f x) = c) :
    ¬ Separates gamma (columnAnchorEval f as) := by
  have h := same_cell_even_anchor_bound gamma f c k as hlen hcell
  have hn : 5*centeredAbs (gamma*columnAnchorEval f as) ≤ N := by
    apply Nat.le_of_mul_le_mul_right (c := k)
    · nlinarith only [h]
    · exact NeZero.pos k
  exact Nat.not_lt.mpr hn

/-- The same selected test rules out every detected model on every
length-`2*k` alternating list from the retained cell. -/
theorem exists_even_model_test_cell {J : Type*} {N g d k : Nat} [NeZero N] [Fact N.Prime] [NeZero k]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hI : I.Nonempty) (hGamma : Gamma.card ≤ g)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hne : ∀ j ∈ I, ∃ y ∈ bohr Gamma (refinementKernelRadius g d rho (r/2)), f j y ≠ 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N) :
    ∃ (P : Finset (ZMod N)) (y gamma : ZMod N), P ⊆ A ∧
      modelTestDensity g d r/(5*k)*A.card ≤ (P.card : Real) ∧
      y ∈ bohr Gamma r ∧ (∀ x ∈ P, y ∈ bohr (T x) r) ∧
      modelTestDensity g d r*I.card ≤ ((I.filter (fun j => Separates gamma (f j y))).card : Real) ∧
      ∀ as : List (ZMod N), as.length = 2*k → (∀ x ∈ as, x ∈ P) → ∀ j ∈ I,
        Separates gamma (f j y) → columnAnchorEval (fun x => L x y) as ≠ f j y := by
  obtain ⟨y,gamma,hy,hAcount,hIcount⟩ := exists_model_test A I Gamma T f hrho hr hrle hA hI hGamma hT hf hf0 hne hN h7
  let S := A.filter (fun x => y ∈ bohr (T x) r)
  let cell := fun x => dirichletCell (5*k) (gamma*L x y)
  have hk : (0 : Real) < 5*k := by exact_mod_cast Nat.mul_pos (by decide : 0 < 5) (NeZero.pos k)
  obtain ⟨t,_,ht⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := (Finset.univ : Finset (Fin (5*k)))) (f := cell) (b := (S.card : Real)/(5*k))
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hk)])
  let P := S.filter (fun x => cell x = t)
  have hP : modelTestDensity g d r/(5*k)*A.card ≤ (P.card : Real) := by
    have h := div_le_div_of_nonneg_right hAcount hk.le
    change (S.card : Real)/(5*k) ≤ (P.card : Real) at ht
    have h' : modelTestDensity g d r/(5*k)*A.card ≤ (S.card : Real)/(5*k) := by
      simpa only [div_mul_eq_mul_div] using h
    exact h'.trans ht
  refine ⟨P,y,gamma,?_,hP,hy,?_,hIcount,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  · intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  · intro as hlen has j _ hsep heq
    have hc : ∀ x ∈ as, dirichletCell (5*k) (gamma*L x y) = t :=
      fun x hx => (Finset.mem_filter.mp (has x hx)).2
    exact same_cell_even_not_separates gamma (fun x => L x y) t as hlen hc (heq.symm ▸ hsep)

end LeanProofs.GowersSzemeredi
