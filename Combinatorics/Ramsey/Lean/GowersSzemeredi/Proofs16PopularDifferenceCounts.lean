import GowersSzemeredi.Definitions

/-! Popular differences retain at least half the pairs of a dense set.
Shifted popular pairs carry uniformly many four-term representations.
These are the counting inputs to robust Bogolyubov progression extraction. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def differenceRepresentations {N : Nat} (A : Finset (ZMod N)) (d : ZMod N) :
    Finset (ZMod N × ZMod N) := (A ×ˢ A).filter fun p => p.1-p.2 = d

def shiftedDifferencePairs {N : Nat} (A K : Finset (ZMod N)) (t : ZMod N) :
    Finset (ZMod N × ZMod N) := (A ×ˢ A).filter fun p => p.1-p.2+t ∈ K

def fourDifferenceRepresentations {N : Nat} (A : Finset (ZMod N)) (t : ZMod N) :
    Finset (ZMod N × ZMod N × ZMod N × ZMod N) :=
  (A ×ˢ A ×ˢ A ×ˢ A).filter fun q => q.1-q.2.1+q.2.2.1-q.2.2.2 = t

def popularDifferenceSet {N : Nat} [NeZero N] (A : Finset (ZMod N)) (theta : Real) :
    Finset (ZMod N) := Finset.univ.filter fun d => theta ≤ ((differenceRepresentations A d).card : Real)

/-- The pairs whose difference is not popular number at most `theta*N`. -/
theorem unpopular_difference_pairs_card_le {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {theta : Real} (ht : 0 ≤ theta) :
    (((A ×ˢ A).filter fun p => p.1-p.2 ∉ popularDifferenceSet A theta).card : Real) ≤ theta*N := by
  let B := (A ×ˢ A).filter fun p => p.1-p.2 ∉ popularDifferenceSet A theta
  have hsum : B.card = ∑ d : ZMod N, (B.filter fun p => p.1-p.2 = d).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hfib : ∀ d : ZMod N, ((B.filter fun p => p.1-p.2 = d).card : Real) ≤ theta := by
    intro d
    by_cases hd : d ∈ popularDifferenceSet A theta
    · have hempty : B.filter (fun p => p.1-p.2 = d) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp he
        exact (Finset.mem_filter.mp hp).2 (he.symm ▸ hd)
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact ht
    · have hsmall : ((differenceRepresentations A d).card : Real) < theta := by
        exact not_le.mp fun h => hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      apply le_trans _ hsmall.le
      exact_mod_cast Finset.card_le_card (show B.filter (fun p => p.1-p.2 = d) ⊆
        differenceRepresentations A d from fun p hp =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
            (Finset.mem_filter.mp hp).2⟩)
  calc
    (B.card : Real) = ∑ d : ZMod N, ((B.filter fun p => p.1-p.2 = d).card : Real) := by exact_mod_cast hsum
    _ ≤ ∑ _d : ZMod N, theta := Finset.sum_le_sum fun d _ => hfib d
    _ = theta*N := by simp [mul_comm]

/-- With threshold `delta^2*N/2`, popular differences carry half of all pairs. -/
theorem popular_difference_pairs_dense {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {delta : Real} (hd : 0 ≤ delta)
    (hA : delta*N ≤ (A.card : Real)) :
    (A.card : Real)^2/2 ≤
      ((shiftedDifferencePairs A (popularDifferenceSet A (delta^2*N/2)) 0).card : Real) := by
  have hbad := unpopular_difference_pairs_card_le A (by positivity : 0 ≤ delta^2*N/2)
  have hsplit := Finset.card_filter_add_card_filter_not (s := A ×ˢ A)
    (fun p => p.1-p.2 ∈ popularDifferenceSet A (delta^2*N/2))
  have hsplitR : (((A ×ˢ A).filter fun p => p.1-p.2 ∈ popularDifferenceSet A (delta^2*N/2)).card : Real) +
      (((A ×ˢ A).filter fun p => p.1-p.2 ∉ popularDifferenceSet A (delta^2*N/2)).card : Real) =
        (A.card : Real)^2 := by
    rw [Finset.card_product] at hsplit
    exact_mod_cast (by simpa only [pow_two] using hsplit)
  have hsq : (delta*N)^2 ≤ (A.card : Real)^2 := pow_le_pow_left₀ (by positivity) hA 2
  simpa only [shiftedDifferencePairs, add_zero] using (by
    nlinarith : (A.card : Real)^2/2 ≤
      (((A ×ˢ A).filter fun p => p.1-p.2 ∈ popularDifferenceSet A (delta^2*N/2)).card : Real))

/-- Every shifted popular pair contributes its full difference fibre. -/
theorem four_difference_representations_ge_popular_pairs {N : Nat}
    (A K : Finset (ZMod N)) (t : ZMod N) {theta : Real}
    (hK : ∀ d ∈ K, theta ≤ ((differenceRepresentations A d).card : Real)) :
    theta*((shiftedDifferencePairs A K t).card : Real) ≤ (fourDifferenceRepresentations A t).card := by
  let P := shiftedDifferencePairs A K t
  let S := P.sigma fun p => differenceRepresentations A (p.1-p.2+t)
  have hcount : S.card ≤ (fourDifferenceRepresentations A t).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p.2.1, p.2.2, p.1.2, p.1.1))
    · intro p hp
      obtain ⟨hpP, hpD⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hpmem, hpK⟩ := Finset.mem_filter.mp hpP
      obtain ⟨hdmem, hdeq⟩ := Finset.mem_filter.mp hpD
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hpmem
      obtain ⟨hc, hd⟩ := Finset.mem_product.mp hdmem
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, Finset.mem_product.mpr
        ⟨hd, Finset.mem_product.mpr ⟨hb, ha⟩⟩⟩, by linear_combination hdeq⟩
    · intro p hp q hq he
      simp only [Prod.mk.injEq] at he
      have h1 : p.1 = q.1 := Prod.ext he.2.2.2 he.2.2.1
      cases p with | mk p1 p2 =>
        cases q with | mk q1 q2 =>
          dsimp only at h1 he
          subst q1
          exact Sigma.ext rfl (heq_of_eq (Prod.ext he.1 he.2.1))
  have hmass : theta*(P.card : Real) ≤ (S.card : Real) := by
    calc
      _ = ∑ _p ∈ P, theta := by simp [mul_comm]
      _ ≤ ∑ p ∈ P, ((differenceRepresentations A (p.1-p.2+t)).card : Real) :=
        Finset.sum_le_sum fun p hp => hK _ (Finset.mem_filter.mp hp).2
      _ = S.card := by exact_mod_cast (Finset.card_sigma P _).symm
  exact hmass.trans (by exact_mod_cast hcount)

end LeanProofs.GowersSzemeredi
