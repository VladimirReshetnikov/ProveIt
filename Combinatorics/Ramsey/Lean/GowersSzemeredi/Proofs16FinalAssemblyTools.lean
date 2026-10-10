import GowersSzemeredi.Proofs16FinalWindow
import GowersSzemeredi.Proofs16PropNineThreeTwelve

/-! Counting tools for assembling Milićević's Proposition 9.3 output
(arXiv:2601.01682, printed pp. 67–68). The assembly design is in J.5c.

* `twelveXSide`, `twelveYSide`: the x- and y-side 8-tuples of a 12-tuple.
  `columnTupleFrequencies` of them are `twelveK` and `twelveL`
  (`columnTupleFrequencies_twelveXSide`, `…YSide`), so a 12-tuple that is
  not bad gives exactly the split hypothesis of `glued_quadruple_respected`.
* `exists_quadruple_window`: the window `J` chosen *for quadruples*. If
  every `S_a ⊆ [m]` has `|S_a| ≤ k` and `4k ≤ m`, some `J` of size `4k`
  contains all four `S_{q_j}` for at least `|Q|/C(m, 4k)` of the
  quadruples `q ∈ Q`.
* `dense_additive_quadruples_ge`: a set `A ⊆ ℤ/N` contains at least
  `|A|³ − (N − |A|)·N²` additive quadruples `q₀ + q₁ = q₂ + q₃`.
* `markov_large_fibers`: if `∑_a |G_a| ≥ (1 − η)·N·M` with every
  `|G_a| ≤ M`, then at least `(1 − 2η)N` values of `a` have
  `|G_a| ≥ M/2`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The x-side 8-tuple `(x_j + a_j, x_j)_j` of a 12-tuple. -/
def twelveXSide {N : Nat} (u : Fin 11 → ZMod N) : Fin 8 → ZMod N :=
  ![twelvePoint u 0 0, twelvePoint u 0 1, twelvePoint u 1 0, twelvePoint u 1 1,
    twelvePoint u 2 0, twelvePoint u 2 1, twelvePoint u 3 0, twelvePoint u 3 1]

/-- The y-side 8-tuple `(y_j + a_j, y_j)_j` of a 12-tuple. -/
def twelveYSide {N : Nat} (u : Fin 11 → ZMod N) : Fin 8 → ZMod N :=
  ![twelvePoint u 0 2, twelvePoint u 0 3, twelvePoint u 1 2, twelvePoint u 1 3,
    twelvePoint u 2 2, twelvePoint u 2 3, twelvePoint u 3 2, twelvePoint u 3 3]

theorem columnTuplePairs_twelveXSide {N : Nat} (u : Fin 11 → ZMod N) (j : Fin 4) :
    columnTuplePairs (twelveXSide u) j = (twelvePoint u j 0, twelvePoint u j 1) := by
  fin_cases j <;> rfl

theorem columnTuplePairs_twelveYSide {N : Nat} (u : Fin 11 → ZMod N) (j : Fin 4) :
    columnTuplePairs (twelveYSide u) j = (twelvePoint u j 2, twelvePoint u j 3) := by
  fin_cases j <;> rfl

theorem columnTupleFrequencies_twelveXSide {N : Nat} (T : ZMod N → Finset (ZMod N))
    (u : Fin 11 → ZMod N) : columnTupleFrequencies T (twelveXSide u) = twelveK T u := by
  ext z
  simp only [columnTupleFrequencies, twelveK, Finset.mem_biUnion, Finset.mem_univ, true_and,
    columnTuplePairs_twelveXSide, columnDifferenceSpectrum]

theorem columnTupleFrequencies_twelveYSide {N : Nat} (T : ZMod N → Finset (ZMod N))
    (u : Fin 11 → ZMod N) : columnTupleFrequencies T (twelveYSide u) = twelveL T u := by
  ext z
  simp only [columnTupleFrequencies, twelveL, Finset.mem_biUnion, Finset.mem_univ, true_and,
    columnTuplePairs_twelveYSide, columnDifferenceSpectrum]

/-- **The window chosen for quadruples.** -/
theorem exists_quadruple_window {α : Type*} (Q : Finset (Fin 4 → α)) (S : α → Finset Nat)
    {m k : Nat} (hk : 4 * k ≤ m) (hS : ∀ a, S a ⊆ Finset.range m ∧ (S a).card ≤ k) :
    ∃ J ⊆ Finset.range m, J.card = 4 * k ∧
      Q.card ≤ m.choose (4 * k) * (Q.filter fun q => ∀ j, S (q j) ⊆ J).card := by
  have hS' : ∀ q ∈ Q, (Finset.univ.biUnion fun j => S (q j)) ⊆ Finset.range m ∧
      (Finset.univ.biUnion fun j => S (q j)).card ≤ 4 * k := by
    intro q _
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hi
      exact (hS (q j)).1 hj
    · refine Finset.card_biUnion_le.trans ?_
      calc ∑ j : Fin 4, (S (q j)).card ≤ ∑ _j : Fin 4, k :=
            Finset.sum_le_sum fun j _ => (hS _).2
        _ = 4 * k := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨J, hJ, hJcard, hcount⟩ := exists_index_window Q
    (fun q => Finset.univ.biUnion fun j => S (q j)) hk hS'
  refine ⟨J, hJ, hJcard, hcount.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))⟩
  intro q hq
  obtain ⟨hqQ, hsub⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨hqQ, fun j => ?_⟩
  exact (Finset.subset_biUnion_of_mem (fun j => S (q j)) (Finset.mem_univ j)).trans hsub

/-- The additive quadruples with all entries in `A`. -/
def additiveQuadruplesIn {N : Nat} [NeZero N] (A : Finset (ZMod N)) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => q 0 + q 1 = q 2 + q 3 ∧ ∀ j, q j ∈ A

/-- **Dense sets have many additive quadruples.** -/
theorem dense_additive_quadruples_ge {N : Nat} [NeZero N] (A : Finset (ZMod N)) :
    (A.card : Real) ^ 3 - ((N : Real) - A.card) * (N : Real) ^ 2 ≤
      (additiveQuadruplesIn A).card := by
  let tri := (A ×ˢ A ×ˢ A)
  let good := tri.filter fun t => t.1 + t.2.1 - t.2.2 ∈ A
  let bad := tri.filter fun t => t.1 + t.2.1 - t.2.2 ∉ A
  have hsplit : (good.card : Real) + bad.card = (A.card : Real) ^ 3 := by
    have h := Finset.card_filter_add_card_filter_not (s := tri)
      (fun t => t.1 + t.2.1 - t.2.2 ∈ A)
    rw [Finset.card_product, Finset.card_product] at h
    have : (good.card + bad.card : Nat) = A.card * (A.card * A.card) := h
    rw [show (A.card : Real) ^ 3 = ((A.card * (A.card * A.card) : Nat) : Real) by
      push_cast; ring, ← this]
    push_cast; ring
  -- each value outside `A` is hit by at most `N²` triples
  have hbad : (bad.card : Real) ≤ ((N : Real) - A.card) * (N : Real) ^ 2 := by
    have hmaps : ∀ t ∈ bad, t.1 + t.2.1 - t.2.2 ∈ Aᶜ := fun t ht =>
      Finset.mem_compl.mpr (Finset.mem_filter.mp ht).2
    have h := Finset.card_eq_sum_card_fiberwise hmaps
    have hfib : ∀ c ∈ Aᶜ,
        (bad.filter fun t => t.1 + t.2.1 - t.2.2 = c).card ≤ N ^ 2 := by
      intro c _
      have : (bad.filter fun t => t.1 + t.2.1 - t.2.2 = c).card ≤
          ((Finset.univ : Finset (ZMod N)) ×ˢ (Finset.univ : Finset (ZMod N))).card := by
        refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) (fun _ _ => by simp) ?_
        intro t ht t' ht' htt
        simp only [Prod.mk.injEq] at htt
        have e := (Finset.mem_filter.mp ht).2
        have e' := (Finset.mem_filter.mp ht').2
        refine Prod.ext htt.1 (Prod.ext htt.2 ?_)
        rw [htt.1, htt.2] at e
        have := e.trans e'.symm
        linear_combination -this
      rwa [Finset.card_product, Finset.card_univ, ZMod.card, ← sq] at this
    have hcompl : ((Aᶜ).card : Real) = (N : Real) - A.card := by
      rw [Finset.card_compl, ZMod.card,
        Nat.cast_sub (by simpa [ZMod.card] using Finset.card_le_univ A)]
    calc (bad.card : Real) = ∑ c ∈ Aᶜ,
          ((bad.filter fun t => t.1 + t.2.1 - t.2.2 = c).card : Real) := by
          rw [h]; push_cast; rfl
      _ ≤ ∑ _c ∈ Aᶜ, ((N ^ 2 : Nat) : Real) :=
          Finset.sum_le_sum fun c hc => by exact_mod_cast hfib c hc
      _ = ((N : Real) - A.card) * (N : Real) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcompl]; push_cast; ring
  -- good triples inject into the quadruples
  have hgood : good.card ≤ (additiveQuadruplesIn A).card := by
    refine Finset.card_le_card_of_injOn (fun t => ![t.1, t.2.1, t.2.2, t.1 + t.2.1 - t.2.2]) ?_ ?_
    · intro t ht
      obtain ⟨htri, h4⟩ := Finset.mem_filter.mp ht
      obtain ⟨h1, h23⟩ := Finset.mem_product.mp htri
      obtain ⟨h2, h3⟩ := Finset.mem_product.mp h23
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, fun j => ?_⟩
      · show t.1 + t.2.1 = t.2.2 + (t.1 + t.2.1 - t.2.2)
        ring
      · fin_cases j
        · exact h1
        · exact h2
        · exact h3
        · exact h4
    · intro t _ t' _ htt
      have e0 := congrFun htt 0
      have e1 := congrFun htt 1
      have e2 := congrFun htt 2
      exact Prod.ext e0 (Prod.ext e1 e2)
  have : (good.card : Real) ≤ (additiveQuadruplesIn A).card := by exact_mod_cast hgood
  linarith

/-- **Markov for fibre sizes.** -/
theorem markov_large_fibers {N : Nat} [NeZero N] (G : ZMod N → Nat) {M : Real} (hM : 0 < M)
    (hG : ∀ a, (G a : Real) ≤ M) {η : Real}
    (hsum : (1 - η) * N * M ≤ ∑ a : ZMod N, (G a : Real)) :
    (1 - 2 * η) * N ≤ ((Finset.univ.filter fun a : ZMod N => M / 2 ≤ G a).card : Real) := by
  set A := Finset.univ.filter fun a : ZMod N => M / 2 ≤ G a with hA
  have hsplit : ∑ a : ZMod N, (G a : Real) =
      ∑ a ∈ A, (G a : Real) + ∑ a ∈ Aᶜ, (G a : Real) :=
    (Finset.sum_add_sum_compl A _).symm
  have h1 : ∑ a ∈ A, (G a : Real) ≤ A.card * M := by
    calc ∑ a ∈ A, (G a : Real) ≤ ∑ _a ∈ A, M := Finset.sum_le_sum fun a _ => hG a
      _ = A.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ a ∈ Aᶜ, (G a : Real) ≤ ((N : Real) - A.card) * (M / 2) := by
    have hc : ((Aᶜ).card : Real) = (N : Real) - A.card := by
      rw [Finset.card_compl, ZMod.card,
        Nat.cast_sub (by simpa [ZMod.card] using Finset.card_le_univ A)]
    calc ∑ a ∈ Aᶜ, (G a : Real) ≤ ∑ _a ∈ Aᶜ, M / 2 :=
          Finset.sum_le_sum fun a ha => by
            have : a ∉ A := Finset.mem_compl.mp ha
            simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at this
            exact this.le
      _ = ((N : Real) - A.card) * (M / 2) := by rw [Finset.sum_const, nsmul_eq_mul, hc]
  have hAN : (A.card : Real) ≤ N := by
    have := Finset.card_le_univ A
    rw [ZMod.card] at this
    exact_mod_cast this
  nlinarith

end LeanProofs.GowersSzemeredi
