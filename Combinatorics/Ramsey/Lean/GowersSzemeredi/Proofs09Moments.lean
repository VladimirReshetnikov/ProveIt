import GowersSzemeredi.Proofs05_10

/-!
# Higher Fourier moments of a function graph

This module proves Gowers's Lemma 9.2.  Its main ingredient identifies the
`2k`-th Fourier moment of the indicator of the graph of a partial function
with the number of respected additive `2k`-tuples.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def section9Phase {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u x : ZMod N) : Complex :=
  indicator B x * exponential (phi x * u)

@[simp] private lemma section9_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma section9_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma section9_norm_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : ‖exponential x‖ = 1 := by
  exact (ZMod.stdAddChar (N := N)).norm_apply x

private lemma ofReal_norm_even_pow (z : Complex) (k : Nat) :
    (((‖z‖ ^ (2 * k) : Real)) : Complex) = z ^ k * star z ^ k := by
  calc
    (((‖z‖ ^ (2 * k) : Real)) : Complex) =
        (((‖z‖ ^ 2 : Real)) : Complex) ^ k := by
      rw [← Complex.ofReal_pow]
      rw [← pow_mul]
    _ = (z * star z) ^ k := by
      congr 1
      rw [Complex.star_def, Complex.mul_conj']
      norm_cast
    _ = z ^ k * star z ^ k := by rw [mul_pow]

private abbrev section9Mem {N k : Nat} (B : Finset (ZMod N))
    (a : Fin k → ZMod N) : Prop :=
  ∀ i, a i ∈ B

private abbrev section9PairGood {N k : Nat} (B : Finset (ZMod N))
    (phi : ZMod N → ZMod N)
    (p : (Fin k → ZMod N) × (Fin k → ZMod N)) : Prop :=
  section9Mem B p.1 ∧ section9Mem B p.2 ∧
    (∑ i, p.1 i) = ∑ i, p.2 i ∧
    (∑ i, phi (p.1 i)) = ∑ i, phi (p.2 i)

private def section9PairEquiv (k : Nat) (G : Type*) :
    ((Fin k → G) × (Fin k → G)) ≃ (Fin (2 * k) → G) :=
  (Fin.appendEquiv k k).trans
    ((finCongr (Nat.two_mul k).symm).arrowCongr (Equiv.refl G))

private def section9LeftIndex (k : Nat) (i : Fin k) : Fin (2 * k) :=
  Fin.cast (Nat.two_mul k).symm (Fin.castAdd k i)

private def section9RightIndex (k : Nat) (i : Fin k) : Fin (2 * k) :=
  Fin.cast (Nat.two_mul k).symm (Fin.natAdd k i)

@[simp] private lemma section9PairEquiv_left (k : Nat) (G : Type*)
    (a b : Fin k → G) (i : Fin k) :
    section9PairEquiv k G (a, b) (section9LeftIndex k i) = a i := by
  simp [section9PairEquiv, section9LeftIndex]

@[simp] private lemma section9PairEquiv_right (k : Nat) (G : Type*)
    (a b : Fin k → G) (i : Fin k) :
    section9PairEquiv k G (a, b) (section9RightIndex k i) = b i := by
  change Fin.append a b (Fin.natAdd k i) = b i
  exact Fin.append_right a b i

private lemma section9_leftIndex_mem (k : Nat) (i : Fin k) :
    (section9LeftIndex k i : Nat) < k := by
  simp [section9LeftIndex]

private lemma section9_rightIndex_mem (k : Nat) (i : Fin k) :
    k ≤ (section9RightIndex k i : Nat) := by
  simp [section9RightIndex]

private lemma section9_leftIndex_injective (k : Nat) :
    Function.Injective (section9LeftIndex k) := by
  intro i j hij
  apply Fin.ext
  simpa [section9LeftIndex] using congrArg Fin.val hij

private lemma section9_rightIndex_injective (k : Nat) :
    Function.Injective (section9RightIndex k) := by
  intro i j hij
  apply Fin.ext
  simpa [section9RightIndex] using congrArg Fin.val hij

private lemma section9_leftIndex_surj (k : Nat) (j : Fin (2 * k))
    (hj : (j : Nat) < k) :
    ∃ i : Fin k, section9LeftIndex k i = j := by
  refine ⟨⟨j, hj⟩, ?_⟩
  apply Fin.ext
  simp [section9LeftIndex]

private lemma section9_rightIndex_surj (k : Nat) (j : Fin (2 * k))
    (hj : k ≤ (j : Nat)) :
    ∃ i : Fin k, section9RightIndex k i = j := by
  have hjlt : (j : Nat) < k + k := by
    simpa [Nat.two_mul] using j.isLt
  refine ⟨⟨(j : Nat) - k, by omega⟩, ?_⟩
  apply Fin.ext
  simp [section9RightIndex]
  omega

private lemma section9_sum_left {G : Type*} [AddCommMonoid G] (k : Nat)
    (a b : Fin k → G) :
    (Finset.univ.filter (fun j : Fin (2 * k) ↦ (j : Nat) < k)).sum
      (fun j ↦ section9PairEquiv k G (a, b) j) = ∑ i, a i := by
  symm
  apply Finset.sum_bij (fun i _ ↦ section9LeftIndex k i)
  · intro i _
    simp [section9_leftIndex_mem]
  · intro i _ j _ hij
    exact section9_leftIndex_injective k hij
  · intro j hj
    have hjlt : (j : Nat) < k := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := section9_leftIndex_surj k j hjlt
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (section9PairEquiv_left k G a b i).symm

private lemma section9_sum_right {G : Type*} [AddCommMonoid G] (k : Nat)
    (a b : Fin k → G) :
    (Finset.univ.filter (fun j : Fin (2 * k) ↦ k ≤ (j : Nat))).sum
      (fun j ↦ section9PairEquiv k G (a, b) j) = ∑ i, b i := by
  symm
  apply Finset.sum_bij (fun i _ ↦ section9RightIndex k i)
  · intro i _
    simp [section9_rightIndex_mem]
  · intro i _ j _ hij
    exact section9_rightIndex_injective k hij
  · intro j hj
    have hjge : k ≤ (j : Nat) := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := section9_rightIndex_surj k j hjge
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (section9PairEquiv_right k G a b i).symm

private lemma section9_mem_pair_iff {N k : Nat} (B : Finset (ZMod N))
    (a b : Fin k → ZMod N) :
    (∀ j, section9PairEquiv k (ZMod N) (a, b) j ∈ B) ↔
      section9Mem B a ∧ section9Mem B b := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h (section9LeftIndex k i)
    · intro i
      simpa using h (section9RightIndex k i)
  · rintro ⟨ha, hb⟩ j
    by_cases hj : (j : Nat) < k
    · obtain ⟨i, rfl⟩ := section9_leftIndex_surj k j hj
      simpa using ha i
    · obtain ⟨i, rfl⟩ := section9_rightIndex_surj k j (by omega)
      simpa using hb i

private lemma section9PairEquiv_comp {G H : Type*} (k : Nat)
    (f : G → H) (a b : Fin k → G) (j : Fin (2 * k)) :
    f (section9PairEquiv k G (a, b) j) =
      section9PairEquiv k H (f ∘ a, f ∘ b) j := by
  by_cases hj : (j : Nat) < k
  · obtain ⟨i, rfl⟩ := section9_leftIndex_surj k j hj
    simp
  · obtain ⟨i, rfl⟩ := section9_rightIndex_surj k j (by omega)
    simp

private lemma section9_sum_left_comp {G H : Type*} [AddCommMonoid H]
    (k : Nat) (f : G → H) (a b : Fin k → G) :
    (Finset.univ.filter (fun j : Fin (2 * k) ↦ (j : Nat) < k)).sum
        (fun j ↦ f (section9PairEquiv k G (a, b) j)) =
      ∑ i, f (a i) := by
  calc
    _ = (Finset.univ.filter (fun j : Fin (2 * k) ↦ (j : Nat) < k)).sum
        (fun j ↦ section9PairEquiv k H (f ∘ a, f ∘ b) j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact section9PairEquiv_comp k f a b j
    _ = ∑ i, f (a i) := by
          simpa [Function.comp_apply] using
            section9_sum_left (G := H) k (f ∘ a) (f ∘ b)

private lemma section9_sum_right_comp {G H : Type*} [AddCommMonoid H]
    (k : Nat) (f : G → H) (a b : Fin k → G) :
    (Finset.univ.filter (fun j : Fin (2 * k) ↦ k ≤ (j : Nat))).sum
        (fun j ↦ f (section9PairEquiv k G (a, b) j)) =
      ∑ i, f (b i) := by
  calc
    _ = (Finset.univ.filter (fun j : Fin (2 * k) ↦ k ≤ (j : Nat))).sum
        (fun j ↦ section9PairEquiv k H (f ∘ a, f ∘ b) j) := by
          apply Finset.sum_congr rfl
          intro j _
          exact section9PairEquiv_comp k f a b j
    _ = ∑ i, f (b i) := by
          simpa [Function.comp_apply] using
            section9_sum_right (G := H) k (f ∘ a) (f ∘ b)

@[simp] private lemma section9_prod_exponential {N k : Nat} [NeZero N]
    (f : Fin k → ZMod N) :
    ∏ i, exponential (f i) = exponential (∑ i, f i) := by
  symm
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [exponential]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        section9_exponential_add, ih]

private lemma section9_prod_indicator {N k : Nat}
    (B : Finset (ZMod N)) (a : Fin k → ZMod N) :
    ∏ i, indicator B (a i) = if section9Mem B a then 1 else 0 := by
  classical
  by_cases h : section9Mem B a
  · simp [indicator, h]
  · simp only [section9Mem, not_forall] at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg]
    · exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [indicator, hi])
    · simpa only [section9Mem] using not_forall.mpr ⟨i, hi⟩

private lemma section9_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) = if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma section9_pair_count_eq {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    countWhere (section9PairGood (k := k) B phi) =
      phiAdditiveTupleCount k B phi := by
  classical
  unfold phiAdditiveTupleCount countWhere IsAdditiveTuple
  apply Finset.card_equiv (section9PairEquiv k (ZMod N))
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [section9_mem_pair_iff B p.1 p.2,
    section9_sum_left k p.1 p.2, section9_sum_right k p.1 p.2,
    section9_sum_left_comp k phi p.1 p.2,
    section9_sum_right_comp k phi p.1 p.2]
  simp only [section9PairGood, and_assoc]

private def section9FourierTerm {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u r x : ZMod N) : Complex :=
  exponential (-(x * r)) * section9Phase B phi u x

private lemma section9_prod_fourierTerm {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u r : ZMod N) (a : Fin k → ZMod N) :
    ∏ i, section9FourierTerm B phi u r (a i) =
      if section9Mem B a then
        exponential (-((∑ i, a i) * r) + (∑ i, phi (a i)) * u)
      else 0 := by
  classical
  by_cases hmem : section9Mem B a
  · rw [if_pos hmem]
    simp only [section9FourierTerm, section9Phase, indicator,
      if_pos (hmem _), one_mul]
    simp_rw [← section9_exponential_add]
    rw [section9_prod_exponential]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_mul, Finset.sum_mul]
  · rw [if_neg hmem]
    simp only [section9Mem, not_forall] at hmem
    obtain ⟨i, hi⟩ := hmem
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [section9FourierTerm, section9Phase, indicator, hi]

private lemma section9_pair_orthogonality {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (a b : Fin k → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
      (∏ i, section9FourierTerm B phi u r (a i)) *
        star (∏ i, section9FourierTerm B phi u r (b i))) =
      if section9PairGood B phi (a, b) then (N : Complex) ^ 2 else 0 := by
  classical
  by_cases ha : section9Mem B a <;> by_cases hb : section9Mem B b
  · simp_rw [section9_prod_fourierTerm, if_pos ha, if_pos hb,
      section9_star_exponential, ← section9_exponential_add]
    have hphase (u r : ZMod N) :
        (-((∑ i, a i) * r) + (∑ i, phi (a i)) * u) +
            -(-((∑ i, b i) * r) + (∑ i, phi (b i)) * u) =
          ((∑ i, phi (a i)) - ∑ i, phi (b i)) * u +
            ((∑ i, b i) - ∑ i, a i) * r := by
      ring
    simp_rw [hphase, section9_exponential_add]
    calc
      (∑ u : ZMod N, ∑ r : ZMod N,
          exponential (((∑ i, phi (a i)) - ∑ i, phi (b i)) * u) *
            exponential (((∑ i, b i) - ∑ i, a i) * r)) =
          (∑ u : ZMod N,
            exponential (((∑ i, phi (a i)) - ∑ i, phi (b i)) * u)) *
          (∑ r : ZMod N,
            exponential (((∑ i, b i) - ∑ i, a i) * r)) := by
              simp_rw [← Finset.mul_sum]
              rw [← Finset.sum_mul]
      _ = if section9PairGood B phi (a, b) then (N : Complex) ^ 2 else 0 := by
            rw [section9_sum_exponential_mul, section9_sum_exponential_mul]
            by_cases hadd : (∑ i, a i) = ∑ i, b i
            · by_cases hphi : (∑ i, phi (a i)) = ∑ i, phi (b i)
              · simp [section9PairGood, ha, hb, hadd, hphi, pow_two]
              · have hdiff : (∑ i, phi (a i)) - ∑ i, phi (b i) ≠ 0 :=
                  sub_ne_zero.mpr hphi
                have hdiff' : 0 ≠ (∑ i, phi (a i)) - ∑ i, phi (b i) :=
                  hdiff.symm
                simp [section9PairGood, hadd, hphi, hdiff]
            · have hdiff : (∑ i, b i) - ∑ i, a i ≠ 0 :=
                sub_ne_zero.mpr (Ne.symm hadd)
              have hdiff' : 0 ≠ (∑ i, b i) - ∑ i, a i := hdiff.symm
              by_cases hphi : (∑ i, phi (a i)) = ∑ i, phi (b i)
              · simp [section9PairGood, hadd, hphi, hdiff]
              · have hpdiff : (∑ i, phi (a i)) - ∑ i, phi (b i) ≠ 0 :=
                  sub_ne_zero.mpr hphi
                have hpdiff' : 0 ≠
                    (∑ i, phi (a i)) - ∑ i, phi (b i) := hpdiff.symm
                simp [section9PairGood, hadd, hphi, hdiff, hpdiff]
  · simp [section9_prod_fourierTerm, hb, section9PairGood]
  · simp [section9_prod_fourierTerm, ha, section9PairGood]
  · simp [section9_prod_fourierTerm, ha, hb, section9PairGood]

private lemma section9_sum_ite_const_eq_countWhere {X : Type*} [Fintype X]
    (P : X → Prop) [DecidablePred P] (c : Complex) :
    (∑ x : X, if P x then c else 0) = (countWhere P : Nat) • c := by
  classical
  have hcard : (Finset.univ.filter P).card = countWhere P := by
    unfold countWhere
    apply congrArg Finset.card
    ext x
    simp
  calc
    (∑ x : X, if P x then c else 0) =
        (Finset.univ.filter P).card • c := by
          rw [← Finset.sum_filter]
          simp
    _ = (countWhere P : Nat) • c := by rw [hcard]

private lemma section9_fourier_eq {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u r : ZMod N) :
    fourier (section9Phase B phi u) r =
      ∑ x : ZMod N, section9FourierTerm B phi u r x := by
  simp only [fourier, ZMod.dft_apply, smul_eq_mul, section9FourierTerm,
    exponential]

private lemma section9_norm_power_expansion {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u r : ZMod N) :
    (((‖fourier (section9Phase B phi u) r‖ ^ (2 * k) : Real)) : Complex) =
      ∑ a : Fin k → ZMod N, ∑ b : Fin k → ZMod N,
        (∏ i, section9FourierTerm B phi u r (a i)) *
          star (∏ i, section9FourierTerm B phi u r (b i)) := by
  rw [ofReal_norm_even_pow, section9_fourier_eq]
  rw [Fintype.sum_pow]
  simp only [star_sum, Fintype.sum_pow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [star_prod]

private lemma section9_moment_eq_count {N k : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (section9Phase B phi u) r‖ ^ (2 * k)) =
      (N : Real) ^ 2 * phiAdditiveTupleCount k B phi := by
  classical
  have hcomplex :
      (((∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (section9Phase B phi u) r‖ ^ (2 * k) : Real)) : Complex) =
        (((N : Real) ^ 2 * countWhere
          (section9PairGood (k := k) B phi) : Real) : Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ u : ZMod N,
          (((∑ r : ZMod N,
            ‖fourier (section9Phase B phi u) r‖ ^ (2 * k) : Real)) : Complex)) =
          ∑ u : ZMod N, ∑ r : ZMod N,
            ∑ a : Fin k → ZMod N, ∑ b : Fin k → ZMod N,
              (∏ i, section9FourierTerm B phi u r (a i)) *
                star (∏ i, section9FourierTerm B phi u r (b i)) := by
                  apply Finset.sum_congr rfl
                  intro u _
                  rw [Complex.ofReal_sum]
                  apply Finset.sum_congr rfl
                  intro r _
                  exact section9_norm_power_expansion B phi u r
      _ = ∑ u : ZMod N, ∑ a : Fin k → ZMod N,
              ∑ r : ZMod N, ∑ b : Fin k → ZMod N,
                (∏ i, section9FourierTerm B phi u r (a i)) *
                  star (∏ i, section9FourierTerm B phi u r (b i)) := by
                    apply Finset.sum_congr rfl
                    intro u _
                    rw [Finset.sum_comm]
        _ = ∑ u : ZMod N, ∑ a : Fin k → ZMod N,
              ∑ b : Fin k → ZMod N, ∑ r : ZMod N,
                (∏ i, section9FourierTerm B phi u r (a i)) *
                  star (∏ i, section9FourierTerm B phi u r (b i)) := by
                    apply Finset.sum_congr rfl
                    intro u _
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.sum_comm]
        _ = ∑ a : Fin k → ZMod N, ∑ u : ZMod N,
              ∑ b : Fin k → ZMod N, ∑ r : ZMod N,
                (∏ i, section9FourierTerm B phi u r (a i)) *
                  star (∏ i, section9FourierTerm B phi u r (b i)) := by
                    rw [Finset.sum_comm]
        _ = ∑ a : Fin k → ZMod N, ∑ b : Fin k → ZMod N,
              ∑ u : ZMod N, ∑ r : ZMod N,
                (∏ i, section9FourierTerm B phi u r (a i)) *
                  star (∏ i, section9FourierTerm B phi u r (b i)) := by
                    apply Finset.sum_congr rfl
                    intro a _
                    rw [Finset.sum_comm]
        _ = ∑ a : Fin k → ZMod N, ∑ b : Fin k → ZMod N,
              if section9PairGood B phi (a, b) then (N : Complex) ^ 2 else 0 := by
                    apply Finset.sum_congr rfl
                    intro a _
                    apply Finset.sum_congr rfl
                    intro b _
                    exact section9_pair_orthogonality B phi a b
        _ = ∑ p : (Fin k → ZMod N) × (Fin k → ZMod N),
              if section9PairGood B phi p then (N : Complex) ^ 2 else 0 := by
                    rw [← Finset.sum_product']
                    simp only [Finset.univ_product_univ]
        _ = (((N : Real) ^ 2 * countWhere
            (section9PairGood (k := k) B phi) : Real) : Complex) := by
              rw [section9_sum_ite_const_eq_countWhere]
              push_cast
              simp only [nsmul_eq_mul]
              exact mul_comm _ _
  rw [section9_pair_count_eq B phi] at hcomplex
  exact Complex.ofReal_injective hcomplex

private lemma section9_phiTuple_two_eq {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    phiAdditiveTupleCount 2 B phi = phiAdditiveCount B phi := by
  classical
  unfold phiAdditiveTupleCount phiAdditiveCount
  apply countWhere_congr
  intro q
  simp only [IsPhiAdditive, IsAdditiveTuple, IsAdditiveQuadruple]
  rw [show (Finset.univ.filter (fun i : Fin 4 ↦ (i : Nat) < 2)) =
      {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 ↦ 2 ≤ (i : Nat))) =
      {2, 3} by decide]
  simp

private lemma section9_phase_norm_sq_sum {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (u : ZMod N) :
    (∑ x : ZMod N, ‖section9Phase B phi u x‖ ^ 2) = B.card := by
  classical
  calc
    (∑ x : ZMod N, ‖section9Phase B phi u x‖ ^ 2) =
        ∑ x : ZMod N, if x ∈ B then (1 : Real) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x ∈ B <;> simp [section9Phase, indicator, hx]
    _ = B.card := by
      rw [← Finset.sum_filter]
      simp

private lemma section9_second_moment_le {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (section9Phase B phi u) r‖ ^ 2) ≤ (N : Real) ^ 3 := by
  have hcardNat : B.card ≤ N := by
    simpa only [ZMod.card] using B.card_le_univ
  have hcard : (B.card : Real) ≤ N := by exact_mod_cast hcardNat
  calc
    (∑ u : ZMod N, ∑ r : ZMod N,
        ‖fourier (section9Phase B phi u) r‖ ^ 2) =
        ∑ _u : ZMod N, (N : Real) * B.card := by
          apply Finset.sum_congr rfl
          intro u _
          rw [identity_2_3_holds N (section9Phase B phi u),
            section9_phase_norm_sq_sum]
    _ = (N : Real) ^ 2 * B.card := by simp; ring
    _ ≤ (N : Real) ^ 2 * N :=
      mul_le_mul_of_nonneg_left hcard (sq_nonneg _)
    _ = (N : Real) ^ 3 := by ring

private lemma section9_interpolation {X : Type*} [Fintype X]
    (a : X → Real) :
    (∑ i, a i ^ 4) ≤
      (∑ i, a i ^ 2) ^ ((6 : Real) / 7) *
        (∑ i, a i ^ 16) ^ ((1 : Real) / 7) := by
  have h := Real.inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset X)) (p := (7 : Real)) (by norm_num)
    (fun i ↦ a i ^ 2) (fun i ↦ a i ^ 2)
    (fun i ↦ sq_nonneg (a i)) (fun i ↦ sq_nonneg (a i))
  have h4 : (∑ i, a i ^ 2 * a i ^ 2) = ∑ i, a i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h4] at h
  norm_num [Real.rpow_natCast] at h
  ring_nf at h
  exact h

private lemma section9_sum_pair {X Y M : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid M] (F : X × Y → M) :
    (∑ p : X × Y, F p) = ∑ x : X, ∑ y : Y, F (x, y) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

/-- Lemma 9.2 follows by interpolating the fourth Fourier moment between the
second and sixteenth moments of the character twists of the graph of `phi`.
The two character sums enforce, respectively, the additive relation and its
image under `phi`. -/
theorem lemma_9_2_holds : lemma_9_2 := by
  intro N _ B phi gamma hadd
  let moment : Nat → Real := fun e =>
    ∑ u : ZMod N, ∑ r : ZMod N,
      ‖fourier (section9Phase B phi u) r‖ ^ e
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmoment_nonneg (e : Nat) : 0 ≤ moment e := by
    dsimp only [moment]
    positivity
  have hsecond : moment 2 ≤ (N : Real) ^ 3 := by
    simpa only [moment] using section9_second_moment_le B phi
  have hfourth_eq :
      moment 4 = (N : Real) ^ 2 * phiAdditiveCount B phi := by
    calc
      moment 4 = (N : Real) ^ 2 * phiAdditiveTupleCount 2 B phi := by
        simpa only [moment] using section9_moment_eq_count (k := 2) B phi
      _ = (N : Real) ^ 2 * phiAdditiveCount B phi := by
        rw [section9_phiTuple_two_eq B phi]
  have hsixteenth_eq :
      moment 16 = (N : Real) ^ 2 * phiAdditiveTupleCount 8 B phi := by
    simpa only [moment] using section9_moment_eq_count (k := 8) B phi
  have hinterp : moment 4 ≤
      moment 2 ^ ((6 : Real) / 7) * moment 16 ^ ((1 : Real) / 7) := by
    let a : (ZMod N × ZMod N) → Real := fun p =>
      ‖fourier (section9Phase B phi p.1) p.2‖
    have h := section9_interpolation a
    simpa only [moment, a, section9_sum_pair] using h
  have hinterp_pow : moment 4 ^ 7 ≤ moment 2 ^ 6 * moment 16 := by
    have hpow := pow_le_pow_left₀ (hmoment_nonneg 4) hinterp 7
    calc
      moment 4 ^ 7 ≤
          (moment 2 ^ ((6 : Real) / 7) *
            moment 16 ^ ((1 : Real) / 7)) ^ 7 := hpow
      _ = moment 2 ^ 6 * moment 16 := by
        rw [mul_pow,
          ← Real.rpow_mul_natCast (hmoment_nonneg 2) ((6 : Real) / 7) 7,
          ← Real.rpow_mul_natCast (hmoment_nonneg 16) ((1 : Real) / 7) 7]
        norm_num [Real.rpow_natCast]
  by_cases hgamma : 0 ≤ gamma
  · have hfourth_lower : gamma * (N : Real) ^ 5 ≤ moment 4 := by
      rw [hfourth_eq]
      unfold GammaAdditive at hadd
      calc
        gamma * (N : Real) ^ 5 =
            (N : Real) ^ 2 * (gamma * (N : Real) ^ 3) := by ring
        _ ≤ (N : Real) ^ 2 * phiAdditiveCount B phi :=
          mul_le_mul_of_nonneg_left hadd (sq_nonneg _)
    have hfourth_lower_pow :
        (gamma * (N : Real) ^ 5) ^ 7 ≤ moment 4 ^ 7 :=
      pow_le_pow_left₀ (mul_nonneg hgamma (pow_nonneg hN.le 5))
        hfourth_lower 7
    have hsecond_pow : moment 2 ^ 6 ≤ ((N : Real) ^ 3) ^ 6 :=
      pow_le_pow_left₀ (hmoment_nonneg 2) hsecond 6
    have hsixteenth_nonneg : 0 ≤ moment 16 := hmoment_nonneg 16
    have hcombined :
        (gamma * (N : Real) ^ 5) ^ 7 ≤
          ((N : Real) ^ 3) ^ 6 * moment 16 := by
      calc
        (gamma * (N : Real) ^ 5) ^ 7 ≤ moment 4 ^ 7 := hfourth_lower_pow
        _ ≤ moment 2 ^ 6 * moment 16 := hinterp_pow
        _ ≤ ((N : Real) ^ 3) ^ 6 * moment 16 :=
          mul_le_mul_of_nonneg_right hsecond_pow hsixteenth_nonneg
    have hsimplified : gamma ^ 7 * (N : Real) ^ 17 ≤ moment 16 := by
      apply le_of_mul_le_mul_left _ (show 0 < (N : Real) ^ 18 by positivity)
      calc
        (N : Real) ^ 18 * (gamma ^ 7 * (N : Real) ^ 17) =
            (gamma * (N : Real) ^ 5) ^ 7 := by ring
        _ ≤ ((N : Real) ^ 3) ^ 6 * moment 16 := hcombined
        _ = (N : Real) ^ 18 * moment 16 := by ring
    apply le_of_mul_le_mul_left _ (show 0 < (N : Real) ^ 2 by positivity)
    calc
      (N : Real) ^ 2 * (gamma ^ 7 * (N : Real) ^ 15) =
          gamma ^ 7 * (N : Real) ^ 17 := by ring
      _ ≤ moment 16 := hsimplified
      _ = (N : Real) ^ 2 * phiAdditiveTupleCount 8 B phi := hsixteenth_eq
  · have hgamma' : gamma < 0 := lt_of_not_ge hgamma
    have : gamma ^ 7 ≤ 0 :=
      (show Odd 7 by decide).pow_nonpos hgamma'.le
    exact (mul_nonpos_of_nonpos_of_nonneg this (pow_nonneg hN.le 15)).trans
      (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
