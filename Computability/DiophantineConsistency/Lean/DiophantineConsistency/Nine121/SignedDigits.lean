import DiophantineConsistency.ModelDigitTransfer
import DiophantineConsistency.ModelArithmetic

/-! # Signed radix digits and the target-digit test, in every model of `𝗜𝚺₁`

A nonnegative model natural `X` with a signed expansion `ι X = Σ_{e<n} d_e Bᵉ`
(standard length `n`, coefficients in the ring of differences with
`2|d_e| + 2 ≤ B`) has genuine radix-`B` digits `u_e < B` obtained by borrow
propagation: `ι u_e = d_e + δ_e + ε_e B` with a borrow `δ_e ∈ {0, −1}` and
`ε_e ∈ {0, 1}` (`signed_digits`). The final borrow vanishes because `X ≥ 0`.

At a target position the signed coefficient is `2c + 1`; there the digit is
`0` or `1` iff `c = 0` (`target_digit`), whatever the borrow. With
`B = 2^v` and the mask digit `B − 2` (Lemma 2.7, `lt_exp_iff_noCarry`) this is
the high-block carry test of the nine-variable prefixes (`high_noCarry_iff`):

  `NoCarry X (Σ_{e<n, e target} (B − 2) Bᵉ) ↔ ∀ target e < n, c_e = 0`,

for `ι X = Σ_{e<n} (2c_e + [e target]) Bᵉ` with `4|c_e| + 4 ≤ B`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Nine121.SignedDigits
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ModelDifferenceRing ModelDigitTransfer ModelCarries ArithmeticBinaryCarry ModelArithmetic ArithmeticWindowDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The digit relation produced by borrow propagation. -/
def DigitRel (B : V) (u : V) (d : DiffRing V) : Prop :=
  ∃ δ ε : DiffRing V, (δ = 0 ∨ δ = -1) ∧ (ε = 0 ∨ ε = 1) ∧ ι u = d + δ + ε * ι B

private theorem prefix_digits (B : V) (n : ℕ) (d : ℕ → DiffRing V)
    (hd : ∀ e < n, 2 * |d e| + 2 ≤ ι B) :
    ∃ u : ℕ → V, ∃ β : DiffRing V, (β = 0 ∨ β = -1) ∧ (∀ e < n, u e < B) ∧
      ι (dsum B u n) = (∑ e ∈ Finset.range n, d e * ι B ^ e) - β * ι B ^ n ∧
      ∀ e < n, DigitRel B (u e) (d e) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, 0, Or.inl rfl, fun e he => absurd he (Nat.not_lt_zero e), ?_,
      fun e he => absurd he (Nat.not_lt_zero e)⟩
    simp [dsum_zero]
  | succ n ih =>
    obtain ⟨u, β, hβ, hu, hsum, hrel⟩ := ih (fun e he => hd e (Nat.lt_succ_of_lt he))
    have hdn := hd n (Nat.lt_succ_self n)
    have habs := abs_nonneg (d n)
    have hle := le_abs_self (d n)
    have hge := neg_abs_le (d n)
    have hB0 : (0 : DiffRing V) ≤ ι B := ι_nonneg B
    -- the next digit
    obtain ⟨v, ε, hε, hv, hvrel⟩ : ∃ v : V, ∃ ε : DiffRing V, (ε = 0 ∨ ε = 1) ∧ v < B ∧
        ι v = d n + β + ε * ι B := by
      rcases le_or_gt 0 (d n + β) with h | h
      · obtain ⟨v, hv⟩ := nonneg_iff.mp h
        refine ⟨v, 0, Or.inl rfl, ?_, by rw [← hv]; ring⟩
        apply (ι_lt_ι (V := V)).mp
        rw [← hv]
        rcases hβ with hβ | hβ <;> rw [hβ] <;> linarith
      · have h' : (0 : DiffRing V) ≤ d n + β + ι B := by
          rcases hβ with hβ | hβ <;> rw [hβ] <;> linarith
        obtain ⟨v, hv⟩ := nonneg_iff.mp h'
        refine ⟨v, 1, Or.inr rfl, ?_, by rw [← hv]; ring⟩
        apply (ι_lt_ι (V := V)).mp
        rw [← hv]
        linarith
    let u' : ℕ → V := fun e => if e = n then v else u e
    have hu'n : u' n = v := if_pos rfl
    have hu'e : ∀ e < n, u' e = u e := fun e he => if_neg (Nat.ne_of_lt he)
    refine ⟨u', -ε, ?_, ?_, ?_, ?_⟩
    · rcases hε with h | h <;> rw [h] <;> simp
    · intro e he
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with h | h
      · rw [hu'e e h]; exact hu e h
      · rw [h, hu'n]; exact hv
    · rw [dsum_succ, dsum_congr B n hu'e, hu'n, map_add, map_mul, map_pow, hsum, hvrel,
        Finset.sum_range_succ]
      ring
    · intro e he
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with h | h
      · rw [hu'e e h]; exact hrel e h
      · rw [h, hu'n]; exact ⟨β, ε, hβ, hε, hvrel⟩

/-- **Signed digits.** -/
theorem signed_digits (B : V) (hB : 1 ≤ B) (n : ℕ) (d : ℕ → DiffRing V)
    (hd : ∀ e < n, 2 * |d e| + 2 ≤ ι B) (X : V)
    (hX : ι X = ∑ e ∈ Finset.range n, d e * ι B ^ e) :
    ∃ u : ℕ → V, (∀ e < n, u e < B) ∧ X = dsum B u n ∧ ∀ e < n, DigitRel B (u e) (d e) := by
  obtain ⟨u, β, hβ, hu, hsum, hrel⟩ := prefix_digits B n d hd
  refine ⟨u, hu, ?_, hrel⟩
  rcases hβ with hβ | hβ
  · apply ι_injective
    rw [hsum, hβ, hX]; ring
  · exfalso
    have hlt : dsum B u n < B ^ n := dsum_lt B u n hu
    have h1 : ι (dsum B u n) < ι B ^ n := by
      rw [← map_pow]; exact (ι_lt_ι (V := V)).mpr hlt
    rw [hsum, hβ, ← hX] at h1
    have := ι_nonneg X
    linarith

private theorem eq_zero_of_two_mul {c : DiffRing V} (h1 : -1 ≤ 2 * c) (h2 : 2 * c ≤ 1) : c = 0 := by
  rcases lt_trichotomy c 0 with h | h | h
  · have : (1 : DiffRing V) ≤ -c := model_discrete (-c) (by linarith)
    linarith
  · exact h
  · have : (1 : DiffRing V) ≤ c := model_discrete c h
    linarith

/-- **The target digit.** At a coefficient `2c + 1` with `4|c| + 4 ≤ B` the
propagated digit is below two iff `c = 0`. -/
theorem target_digit {B u : V} (hu : u < B) {c : DiffRing V} (hc : 4 * |c| + 4 ≤ ι B)
    (hrel : DigitRel B u (2 * c + 1)) : u < 2 ↔ c = 0 := by
  obtain ⟨δ, ε, hδ, hε, he⟩ := hrel
  have hu0 := ι_nonneg u
  have huB : ι u < ι B := (ι_lt_ι (V := V)).mpr hu
  have habs := abs_nonneg c
  have hle := le_abs_self c
  have hge := neg_abs_le c
  have hu2 : u < 2 ↔ ι u ≤ 1 := by
    constructor
    · intro h
      have h' : ι u < ι (2 : V) := (ι_lt_ι (V := V)).mpr h
      rw [map_ofNat] at h'
      have := model_discrete (2 - ι u) (by linarith)
      linarith
    · intro h
      apply (ι_lt_ι (V := V)).mp
      rw [map_ofNat]; linarith
  rw [hu2]
  constructor
  · intro h1
    rcases hε with hε | hε <;> rcases hδ with hδ | hδ <;> rw [hε, hδ] at he
    · exact eq_zero_of_two_mul (by linarith) (by linarith)
    · exact eq_zero_of_two_mul (by linarith) (by linarith)
    · exfalso; linarith
    · exfalso; linarith
  · intro h0
    rw [h0] at he
    rcases hε with hε | hε <;> rcases hδ with hδ | hδ <;> rw [hε, hδ] at he
    · linarith
    · linarith
    · exfalso; linarith
    · exfalso; linarith

/-- **The high-block carry test.** -/
theorem high_noCarry_iff (v : V) (hv : 1 ≤ v) (n : ℕ) (tgt : ℕ → Prop) [DecidablePred tgt]
    (c : ℕ → DiffRing V) (hc : ∀ e < n, 4 * |c e| + 4 ≤ ι (Exp.exp v)) (X : V)
    (hX : ι X = ∑ e ∈ Finset.range n, (2 * c e + if tgt e then 1 else 0) * ι (Exp.exp v) ^ e) :
    NoCarry X (dsum (Exp.exp v) (fun e => if tgt e then Exp.exp v - 2 else 0) n) ↔
      ∀ e < n, tgt e → c e = 0 := by
  have hB1 : 1 ≤ Exp.exp v := one_le_exp v
  have hd : ∀ e < n, 2 * |2 * c e + if tgt e then 1 else 0| + 2 ≤ ι (Exp.exp v) := by
    intro e he
    have h := hc e he
    have h1 : |2 * c e + if tgt e then 1 else 0| ≤ 2 * |c e| + 1 := by
      calc |2 * c e + if tgt e then 1 else 0| ≤ |2 * c e| + |if tgt e then (1 : DiffRing V) else 0| :=
            abs_add_le _ _
        _ ≤ 2 * |c e| + 1 := by
            rw [abs_mul, abs_two]
            split_ifs <;> simp
    linarith
  obtain ⟨u, hu, hXu, hrel⟩ := signed_digits (Exp.exp v) hB1 n _ hd X hX
  have hm : ∀ e < n, (fun e => if tgt e then Exp.exp v - 2 else (0 : V)) e < Exp.exp v := by
    intro e _
    dsimp only
    split_ifs
    · exact tsub_lt_self (exp_pos v) (by norm_num)
    · exact exp_pos v
  rw [hXu, noCarry_dsum_iff v u _ n hu hm]
  have h2 : Exp.exp v - 2 = Exp.exp v - Exp.exp (1 : V) := by
    have e1 : Exp.exp (1 : V) = 2 := by
      have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
    rw [e1]
  constructor
  · intro h e he ht
    have hn := h e he
    simp only [if_pos ht] at hn
    rw [h2] at hn
    have hlt : u e < Exp.exp 1 := (lt_exp_iff_noCarry hv (hu e he)).mpr ((noCarry_comm _ _).mp hn)
    have e1 : Exp.exp (1 : V) = 2 := by
      have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
    rw [e1] at hlt
    have hr := hrel e he
    simp only [if_pos ht] at hr
    exact (target_digit (hu e he) (hc e he) hr).mp hlt
  · intro h e he
    by_cases ht : tgt e
    · simp only [if_pos ht]
      rw [h2]
      apply (noCarry_comm _ _).mp
      apply (lt_exp_iff_noCarry hv (hu e he)).mp
      have e1 : Exp.exp (1 : V) = 2 := by
        have := exp_succ (0 : V); rw [zero_add, exp_zero, mul_one] at this; exact this
      rw [e1]
      have hr := hrel e he
      simp only [if_pos ht] at hr
      exact (target_digit (hu e he) (hc e he) hr).mpr (h e he ht)
    · simp only [if_neg ht]
      exact noCarry_zero_right _

end Nine121.SignedDigits

#print axioms Nine121.SignedDigits.signed_digits
#print axioms Nine121.SignedDigits.target_digit
#print axioms Nine121.SignedDigits.high_noCarry_iff
