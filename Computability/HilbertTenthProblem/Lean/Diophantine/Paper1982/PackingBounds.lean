import Diophantine.Paper1982.Master3

/-!
# Jones 1982, §4: bounds for the three packed carry tests

The equations (U3)–(U8), with (U6') replacing (U6), already imply the six strict
block bounds used in (U18)–(U22). No carry condition is needed for these estimates.
In particular this allows the packed test to be decoded in the sufficiency direction
of Theorem 2 without assuming the three tests that it is intended to recover.
-/

namespace Jones1982

open Polynomial Finset

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- The bounds `Sᵢ < Nᵢ` and `Tᵢ < Nᵢ` for (U18)–(U22), derived from the
common equations alone. The lower bound for the signed third block is
`UEqs.S3_nonneg`. A base of at least two suffices; a power-of-two hypothesis is
only needed later to split the carry test. -/
theorem UEqs.packing_bounds (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x)
    {b e g l m q t θ lam α : ℕ} (hb2 : 2 ≤ b)
    (hg0 : 0 < g) (hl0 : 0 < l) (hm : 0 < m) (ht : 0 < t) (hα : 0 < α)
    (hU : UEqs ν x z u y b e g l m q t θ lam α) :
    g < q ^ 3 ∧ q ^ 3 - 1 - (b - 1) * l < q ^ 3 ∧
      e + l * q ^ 2 < q ^ 4 ∧ θ * lam < q ^ 4 ∧
      (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
        b ^ 5 * lam * (1 + q ^ 4)).toNat < q ^ 9 ∧ (b ^ 5 - 2) * q < q ^ 9 := by
  obtain ⟨_, _, heq, hlq, hgq, _, _, _, hlamE⟩ :=
    hU.sizes hI hx hb2 hg0 hl0 hm ht hα
  have hq : q = (b ^ 5) ^ L4 ν := by rw [hU.U3, q_eq]
  have hL1 : 1 ≤ L4 ν := Nat.one_le_pow _ _ (by norm_num)
  have hbB : b ≤ b ^ 5 := Nat.le_self_pow (by norm_num) b
  have hBq : b ^ 5 ≤ q := by
    rw [hq]
    exact Nat.le_self_pow (by omega) _
  have hq32 : 32 ≤ q := by
    have := Nat.pow_le_pow_left hb2 5
    norm_num at this
    omega
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hq4 : 0 < q ^ 4 := by positivity
  have hq9 : 0 < q ^ 9 := by positivity
  have h1 : g < q ^ 3 := hgq.trans_le (Nat.le_self_pow (by norm_num) q)
  have h1' : q ^ 3 - 1 - (b - 1) * l < q ^ 3 := by
    have : 0 < q ^ 3 := by positivity
    omega
  have h2 : e + l * q ^ 2 < q ^ 4 := by
    calc e + l * q ^ 2 < q ^ 2 + l * q ^ 2 := Nat.add_lt_add_right heq _
      _ = (l + 1) * q ^ 2 := by ring
      _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = q ^ 4 := by ring
  have hz := hI.two_le
  have hθ : θ + 1 ≤ b ^ 5 := by have := hU.U5; omega
  have h2' : θ * lam < q ^ 4 := by
    have := Nat.mul_le_mul_right lam hθ
    have := hU.U4
    nlinarith
  -- The geometric series includes its `2L`-th term, so `e < q² ≤ λ ≤ zλ`.
  have hq2lam : q ^ 2 ≤ lam := by
    rw [hlamE, hq, ← pow_mul, mul_comm (L4 ν) 2]
    exact Finset.single_le_sum (f := fun i => (b ^ 5) ^ i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (by omega : 2 * L4 ν < 4 * L4 ν))
  have hezlam : e ≤ z * lam :=
    heq.le.trans (hq2lam.trans (Nat.le_mul_of_pos_left _ (by omega)))
  -- (U4) gives `λ ≤ q⁴` and `Bλ ≤ 2q⁴`.
  have hlam : lam ≤ q ^ 4 := by
    have hB2 : 2 ≤ b ^ 5 := hb2.trans hbB
    have := Nat.mul_le_mul_left lam hB2
    have := hU.U4
    nlinarith
  have hBlam : b ^ 5 * lam ≤ 2 * q ^ 4 := by
    have := hU.U4
    nlinarith
  have h3 : (2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 +
      b ^ 5 * lam * (1 + q ^ 4)).toNat < q ^ 9 := by
    apply (Int.toNat_lt_of_ne_zero hq9.ne').2
    push_cast
    have heZ : (e : ℤ) ≤ (z : ℤ) * lam := by exact_mod_cast hezlam
    have hBlamZ : (b : ℤ) ^ 5 * lam ≤ 2 * (q : ℤ) ^ 4 := by exact_mod_cast hBlam
    have hq4Z : (1 : ℤ) ≤ (q : ℤ) ^ 4 := by exact_mod_cast hq4
    have hterm : 2 * ((e : ℤ) - z * lam) * (1 + x * b ^ 5 + g) ^ 4 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hmask : (b : ℤ) ^ 5 * lam * (1 + q ^ 4) ≤ 4 * (q : ℤ) ^ 8 := by
      calc (b : ℤ) ^ 5 * lam * (1 + q ^ 4)
          ≤ (2 * (q : ℤ) ^ 4) * (2 * (q : ℤ) ^ 4) :=
            mul_le_mul hBlamZ (by linarith) (by positivity) (by positivity)
        _ = 4 * (q : ℤ) ^ 8 := by ring
    have hq32Z : (32 : ℤ) ≤ q := by exact_mod_cast hq32
    have hlarge : 4 * (q : ℤ) ^ 8 < (q : ℤ) ^ 9 := by
      calc 4 * (q : ℤ) ^ 8 < (q : ℤ) * q ^ 8 :=
          mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = (q : ℤ) ^ 9 := by ring
    linarith
  have h3' : (b ^ 5 - 2) * q < q ^ 9 := by
    have hsub : b ^ 5 - 2 < q := by omega
    calc (b ^ 5 - 2) * q < q * q := Nat.mul_lt_mul_of_pos_right hsub hq0
      _ = q ^ 2 := by ring
      _ ≤ q ^ 9 := Nat.pow_le_pow_right hq1 (by norm_num)
  exact ⟨h1, h1', h2, h2', h3, h3'⟩

end Jones1982
