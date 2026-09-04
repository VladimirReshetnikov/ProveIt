import FabiusFunction.PeriodDoublingHankel
import FabiusFunction.ThueMorseNewman

/-!
# Hankel determinants of the Thue–Morse sequence never vanish

The atlas's `thm:hankel-nonzero` (Allouche–Peyrière–Wen–Wen),
previously a literature citation: **every Hankel determinant of the
signed Thue–Morse sequence is nonzero** — indeed

`H_r(ε) = 2^(r-1) · (odd)`.

The proof is a two-adic valuation argument.  Parity-interleaving the
rows and columns of `H_{2n}` (resp. `H_{2n+1}`) and eliminating with
one unitriangular block certificate exposes the factorization

`H_{2n}(ε) = 2^n · H_n(ε) · H_n(m)`,
`H_{2n+1}(ε) = 2^n · H_{n+1}(ε) · H_n(m)`,

where `m(k) = (ε(k+1) - ε(k))/2 = τ(k) - τ(k+1)` is the difference
sequence.  Its Hankel determinants are **odd**: reduced mod `2` the
matrix becomes the period-doubling Hankel matrix, whose determinant
is `1` by `PeriodDoublingHankel`.  Strong induction then gives the
exact two-adic valuation `v₂(H_r) = r - 1`, so `H_r ≠ 0`.

* `mseq` — the integer difference sequence.
* `thueMorseSign_two_mul_add_two_mul` and its three companions — the
  doubling laws `ε(2h) = ε(h)`, `ε(2h+1) = -ε(h)` in the four
  parity-interleaved shapes `ε(2i + 2j)`, `ε(2i + (2j+1))`,
  `ε(2i+1 + 2j)`, `ε(2i+1 + (2j+1))`.
* `hankelSign_submatrix_eq_fromBlocks` — parity-interleaving the
  sign Hankel matrix exposes the block form `[H, -H; -H, H⁺]`, for
  any even/odd interleaving of the index set.
* `hankelSign_det_two_mul` / `hankelSign_det_two_mul_add_one` — the
  two doubling factorizations.
* `mseqHankel_det_odd` — the mod-two transfer.
* `hankelSign_det_eq_two_pow_mul_odd` — **the exact valuation**.
* `thueMorseHankel_ne_zero` — **the APWW theorem**
  (`eq:hankel-nonzero`).
-/

set_option autoImplicit false

open Finset Matrix

namespace Fabius

/-- The Hankel matrix of the signed Thue–Morse sequence. -/
def hankelSign (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => thueMorseSign ((i : ℕ) + j)

/-- The integer difference sequence `m(k) = τ(k) - τ(k+1)`, half the
increment of the signs. -/
def mseq (k : ℕ) : ℤ :=
  (thueMorseBit k : ℤ) - (thueMorseBit (k + 1) : ℤ)

/-- The Hankel matrix of the difference sequence. -/
def mseqHankel (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  of fun i j => mseq ((i : ℕ) + j)

/-- `2·m(k) = ε(k+1) - ε(k)`. -/
theorem two_mul_mseq (k : ℕ) :
    2 * mseq k = thueMorseSign (k + 1) - thueMorseSign k := by
  have h1 := thueMorseSign_eq_one_sub_two_mul_bit k
  have h2 := thueMorseSign_eq_one_sub_two_mul_bit (k + 1)
  rw [mseq]
  omega

/-- Reduced mod two, the difference sequence is the period-doubling
bit. -/
theorem mseq_cast (k : ℕ) : ((mseq k : ℤ) : ZMod 2) = pdBit k := by
  rw [mseq, pdBit]
  push_cast
  rw [zmod_two_sub_eq_add]

/-! ### The doubling laws in parity-interleaved shape

Interleaving even and odd indices produces Hankel entries at the four
sums `2i + 2j`, `2i + (2j+1)`, `2i+1 + 2j`, `2i+1 + (2j+1)`; the
doubling laws `ε(2h) = ε(h)` and `ε(2h+1) = -ε(h)` evaluate each. -/

/-- `ε(2i + 2j) = ε(i + j)`: an even-even entry is a sign entry. -/
theorem thueMorseSign_two_mul_add_two_mul (i j : ℕ) :
    thueMorseSign (2 * i + 2 * j) = thueMorseSign (i + j) := by
  rw [show 2 * i + 2 * j = 2 * (i + j) by ring, thueMorseSign_two_mul]

/-- `ε(2i + (2j+1)) = -ε(i + j)`: an even-odd entry is a negated sign
entry. -/
theorem thueMorseSign_two_mul_add_two_mul_add_one (i j : ℕ) :
    thueMorseSign (2 * i + (2 * j + 1)) = -thueMorseSign (i + j) := by
  rw [show 2 * i + (2 * j + 1) = 2 * (i + j) + 1 by ring,
    thueMorseSign_two_mul_add_one]

/-- `ε(2i+1 + 2j) = -ε(i + j)`: an odd-even entry is a negated sign
entry. -/
theorem thueMorseSign_two_mul_add_one_add_two_mul (i j : ℕ) :
    thueMorseSign (2 * i + 1 + 2 * j) = -thueMorseSign (i + j) := by
  rw [show 2 * i + 1 + 2 * j = 2 * (i + j) + 1 by ring,
    thueMorseSign_two_mul_add_one]

/-- `ε(2i+1 + (2j+1)) = ε(i + j + 1)`: an odd-odd entry is a shifted
sign entry. -/
theorem thueMorseSign_two_mul_add_one_add_two_mul_add_one (i j : ℕ) :
    thueMorseSign (2 * i + 1 + (2 * j + 1)) =
      thueMorseSign (i + j + 1) := by
  rw [show 2 * i + 1 + (2 * j + 1) = 2 * (i + j + 1) by ring,
    thueMorseSign_two_mul]

/-- **Parity interleaving exposes the block structure.**  For any
even/odd interleaving `e` of the index set — `e (inl i) = 2i` on the
left summand and `e (inr j) = 2j + 1` on the right — the interleaved
sign Hankel matrix is the block matrix

`[H_p(ε), -H; -H, H⁺]`, with `H(i,j) = ε(i+j)`, `H⁺(i,j) = ε(i+j+1)`,

by the four interleaved doubling laws.  Both doubling factorizations
below are this one lemma at `interleaveEquiv` and `interleaveOddEquiv`
respectively. -/
theorem hankelSign_submatrix_eq_fromBlocks {p q N : ℕ}
    (e : Fin p ⊕ Fin q ≃ Fin N)
    (hl : ∀ i : Fin p, ((e (Sum.inl i)) : ℕ) = 2 * i)
    (hr : ∀ j : Fin q, ((e (Sum.inr j)) : ℕ) = 2 * j + 1) :
    (hankelSign N).submatrix e e =
      fromBlocks (hankelSign p)
        (of fun (i : Fin p) (j : Fin q) => -thueMorseSign ((i : ℕ) + j))
        (of fun (i : Fin q) (j : Fin p) => -thueMorseSign ((i : ℕ) + j))
        (of fun i j : Fin q => thueMorseSign ((i : ℕ) + j + 1)) := by
  refine Matrix.ext ?_
  rintro (i | i) (j | j) <;>
    simp only [submatrix_apply, hankelSign, of_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, hl, hr]
  · exact thueMorseSign_two_mul_add_two_mul _ _
  · exact thueMorseSign_two_mul_add_two_mul_add_one _ _
  · exact thueMorseSign_two_mul_add_one_add_two_mul _ _
  · exact thueMorseSign_two_mul_add_one_add_two_mul_add_one _ _

/-- **The even doubling factorization**:
`H_{2n}(ε) = 2^n · H_n(ε) · H_n(m)`. -/
theorem hankelSign_det_two_mul (n : ℕ) :
    (hankelSign (2 * n)).det =
      2 ^ n * ((hankelSign n).det * (mseqHankel n).det) := by
  rw [← det_submatrix_equiv_self (interleaveEquiv n) (hankelSign (2 * n))]
  have hform : (hankelSign (2 * n)).submatrix (interleaveEquiv n)
      (interleaveEquiv n) =
      fromBlocks (hankelSign n)
        (of fun i j : Fin n => -thueMorseSign ((i : ℕ) + j))
        (of fun i j : Fin n => -thueMorseSign ((i : ℕ) + j))
        (of fun i j : Fin n => thueMorseSign ((i : ℕ) + j + 1)) :=
    hankelSign_submatrix_eq_fromBlocks (interleaveEquiv n)
      (interleaveEquiv_inl n) (interleaveEquiv_inr n)
  have hC : (of fun i j : Fin n => -thueMorseSign ((i : ℕ) + j)) =
      (-1 : Matrix (Fin n) (Fin n) ℤ) * hankelSign n := by
    refine Matrix.ext fun i j => ?_
    rw [neg_one_mul, Matrix.neg_apply]
    rfl
  rw [hform, det_fromBlocks_of_eq_mul _ _ _ _ _ hC]
  have hmat : (of fun i j : Fin n => thueMorseSign ((i : ℕ) + j + 1)) -
      (-1 : Matrix (Fin n) (Fin n) ℤ) *
        (of fun i j : Fin n => -thueMorseSign ((i : ℕ) + j)) =
      (2 : ℤ) • mseqHankel n := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.sub_apply, neg_one_mul, Matrix.neg_apply,
      Matrix.smul_apply]
    simp only [of_apply, mseqHankel]
    rw [smul_eq_mul, two_mul_mseq]
    ring
  rw [hmat, det_smul, Fintype.card_fin]
  ring

/-- **The odd doubling factorization**:
`H_{2n+1}(ε) = 2^n · H_{n+1}(ε) · H_n(m)`. -/
theorem hankelSign_det_two_mul_add_one (n : ℕ) :
    (hankelSign (2 * n + 1)).det =
      2 ^ n * ((hankelSign (n + 1)).det * (mseqHankel n).det) := by
  rw [← det_submatrix_equiv_self (interleaveOddEquiv n)
    (hankelSign (2 * n + 1))]
  have hform : (hankelSign (2 * n + 1)).submatrix (interleaveOddEquiv n)
      (interleaveOddEquiv n) =
      fromBlocks (hankelSign (n + 1))
        (of fun (i : Fin (n + 1)) (j : Fin n) =>
          -thueMorseSign ((i : ℕ) + j))
        (of fun (i : Fin n) (j : Fin (n + 1)) =>
          -thueMorseSign ((i : ℕ) + j))
        (of fun i j : Fin n => thueMorseSign ((i : ℕ) + j + 1)) :=
    hankelSign_submatrix_eq_fromBlocks (interleaveOddEquiv n)
      (interleaveOddEquiv_inl n) (interleaveOddEquiv_inr n)
  have hC : (of fun (i : Fin n) (j : Fin (n + 1)) =>
      -thueMorseSign ((i : ℕ) + j)) =
      (-(of fun (i : Fin n) (k : Fin (n + 1)) =>
        if k = Fin.castSucc i then (1 : ℤ) else 0)) *
        hankelSign (n + 1) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_apply]
    simp only [of_apply, hankelSign]
    rw [Finset.sum_eq_single (Fin.castSucc i)]
    · rw [if_pos rfl, one_mul, Fin.val_castSucc]
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hform, det_fromBlocks_of_eq_mul _ _ _ _ _ hC]
  have hmat : (of fun i j : Fin n => thueMorseSign ((i : ℕ) + j + 1)) -
      (-(of fun (i : Fin n) (k : Fin (n + 1)) =>
        if k = Fin.castSucc i then (1 : ℤ) else 0)) *
        (of fun (i : Fin (n + 1)) (j : Fin n) =>
          -thueMorseSign ((i : ℕ) + j)) =
      (2 : ℤ) • mseqHankel n := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.sub_apply, Matrix.neg_mul, Matrix.neg_apply,
      Matrix.mul_apply, Matrix.smul_apply]
    simp only [of_apply, mseqHankel]
    rw [Finset.sum_eq_single (Fin.castSucc i)]
    · rw [if_pos rfl, one_mul, Fin.val_castSucc, smul_eq_mul,
        two_mul_mseq]
      ring
    · intro b _ hb
      rw [if_neg hb, zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hmat, det_smul, Fintype.card_fin]
  ring

/-- **The difference-sequence Hankel determinants are odd**: mod two
they become the period-doubling determinants, which are all `1`. -/
theorem mseqHankel_det_odd (n : ℕ) : ¬(2 : ℤ) ∣ (mseqHankel n).det := by
  intro hdvd
  have hmap : ((Int.castRingHom (ZMod 2)) (mseqHankel n).det) =
      (pdHankel n).det := by
    rw [RingHom.map_det (Int.castRingHom (ZMod 2))]
    congr 1
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    simp only [mseqHankel, of_apply, pdHankel]
    exact mseq_cast _
  have hcast : ((Int.castRingHom (ZMod 2)) (mseqHankel n).det) = 0 := by
    show (((mseqHankel n).det : ℤ) : ZMod 2) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  rw [hmap, (pdHankel_det_eq_one n).1] at hcast
  exact one_ne_zero hcast

/-- **The exact two-adic valuation**: `H_r(ε) = 2^(r-1)·(odd)` for
`r ≥ 1`. -/
theorem hankelSign_det_eq_two_pow_mul_odd :
    ∀ r : ℕ, 1 ≤ r →
      ∃ u : ℤ, ¬(2 : ℤ) ∣ u ∧ (hankelSign r).det = 2 ^ (r - 1) * u := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr
    match r, hr with
    | 1, _ =>
        refine ⟨1, by norm_num, ?_⟩
        rw [det_fin_one]
        show thueMorseSign ((0 : ℕ) + 0) = 2 ^ (1 - 1) * 1
        norm_num [thueMorseSign, binaryWeight]
    | (m + 2), _ =>
        have hprime : Prime (2 : ℤ) := Int.prime_two
        rcases Nat.even_or_odd (m + 2) with ⟨t, ht⟩ | ⟨t, ht⟩
        · have ht' : m + 2 = 2 * t := by omega
          have ht1 : 1 ≤ t := by omega
          have htlt : t < m + 2 := by omega
          obtain ⟨u, hu, hval⟩ := ih t htlt ht1
          refine ⟨u * (mseqHankel t).det, ?_, ?_⟩
          · intro hdvd
            rcases (hprime.dvd_mul).mp hdvd with h | h
            · exact hu h
            · exact mseqHankel_det_odd t h
          · rw [ht', hankelSign_det_two_mul, hval,
              show 2 * t - 1 = t + (t - 1) by omega, pow_add]
            ring
        · have ht' : m + 2 = 2 * t + 1 := by omega
          have ht1 : 1 ≤ t := by omega
          have ht1lt : t + 1 < m + 2 := by omega
          obtain ⟨u, hu, hval⟩ := ih (t + 1) ht1lt (by omega)
          refine ⟨u * (mseqHankel t).det, ?_, ?_⟩
          · intro hdvd
            rcases (hprime.dvd_mul).mp hdvd with h | h
            · exact hu h
            · exact mseqHankel_det_odd t h
          · rw [ht', hankelSign_det_two_mul_add_one, hval,
              show 2 * t + 1 - 1 = t + (t + 1 - 1) by omega, pow_add]
            ring

/-- **The Allouche–Peyrière–Wen–Wen theorem** (`eq:hankel-nonzero`):
every Hankel determinant of the signed Thue–Morse sequence is
nonzero. -/
theorem thueMorseHankel_ne_zero (r : ℕ) (hr : 1 ≤ r) :
    (hankelSign r).det ≠ 0 := by
  obtain ⟨u, hu, hval⟩ := hankelSign_det_eq_two_pow_mul_odd r hr
  rw [hval]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) fun hu0 => ?_
  exact hu (hu0 ▸ dvd_zero 2)

end Fabius
