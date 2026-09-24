import Diophantine.Paper1982.ShortBase
import Diophantine.Paper1982.Master2

/-!
# Digit transfer with the shorter mask in Jones 1982, §5

Lemma 2.9 is used with `n = m = k = L`, where `L = 5^(ν+1)`.
Its bound `V < 2z B^L` retains the permitted top digit of `epoly`.
The packed condition splits at `Q = B^L`; the shorter mask below `Q`
is sufficient for both transferred polynomials.
-/

namespace Jones1982

open Polynomial Finset

/-- Lemma 2.9 with the exact shorter cutoff, including a possible digit at `L`. -/
theorem short_transfer_poly_iff {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {z u y B β : ℕ} (hI : Index ν P z u y) (hB : B = 2 ^ β)
    (hbig : 2 * (2 * z) ^ (L4 ν + 1) ≤ B)
    (p : ℤ[X]) (hp0 : ∀ i, 0 ≤ p.coeff i) (hp1 : ∀ i, p.coeff i < 2 * z)
    (hdeg : p.natDegree ≤ L4 ν) {v V : ℕ} (hv : (v : ℤ) = p.eval (2 * z : ℤ)) :
    (V : ℤ) = p.eval (B : ℤ) ↔
      V ≡ v [MOD B - 2 * z] ∧ V < 2 * z * B ^ L4 ν ∧
        τ 2 V (mask29 B (2 * z) (L4 ν)) = 0 := by
  obtain ⟨s, hs⟩ := hI.pow2
  have hz := hI.two_le
  have h2z : 2 * z = 2 ^ (s + 1) := by rw [hs, pow_succ]; ring
  have hpow : 2 * z ≤ (2 * z) ^ (L4 ν + 1) := Nat.le_self_pow (by omega) _
  have h2zB : 2 * z ≤ B := by omega
  have hst : s + 1 ≤ β := by
    have : 2 ^ (s + 1) ≤ 2 ^ β := by rw [← h2z, ← hB]; exact h2zB
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hbig' := hbig
  rw [h2z, hB] at hbig'
  let ys := coeffList p (L4 ν + 1)
  have hysz : ∀ x ∈ ys, x < 2 ^ (s + 1) := by
    intro x hx
    dsimp [ys] at hx
    obtain ⟨i, _, rfl⟩ := mem_coeffList hx
    rw [← h2z, Int.toNat_lt (hp0 i)]
    push_cast
    exact hp1 i
  have hlen : ys.length ≤ L4 ν + 1 := by dsimp [ys]; rw [coeffList_length]
  have hvy : v = Nat.ofDigits (2 ^ (s + 1)) ys := by
    have heval := ofDigits_coeffList_eq_eval p hp0 (2 * z) (n := L4 ν + 1) (by omega)
    have heq : ((Nat.ofDigits (2 * z) ys : ℕ) : ℤ) = v := by
      dsimp [ys]
      rw [heval, hv]
      push_cast
      rfl
    have heq' : v = Nat.ofDigits (2 * z) ys := by exact_mod_cast heq.symm
    rwa [h2z] at heq'
  have hVB : (V : ℤ) = p.eval (B : ℤ) ↔ V = Nat.ofDigits (2 ^ β) ys := by
    have heval := ofDigits_coeffList_eq_eval p hp0 B (n := L4 ν + 1) (by omega)
    change ((Nat.ofDigits B ys : ℕ) : ℤ) = p.eval (B : ℤ) at heval
    rw [← hB]
    constructor
    · intro h
      have heq : (V : ℤ) = ((Nat.ofDigits B ys : ℕ) : ℤ) := h.trans heval.symm
      exact_mod_cast heq
    · intro h
      rw [h]
      exact heval
  have h29 := lemma_2_9 (s := s + 1) (t := β) (n := L4 ν) (m := L4 ν) (k := L4 ν)
    (by omega) hst le_rfl le_rfl hbig' hysz hlen V
  rw [hVB, h29, ← hvy, ← h2z, ← hB]

/-- The shorter mask always lies below its cutoff. -/
theorem short_mask_lt {B z : ℕ} (hB : 2 ≤ B) (hz : 0 < z) (L : ℕ) :
    mask29 B (2 * z) L < B ^ L := by
  unfold mask29
  have h := Nat.ofDigits_lt_base_pow_length (b := B) (l := List.replicate L (B - 2 * z))
    (by omega) (fun x hx => by rw [List.mem_replicate] at hx; rw [hx.2]; omega)
  simpa using h

set_option maxHeartbeats 1000000 in
/-- The packed transfer condition is exactly recovery of `lpoly` and `epoly`.
The bound on `e` deliberately allows its nonzero digit at position `L`. -/
theorem ShortEqs.transfer_iff {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ}
    {x z u y b B c e g l m Q t lam ε w : ℕ}
    (hI : Index ν P z u y) (hb : b = 2 ^ w) (hw : 1 ≤ w)
    (hlQ : l < Q) (heQ : e < 2 * z * Q)
    (h : ShortEqs ν x z u y b B c e g l m Q t lam ε) :
    τ 2 (l + e * Q) ((B - 2 * z) * lam * (1 + Q)) = 0 ↔
      (l : ℤ) = (lpoly ν 4).eval (B : ℤ) ∧
      (e : ℤ) = (epoly ν 4 P z).eval (B : ℤ) := by
  have hz := hI.two_le
  have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
  have hb1 : 1 ≤ b := by omega
  have hbase := shortBase_bounds (ν := ν) hz hb1
  have hB2 : 2 ≤ B := by rw [h.D2]; omega
  have h2zB : 2 * z ≤ B := by rw [h.D2]; omega
  obtain ⟨s, hs⟩ := hI.pow2
  let β := 1 + w * 4 + (s + 1) * (L4 ν + 1)
  have hBpow : B = 2 ^ β := by rw [h.D2]; exact shortBase_pow_two hs hb
  have hQpow : Q = 2 ^ (β * L4 ν) := by rw [h.power, hBpow, ← pow_mul]
  have hbig : 2 * (2 * z) ^ (L4 ν + 1) ≤ B := by
    have hb4 : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb1
    rw [h.D2]
    unfold shortBase
    exact Nat.mul_le_mul_right _ (by omega : 2 ≤ 2 * b ^ 4)
  have hlam := h.lam_eq hB2
  have hmask : mask29 B (2 * z) (L4 ν) = (B - 2 * z) * lam := by
    rw [mask29_eq, hlam]
    rfl
  have hmasklt : mask29 B (2 * z) (L4 ν) < Q := by
    rw [h.power]
    exact short_mask_lt hB2 (by omega) _
  have hsplit : τ 2 (l + e * Q) ((B - 2 * z) * lam * (1 + Q)) = 0 ↔
      τ 2 l (mask29 B (2 * z) (L4 ν)) = 0 ∧
      τ 2 e (mask29 B (2 * z) (L4 ν)) = 0 := by
    have heq : (B - 2 * z) * lam * (1 + Q) =
        mask29 B (2 * z) (L4 ν) + mask29 B (2 * z) (L4 ν) * Q := by rw [hmask]; ring
    rw [heq, hQpow]
    apply (lemma_2_10 (by rwa [← hQpow]) (by rwa [← hQpow])).symm
  have hlcong : l ≡ u [MOD B - 2 * z] := by
    rw [Nat.modEq_iff_dvd, Nat.cast_sub h2zB]
    push_cast
    refine ⟨-(t : ℤ), ?_⟩
    linear_combination -h.D9
  have hecong : e ≡ y [MOD B - 2 * z] := by
    rw [Nat.modEq_iff_dvd, Nat.cast_sub h2zB]
    push_cast
    refine ⟨-(m : ℤ), ?_⟩
    linear_combination -h.D10
  have hlBound : l < 2 * z * B ^ L4 ν := by
    rw [← h.power]
    exact lt_of_lt_of_le hlQ (Nat.le_mul_of_pos_left Q (by omega))
  have hlpoly := short_transfer_poly_iff hI hBpow hbig (lpoly ν 4)
    (fun j => (coeff_lpoly_bounds ν j).1)
    (fun j => lt_of_le_of_lt (coeff_lpoly_bounds ν j).2 (by omega))
    (le_trans (natDegree_lpoly_le ν)
      (by change 5 ^ ν ≤ 5 ^ (ν + 1); exact Nat.pow_le_pow_right (by norm_num) (by omega))) hI.hu
    (V := l)
  have hepoly := short_transfer_poly_iff hI hBpow hbig (epoly ν 4 P z)
    (fun j => (hI.coeff_epoly_bounds j).1) (fun j => (hI.coeff_epoly_bounds j).2)
    (natDegree_epoly_le ν 4 P z) hI.hy (V := e)
  rw [hsplit, hlpoly, hepoly]
  have heBound : e < 2 * z * B ^ L4 ν := by rwa [← h.power]
  tauto

end Jones1982
