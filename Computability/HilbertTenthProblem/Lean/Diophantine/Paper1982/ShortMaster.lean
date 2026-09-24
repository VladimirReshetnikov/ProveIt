import Diophantine.Paper1982.ShortDigits
import Diophantine.Paper1982.ShortMask
import Diophantine.Paper1982.ShortTransfer
import Diophantine.Paper1982.ShortWitnesses

/-!
# The shorter coding equivalence in Jones 1982, §5

This is the first stage of the construction: retain `Q = B^L` and impose
the three carry tests. Every witness is positive. Replacing the power
equation by Pell conditions and reducing the degree are separate stages.
-/

namespace Jones1982

/-- The shorter coding equations with their three carry conditions. -/
structure ShortSys (ν : ℕ) (x z u y b B c e g l m Q t lam ε : ℕ) : Prop
    extends ShortEqs ν x z u y b B c e g l m Q t lam ε where
  τ1 : τ 2 g (Q - 1 - (b - 1) * l) = 0
  τ2 : τ 2 (l + e * Q) ((B - 2 * z) * lam * (1 + Q)) = 0
  τ3 : τ 2 (shortS3 z B c e Q lam).toNat ((B - 2) * Q) = 0

/-- The budget inequality bounds the two quantities being transferred. -/
theorem ShortEqs.transfer_bounds {ν x z u y b B c e g l m Q t lam ε : ℕ}
    (hb : 0 < b) (h : ShortEqs ν x z u y b B c e g l m Q t lam ε) :
    l < Q ∧ e < 2 * z * Q := by
  have hbl : 2 * z * (b * l) < 2 * z * Q := by
    have := h.D8
    nlinarith only [this, Nat.zero_le e, Nat.zero_le (2 * z * B * c ^ 4)]
  have hbl' := Nat.lt_of_mul_lt_mul_left hbl
  have hl := lt_of_le_of_lt (Nat.le_mul_of_pos_left l hb) hbl'
  have he : e < 2 * z * Q := by have := h.D8; omega
  exact ⟨hl, he⟩

section

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- Soundness of the shorter coding system, retaining its exponential equation. -/
theorem mem_of_ShortSys (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4)
    (hI : Index ν P z u y) {x b B c e g l m Q t lam ε w : ℕ}
    (_hx : 0 < x) (hε : 0 < ε) (hb : b = 2 ^ w) (hw : 0 < w)
    (h : ShortSys ν x z u y b B c e g l m Q t lam ε) : Wset P x := by
  have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
  have hxb : x < b := by have := h.D1; omega
  obtain ⟨hbB, hzB, _⟩ := shortBase_bounds (ν := ν) hI.two_le (by omega : 1 ≤ b)
  rw [← h.D2] at hbB hzB
  have hB2 : 2 ≤ B := by omega
  obtain ⟨s, hs⟩ := hI.pow2
  let k := 1 + w * 4 + (s + 1) * (L4 ν + 1)
  have hBpow : B = 2 ^ k := by rw [h.D2]; exact shortBase_pow_two hs hb
  have hk : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨hlQ, heQ⟩ := h.toShortEqs.transfer_bounds (by omega : 0 < b)
  obtain ⟨hlZ, heZ⟩ := (h.toShortEqs.transfer_iff hI hb hw hlQ heQ).1 h.τ2
  have hgQ : g < Q := by
    have hBc : B * c ^ 4 < Q := by
      apply Nat.lt_of_mul_lt_mul_left (a := 2 * z)
      have := h.D8
      nlinarith only [this, Nat.zero_le e, Nat.zero_le (2 * z * b * l)]
    calc g ≤ c := by have := h.D6; omega
      _ ≤ c ^ 4 := Nat.le_self_pow (by norm_num) c
      _ ≤ B * c ^ 4 := Nat.le_mul_of_pos_left _ (by omega)
      _ < Q := hBc
  obtain ⟨zs, hzs0, hzs, hgZ⟩ := short_code_of_tau1 (ν := ν) hb hBpow hB2 hbB.le hxb hlZ
    (by simpa only [h.power] using hgQ) (by simpa only [h.power] using h.τ1)
  have hcZ : (c : ℤ) = (cpoly ν 4 zs).eval (B : ℤ) := by
    rw [eval_cpoly_eq, hzs0, ← hgZ, h.D6]
    push_cast
    rfl
  have hlamZ : (lam : ℤ) = ∑ i ∈ Finset.range (L4 ν), (B : ℤ) ^ i := by
    rw [h.toShortEqs.lam_eq hB2]
    unfold shortLam
    push_cast
    rfl
  exact ⟨zs, hzs0, (short_tau3_iff hI hν hP h.D2 hBpow hk zs hzs heZ hcZ hlamZ h.power).1 h.τ3⟩

/-- Membership gives positive shorter-system witnesses. The normalization
hypothesis supplies a positive tail coordinate, hence a positive code tail. -/
theorem ShortSys_of_mem (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) (hW : Wset P x) :
    ∃ b B c e g l m Q t lam ε w : ℕ,
      0 < b ∧ 0 < B ∧ 0 < c ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < Q ∧
      0 < t ∧ 0 < lam ∧ 0 < ε ∧ 0 < w ∧ b = 2 ^ w ∧
      ShortSys ν x z u y b B c e g l m Q t lam ε := by
  obtain ⟨zs, hzs0, hsol⟩ := hW
  have htail : ∃ j : Fin (ν + 1), j ≠ 0 ∧ 0 < zs j := by
    by_contra hnone
    have hzero : ∀ j, j ≠ 0 → zs j = 0 := by
      intro j hj
      by_contra hn
      exact hnone ⟨j, hj, by omega⟩
    apply hnorm x
    have heq : (fun j : Fin (ν + 1) => if j = 0 then (x : ℤ) else 0) =
        (fun j : Fin (ν + 1) => (zs j : ℤ)) := by
      funext j
      by_cases hj : j = 0
      · subst j; simp [hzs0]
      · simp [hj, hzero j hj]
    rw [heq]
    exact hsol
  obtain ⟨b, B, c, e, g, l, m, Q, t, lam, ε, w,
    hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, hw, hbpow, hzs, hE, hcZ, heZ, hlZ, hgZ⟩ :=
    exists_shortEqs_of_digits hν hI zs (by rwa [hzs0]) htail
  rw [hzs0] at hE
  obtain ⟨hbB, hzB, _⟩ := shortBase_bounds (ν := ν) hI.two_le hb
  rw [← hE.D2] at hbB hzB
  have hB2 : 2 ≤ B := by omega
  obtain ⟨s, hs⟩ := hI.pow2
  let k := 1 + w * 4 + (s + 1) * (L4 ν + 1)
  have hBpow : B = 2 ^ k := by rw [hE.D2]; exact shortBase_pow_two hs hbpow
  have hk : 1 ≤ k := by dsimp [k]; omega
  obtain ⟨hτ1, _⟩ := short_tau1_of_code (ν := ν) hbpow hBpow hB2 hbB.le hlZ zs hzs hgZ
  rw [← hE.power] at hτ1
  obtain ⟨hlQ, heQ⟩ := hE.transfer_bounds hb
  have hτ2 := (hE.transfer_iff hI hbpow hw hlQ heQ).2 ⟨hlZ, heZ⟩
  have hlamZ : (lam : ℤ) = ∑ i ∈ Finset.range (L4 ν), (B : ℤ) ^ i := by
    rw [hE.lam_eq hB2]
    unfold shortLam
    push_cast
    rfl
  have hτ3 := (short_tau3_iff hI hν hP hE.D2 hBpow hk zs hzs heZ hcZ hlamZ hE.power).2 hsol
  exact ⟨b, B, c, e, g, l, m, Q, t, lam, ε, w,
    hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, hw, hbpow, ⟨hE, hτ1, hτ2, hτ3⟩⟩

/-- The coding equivalence of §5 before eliminating `Q = B^L`. -/
theorem short_master (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ b B c e g l m Q t lam ε w : ℕ,
      0 < b ∧ 0 < B ∧ 0 < c ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < Q ∧
      0 < t ∧ 0 < lam ∧ 0 < ε ∧ 0 < w ∧ b = 2 ^ w ∧
      ShortSys ν x z u y b B c e g l m Q t lam ε := by
  constructor
  · exact ShortSys_of_mem hν hP hnorm hI hx
  · rintro ⟨b, B, c, e, g, l, m, Q, t, lam, ε, w,
      _, _, _, _, _, _, _, _, _, _, hε, hw, hb, h⟩
    exact mem_of_ShortSys hν hP hI hx hε hb hw h

end

end Jones1982
