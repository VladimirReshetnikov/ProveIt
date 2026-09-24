import Diophantine.Paper1982.Packing
import Diophantine.Paper1982.PackingBounds

/-!
# Jones 1982, Theorem 2: one central binomial coefficient

The three carry conditions are combined in blocks of lengths `q³`, `q⁴`, `q⁹`,
and then encoded by a single divisibility condition using Lemma 2.16.
All fourteen witnesses of the printed system are strictly positive. As for
Theorem 1, the exponent is parameterized by `ν`; `ν = 58` recovers `5^60`.
This does not assume the separate universality of the pair `(58, 4)`.
-/

namespace Jones1982

/-- The fourteen-witness system of Theorem 2 of the 1982 article (with `ν = 58`,
also Theorem 2 of the 1980 announcement). The common six equations are
inherited from `UEqs`; the equation for `r` is interpreted over the integers. -/
structure Thm2 (ν : ℕ) (x z u y b e g l m n q r t w α η θ lam : ℕ) : Prop
    extends UEqs ν x z u y b e g l m q t θ lam α where
  E7 : b = 2 ^ w
  E8 : n = q ^ 16
  E9 : (r : ℤ) = rPolynomial x z b e g l n q θ lam
  E10 : η * n ^ 2 = (2 * r).choose r

section

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- The size facts cited before applying Lemma 2.25 in the proof of Theorem 3.
They follow from the common equations and the printed definition of `r`,
without requiring a power-of-two or binomial-divisibility hypothesis. -/
theorem UEqs.packing_sizes (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x)
    {b e g l m n q r t θ lam α : ℕ} (hb2 : 2 ≤ b)
    (hg : 0 < g) (hl : 0 < l) (hm : 0 < m) (ht : 0 < t) (hα : 0 < α)
    (hU : UEqs ν x z u y b e g l m q t θ lam α) (hn : n = q ^ 16)
    (hr : (r : ℤ) = rPolynomial x z b e g l n q θ lam) :
    8 ≤ n ∧ n ≤ r ∧ b ≤ n ∧ 8 ≤ r ∧ b ≤ r := by
  obtain ⟨_, _, _, hlq, _, hbq, _⟩ := hU.sizes hI hx hb2 hg hl hm ht hα
  have hqn : q ≤ n := by rw [hn]; exact Nat.le_self_pow (by norm_num) q
  have hn8 : 8 ≤ n := by
    have : 2 ^ 16 ≤ q ^ 16 := Nat.pow_le_pow_left (by omega) 16
    rw [← hn] at this
    norm_num at this
    omega
  have hM := M1_bounds hb2 hbq hlq
  have hS := hU.S3_nonneg hI hx hb2 hg hl hm ht hα
  have hc := centralCode_eq_rPolynomial (θ := θ) hb2 hM (by omega : 1 ≤ n) hS
  have hrEq : r = centralCode n (packedS x z b e g l q lam) (packedT b l q θ lam) := by
    exact_mod_cast hr.trans hc.symm
  have hnr : n ≤ r := by rw [hrEq]; exact centralCode_ge_base (by omega)
  exact ⟨hn8, hnr, by omega, by omega, by omega⟩

/-- Under the common equations, the three carry conditions are equivalent
to the central-binomial divisibility condition of Theorem 2. -/
theorem UEqs.usys_iff_central (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x)
    {b e g l m q t θ lam α w : ℕ} (hb : b = 2 ^ w) (hw : 0 < w)
    (hg : 0 < g) (hl : 0 < l) (hm : 0 < m) (ht : 0 < t) (hα : 0 < α)
    (hU : UEqs ν x z u y b e g l m q t θ lam α) :
    USys ν x z u y b e g l m q t θ lam α ↔
      (q ^ 16) ^ 2 ∣ (2 * centralCode (q ^ 16)
        (packedS x z b e g l q lam) (packedT b l q θ lam)).choose
          (centralCode (q ^ 16) (packedS x z b e g l q lam) (packedT b l q θ lam)) := by
  have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
  obtain ⟨hS₁, hT₁, hS₂, hT₂, hS₃, hT₃⟩ := hU.packing_bounds hI hx hb2 hg hl hm ht hα
  have hq : q = 2 ^ (w * 5 ^ (ν + 2)) := by rw [hU.U3, hb, ← pow_mul]
  have hiff := pack3_carries_iff_dvd hq hS₁ hT₁ hS₂ hT₂ hS₃ hT₃
  change (_ ∧ _ ∧ _) ↔ _ at hiff
  change USys ν x z u y b e g l m q t θ lam α ↔ _
  constructor
  · intro h
    exact hiff.1 ⟨h.τ1, h.τ2, h.τ3⟩
  · intro h
    obtain ⟨h₁, h₂, h₃⟩ := hiff.2 h
    exact ⟨hU, h₁, h₂, h₃⟩

/-- Theorem 2 of the 1982 article (with `ν = 58` also Theorem 2 of the 1980
announcement): membership is equivalent to the printed system with fourteen
strictly positive witnesses and one central binomial coefficient. -/
theorem theorem_2 (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ ∃ b e g l m n q r t w α η θ lam : ℕ,
      0 < b ∧ 0 < e ∧ 0 < g ∧ 0 < l ∧ 0 < m ∧ 0 < n ∧ 0 < q ∧ 0 < r ∧
      0 < t ∧ 0 < w ∧ 0 < α ∧ 0 < η ∧ 0 < θ ∧ 0 < lam ∧
      Thm2 ν x z u y b e g l m n q r t w α η θ lam := by
  constructor
  · intro hW
    obtain ⟨b, e, g, l, m, q, t, θ, lam, α, w, he, hg, hl, hm, hq, ht, hθ, hlam, hα, hw, hb, hU⟩ :=
      (master hν hP hnorm hI hx).1 hW
    have hb2 : 2 ≤ b := by rw [hb]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨_, _, _, hlq, _, hbq, _⟩ := hU.toUEqs.sizes hI hx hb2 hg hl hm ht hα
    have hM := M1_bounds hb2 hbq hlq
    have hS := hU.toUEqs.S3_nonneg hI hx hb2 hg hl hm ht hα
    let n := q ^ 16
    let r := centralCode n (packedS x z b e g l q lam) (packedT b l q θ lam)
    have hn : 2 ≤ n := le_trans (by omega : 2 ≤ q) (Nat.le_self_pow (by norm_num) q)
    have hr : 0 < r := centralCode_pos hn
    have hdvd : n ^ 2 ∣ (2 * r).choose r :=
      (hU.toUEqs.usys_iff_central hI hx hb hw hg hl hm ht hα).1 hU
    obtain ⟨η, hη⟩ := hdvd
    have hηpos : 0 < η := by
      have hchoose : 0 < (2 * r).choose r := Nat.choose_pos (by omega)
      by_contra h
      have : η = 0 := by omega
      rw [this, mul_zero] at hη
      omega
    refine ⟨b, e, g, l, m, n, q, r, t, w, α, η, θ, lam,
      by omega, he, hg, hl, hm, by omega, hq, hr, ht, hw, hα, hηpos, hθ, hlam,
      ⟨hU.toUEqs, hb, rfl, ?_, ?_⟩⟩
    · exact centralCode_eq_rPolynomial hb2 hM (by omega) hS
    · rw [hη, mul_comm]
  · rintro ⟨b, e, g, l, m, n, q, r, t, w, α, η, θ, lam,
      _, he, hg, hl, hm, hn, hq, hr, ht, hw, hα, hη, hθ, hlam, h⟩
    have hb2 : 2 ≤ b := by rw [h.E7]; exact Nat.one_lt_two_pow (by omega)
    obtain ⟨_, _, _, hlq, _, hbq, _⟩ := h.toUEqs.sizes hI hx hb2 hg hl hm ht hα
    have hM := M1_bounds hb2 hbq hlq
    have hS := h.toUEqs.S3_nonneg hI hx hb2 hg hl hm ht hα
    have hrEq : r = centralCode n (packedS x z b e g l q lam) (packedT b l q θ lam) := by
      have hc := centralCode_eq_rPolynomial (θ := θ) hb2 hM (by omega : 1 ≤ n) hS
      exact_mod_cast h.E9.trans hc.symm
    have hdvd : n ^ 2 ∣ (2 * r).choose r := ⟨η, by rw [← h.E10, mul_comm]⟩
    rw [hrEq, h.E8] at hdvd
    have hU := (h.toUEqs.usys_iff_central hI hx h.E7 hw hg hl hm ht hα).2 hdvd
    exact mem_of_USys hν hP hI hx h.E7 hw hg hl hm ht hα hU

end

end Jones1982
