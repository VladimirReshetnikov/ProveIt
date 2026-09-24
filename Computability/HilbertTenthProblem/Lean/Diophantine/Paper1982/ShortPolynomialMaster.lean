import Diophantine.Paper1982.ShortPolynomialDefs
import Diophantine.Paper1982.ShortPellNecessity
import Diophantine.Paper1982.ShortPellSoundness
import Diophantine.Paper1982.Index

/-!
# The full fifty-three-witness system in Jones 1982, §5

The Pell subsystem eliminates both powers and the central-binomial test.
All fifty-three scalar witnesses of (D1)–(D37) are explicit in the nested
record; the possibly signed `D₀` is kept over `ℤ`. This precedes the
separate substitution and quadratization reducing the system to degree two.
-/

namespace Jones1982

section

variable {ν : ℕ} {P : MvPolynomial (Fin (ν + 1)) ℤ} {z u y : ℕ}

/-- Soundness of the full polynomial system, with no exponential assumption. -/
theorem mem_of_shortPolynomial (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4)
    (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x)
    (h : ShortPolynomialWitnesses ν x z u y) : Wset P x := by
  obtain ⟨hL, hLB, hBQ, hQN, hNR, hN8, _, hbN, _⟩ := h.sizes hI.two_le hx
  obtain ⟨hdvd, ⟨v, hpow⟩, hQ⟩ :=
    ShortPellWitnesses.sound hN8 h.b_pos hbN ⟨hL, hLB, hBQ, hQN, hNR⟩ h.pell
  obtain ⟨hN, hS, hT, hR⟩ := h.packing_eqs
  have hRpacked : h.R = centralCode (shortPackedN z h.Q)
      (shortPackedS z h.B h.c h.e h.g h.l h.Q h.lam)
      (shortPackedT z h.b h.B h.l h.Q h.lam) := by
    simpa only [hN, hS, hT] using hR
  have hPacked : ShortPackedSys ν x z u y h.b h.B h.c h.e h.g h.l h.m h.Q h.t h.lam h.ε := by
    refine ⟨⟨h.D1, h.D2, hQ, h.D6, h.geom_nat, h.D8, h.D9, h.D10⟩, ?_⟩
    simpa only [hN, hRpacked] using hdvd
  have hv : 0 < v := by
    have hb2 : 2 ≤ h.b := by have := h.D1; have := h.ε_pos; omega
    by_contra hn
    have : v = 0 := by omega
    rw [this, pow_zero] at hpow
    omega
  have hShort := (hPacked.toShortEqs.shortSys_iff_packed hI hx h.ε_pos h.l_pos hpow).2 hPacked
  exact mem_of_ShortSys hν hP hI hx h.ε_pos hpow hv hShort

set_option maxHeartbeats 1000000 in
/-- The packed coding system admits all explicit positive intermediate
quantities and the twenty-seven positive Pell witnesses. -/
theorem exists_shortPolynomial_of_packed (hI : Index ν P z u y)
    {x b B c e g l m Q t lam ε v : ℕ} (hx : 0 < x)
    (hb : 0 < b) (hB : 0 < B) (hc : 0 < c) (he : 0 < e) (hg : 0 < g)
    (hl : 0 < l) (hm : 0 < m) (hQ : 0 < Q) (ht : 0 < t) (hlam : 0 < lam)
    (hε : 0 < ε) (hpow : b = 2 ^ v)
    (h : ShortPackedSys ν x z u y b B c e g l m Q t lam ε) :
    Nonempty (ShortPolynomialWitnesses ν x z u y) := by
  let N := shortPackedN z Q
  let S := shortPackedS z B c e g l Q lam
  let T := shortPackedT z b B l Q lam
  let R := centralCode N S T
  obtain ⟨hL, hLB, hBQ, hQN, hNR, hN8, hR8, hbN, _⟩ :=
    h.toShortEqs.packing_sizes hI hx hε (N := N) (R := R) rfl rfl
  obtain ⟨hPell⟩ := exists_shortPell hN8 hb hbN ⟨hL, hLB, hBQ, hQN, hNR⟩
    h.dvd ⟨v, hpow⟩ h.power
  obtain ⟨_, hM0, _, _, hT20, _, hS30, _, hT30, _⟩ :=
    h.toShortEqs.packing_bounds hI hx hε hl
  have hb2 : 2 ≤ b := by have := h.D1; omega
  obtain ⟨_, h4z, _⟩ := shortBase_bounds (ν := ν) hI.two_le hb
  rw [← h.D2] at h4z
  have hbl : b * l < Q := by
    apply Nat.lt_of_mul_lt_mul_left (a := 2 * z)
    have := h.D8
    nlinarith only [this, Nat.zero_le e, Nat.zero_le (2 * z * B * c ^ 4)]
  have hMpos : 0 < (Q : ℤ) - 1 - ((b : ℤ) - 1) * l := by
    have hblZ : (b : ℤ) * l < Q := by exact_mod_cast hbl
    have hlZ : (0 : ℤ) < l := by exact_mod_cast hl
    nlinarith only [hblZ, hlZ]
  have hB2z : (0 : ℤ) < (B : ℤ) - 2 * z := by
    have hz := hI.two_le
    have hnat : 2 * z < B := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hB2 : (0 : ℤ) < (B : ℤ) - 2 := by
    have hz := hI.two_le
    have hnat : 2 < B := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hT2pos : 0 < ((B : ℤ) - 2 * z) * lam * (1 + Q) := by positivity
  have hT3pos : 0 < ((B : ℤ) - 2) * Q := by positivity
  have hMcast : (((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat : ℤ) =
      (Q : ℤ) - 1 - ((b : ℤ) - 1) * l := Int.toNat_of_nonneg hM0
  have hS3cast : ((shortS3 z B c e Q lam).toNat : ℤ) = shortS3 z B c e Q lam :=
    Int.toNat_of_nonneg hS30.le
  have hT2cast : ((((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat : ℤ) =
      ((B : ℤ) - 2 * z) * lam * (1 + Q) := Int.toNat_of_nonneg hT20
  have hT3cast : ((((B : ℤ) - 2) * Q).toNat : ℤ) = ((B : ℤ) - 2) * Q :=
    Int.toNat_of_nonneg hT30
  have hMnat : 0 < ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat := by omega
  have hSpos : 0 < S := by dsimp [S, shortPackedS, pack3]; positivity
  have hTpos : 0 < T := by dsimp [T, shortPackedT, pack3]; positivity
  refine ⟨{
    b := b, B := B, c := c, e := e, g := g, l := l, m := m,
    Q := Q, t := t, lam := lam, ε := ε, N := N, R := R,
    M₁ := ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat,
    D₀ := z * ((lam : ℤ) + Q) - e,
    S₁ := g, S₂ := l + e * Q, S₃ := (shortS3 z B c e Q lam).toNat,
    T₁ := ((Q : ℤ) - 1 - ((b : ℤ) - 1) * l).toNat,
    T₂ := (((B : ℤ) - 2 * z) * lam * (1 + Q)).toNat,
    T₃ := (((B : ℤ) - 2) * Q).toNat,
    N₁ := Q, N₂ := 2 * z * Q ^ 2, N₃ := 8 * Q ^ 2, S := S, T := T,
    pell := hPell,
    b_pos := hb, B_pos := hB, c_pos := hc, e_pos := he, g_pos := hg,
    l_pos := hl, m_pos := hm, Q_pos := hQ, t_pos := ht, lam_pos := hlam, ε_pos := hε,
    N_pos := by omega, R_pos := by omega, M₁_pos := hMnat,
    S₁_pos := hg, S₂_pos := by positivity, S₃_pos := by omega,
    T₁_pos := hMnat, T₂_pos := by omega, T₃_pos := by omega,
    N₁_pos := hQ, N₂_pos := by have := hI.two_le; positivity,
    N₃_pos := by positivity, S_pos := hSpos, T_pos := hTpos,
    D1 := h.D1, D2 := h.D2, D6 := h.D6, D7 := ?_, D8 := h.D8,
    D9 := h.D9, D10 := h.D10, D11 := hMcast, D12 := rfl,
    D13 := ⟨rfl, rfl, rfl⟩, D14 := ⟨rfl, hT2cast, rfl⟩,
    D15 := ⟨hS3cast, hT3cast, rfl⟩, D16 := ⟨rfl, rfl⟩,
    D17 := rfl, D18 := ?_
  }⟩
  · have hgeom := congrArg (fun n : ℕ => (n : ℤ)) h.D7
    push_cast [Nat.cast_sub hB] at hgeom
    exact hgeom
  · have hNsq : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num) N
    have hN1 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (by omega : 1 ≤ N)
    dsimp [R, centralCode]
    push_cast [Nat.cast_sub hNsq, Nat.cast_sub hN1]
    rfl

/-- The complete system (D1)–(D37) is equivalent to membership in the
represented set, with its fifty-three scalar witnesses and no retained powers. -/
theorem short_polynomial_master (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4)
    (hnorm : Normalized P) (hI : Index ν P z u y) {x : ℕ} (hx : 0 < x) :
    Wset P x ↔ Nonempty (ShortPolynomialWitnesses ν x z u y) := by
  constructor
  · intro hW
    obtain ⟨b, B, c, e, g, l, m, Q, t, lam, ε, v,
      hb, hB, hc, he, hg, hl, hm, hQ, ht, hlam, hε, _, hpow, h⟩ :=
      (short_master_packed hν hP hnorm hI hx).1 hW
    exact exists_shortPolynomial_of_packed hI hx hb hB hc he hg hl hm hQ ht hlam hε hpow h
  · rintro ⟨h⟩
    exact mem_of_shortPolynomial hν hP hI hx h

end

/-- A single positive coding triple represents all positive inputs of the
supplied normalized polynomial by the full §5 system. -/
theorem short_polynomial_representation {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧ Index ν P z u y ∧
      ∀ x : ℕ, 0 < x → (Wset P x ↔ Nonempty (ShortPolynomialWitnesses ν x z u y)) := by
  obtain ⟨z, u, y, hz, hu, hy, hI⟩ := exists_index P hν
  exact ⟨z, u, y, hz, hu, hy, hI, fun _ hx => short_polynomial_master hν hP hnorm hI hx⟩

/-- The literal rational inequality (D21) is exactly its integer polynomial
form when the denominator witness is positive. -/
theorem short_ratio_iff {C K Y : ℕ} (hK : 0 < K) :
    ((C : ℚ) / K - Y) ^ 2 < 1 / 4 ↔
      4 * ((C : ℤ) - K * Y) ^ 2 < (K : ℤ) ^ 2 := by
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK
  have hKsq : (0 : ℚ) < (K : ℚ) ^ 2 := pow_pos hKq 2
  have heq : ((C : ℚ) / K - Y) ^ 2 = ((C : ℚ) - K * Y) ^ 2 / (K : ℚ) ^ 2 := by
    field_simp
  rw [heq, div_lt_iff₀ hKsq]
  constructor
  · intro h
    have hq : 4 * ((C : ℚ) - K * Y) ^ 2 < (K : ℚ) ^ 2 := by nlinarith only [h]
    exact_mod_cast hq
  · intro h
    have hq : 4 * ((C : ℚ) - K * Y) ^ 2 < (K : ℚ) ^ 2 := by exact_mod_cast h
    nlinarith only [hq]

end Jones1982
