import Diophantine.Paper1980.Borrow100

/-!
# The carry descent of the counter route

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §§3–4.  The packed word is twice a Boolean word,
so its base-`q` chunks are even and at most `q − 1`; the twelve *conceptual* fields of
`(1)` need not be those chunks, because a complement may be negative and a pair may carry.
This module runs the descent of §3, tracking the carry at each of the twelve levels, and
reaches the conclusions of §§3–4:

* the sign pair is exact, with no carry on either side;
* the zero pair may borrow once but emits nothing into the guard block;
* neither guard pair emits a carry, although their internal carries are large;
* the junk pair's outgoing carry `kappa` satisfies `0 ≤ kappa ≤ K`;
* the state pair has at most one borrow, which the mask and the route residue exclude, so
  `C ≤ S H + kappa ≤ S H + K`;
* hence `2V < q`, hence `kappa = 0`, hence `C ≤ S H`;
* hence the junk pair has no borrow either, so `V ≤ z H` and `V` is even;
* hence, by the parity of the route, `D` is even, and an odd normalized zero field is
  excluded by the mask, so `D ≤ H`.

`nonneg_upper100` is that conclusion: three of the five statements of `Nonneg100`.  The two
guard complements `A₀ ≤ t` and `A₁ ≤ t` are *not* reachable here.  §5 derives them from the
decoded controller, through `D ≥ 2q/R` and `A < 3q/R`, and that decoding is the part of the
note that rests on the published 101 predecessor.
-/

namespace Jones1980

open Ternary

/-! ### One level of the descent -/

/-- Splitting a doubled word at the modulus. -/
theorem Ternary.double_split (B M : ℕ) : 2 * B = 2 * (B % M) + M * (2 * (B / M)) := by
  have hdm := Nat.div_add_mod B M
  have hx : M * (2 * (B / M)) = 2 * (M * (B / M)) := by ring
  omega

/-- The algebraic content of one peel: an incoming value `x` congruent to the actual chunk
`c` modulo `q` differs from it by `q` times the outgoing carry, and the remaining word
carries that difference into the next field. -/
theorem peel_abstract {b q c dd x F T : ℤ}
    (hsplit : b = c + q * dd) (h : b = x + q * (F + q * T)) :
    ∃ γ : ℤ, x = c + q * γ ∧ dd = (F + γ) + q * T := by
  refine ⟨dd - (F + q * T), ?_, by ring⟩
  linear_combination hsplit - h

/-- The data of one level: the next word, the actual chunk, their bounds and the split. -/
theorem peel_data {Bk Q e : ℕ} (hQ : Q = 3 ^ e) (hB : Bool3 Bk) :
    ∃ Bk1 ck : ℕ, Bool3 Bk1 ∧ ck + 1 ≤ Q ∧ ck = 2 * (Bk % Q) ∧
      2 * (Bk : ℤ) = (ck : ℤ) + (Q : ℤ) * (2 * (Bk1 : ℤ)) := by
  refine ⟨Bk / Q, 2 * (Bk % Q), ?_, ?_, rfl, ?_⟩
  · subst hQ; exact hB.div_pow e
  · subst hQ
    have h1 := hB.mod_le_rep e
    have h2 := two_mul_rep_add_one e
    omega
  · exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) (Ternary.double_split Bk Q)

/-! ### Reading off a carry from bounds on the incoming value -/

/-- A nonnegative value below the modulus is its own chunk. -/
theorem carry_zero {q c x γ : ℤ} (h : x = c + q * γ) (hc0 : 0 ≤ c) (hcq : c < q)
    (hx0 : 0 ≤ x) (hxq : x < q) : γ = 0 ∧ x = c := by
  have hq : 0 < q := by linarith
  have h1 : q * γ < q := by linarith
  have h2 : -q < q * γ := by linarith
  have hlt : γ < 1 := by nlinarith
  have hgt : -1 < γ := by nlinarith
  have hγ : γ = 0 := by omega
  exact ⟨hγ, by rw [h, hγ]; ring⟩

/-- A value in `(−q, q)` either is its own chunk or borrows exactly once. -/
theorem carry_borrow {q c x γ : ℤ} (h : x = c + q * γ) (hc0 : 0 ≤ c) (hcq : c < q)
    (hlo : -q < x) (hhi : x < q) : γ = 0 ∨ γ = -1 := by
  have hq : 0 < q := by linarith
  have h1 : q * γ < q := by linarith
  have h2 : -(2 * q) < q * γ := by linarith
  have hlt : γ < 1 := by nlinarith
  have hgt : -2 < γ := by nlinarith
  omega

/-- The carry is the floor of the incoming value over the modulus. -/
theorem carry_range {q c x γ lo hi : ℤ} (h : x = c + q * γ) (hq : 0 < q)
    (hc0 : 0 ≤ c) (hcq : c < q) (hxlo : lo * q ≤ x) (hxhi : x < hi * q) :
    lo ≤ γ ∧ γ < hi := by
  constructor
  · by_contra hcon
    push_neg at hcon
    have : γ + 1 ≤ lo := by omega
    nlinarith
  · by_contra hcon
    push_neg at hcon
    nlinarith

/-! ### The outgoing carry of a pair -/

/-- The junk pair's two-field value is `zH + (q − 1)V`, and its outgoing carry is the floor
of that over `q²`; in particular it is nonnegative. -/
theorem pair_carry_nonneg {Q V ZH c8 c9 g : ℤ} (hq : 1 ≤ Q)
    (h : ZH + (Q - 1) * V = c8 + Q * c9 + Q ^ 2 * g)
    (hZH : 0 ≤ ZH) (hV : 0 ≤ V) (hc80 : 0 ≤ c8) (hc8 : c8 < Q)
    (hc90 : 0 ≤ c9) (hc9 : c9 < Q) : 0 ≤ g := by
  have hA : 0 ≤ (Q - 1) * V := mul_nonneg (by linarith) hV
  have hB : Q * c9 ≤ Q * (Q - 1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hkey : -(Q ^ 2) < Q ^ 2 * g := by nlinarith
  by_contra hcon
  push_neg at hcon
  have hle : g ≤ -1 := by omega
  nlinarith

/-- And it is at most `K`, since `V ≤ K q`. -/
theorem pair_carry_le {Q V ZH c8 c9 g K : ℤ} (hq : 2 ≤ Q)
    (h : ZH + (Q - 1) * V = c8 + Q * c9 + Q ^ 2 * g)
    (hZH : 0 ≤ ZH) (hZHq : ZH < Q) (hV : 0 ≤ V) (hVK : V ≤ K * Q)
    (hc80 : 0 ≤ c8) (hc90 : 0 ≤ c9) : g ≤ K := by
  have h1 : (Q - 1) * V ≤ Q * V := by nlinarith
  have h2 : Q * V ≤ Q * (K * Q) := mul_le_mul_of_nonneg_left hVK (by linarith)
  have hQQ : Q < Q ^ 2 := by nlinarith
  have hkey : Q ^ 2 * g < (K + 1) * Q ^ 2 := by nlinarith
  by_contra hcon
  push_neg at hcon
  have hge : K + 1 ≤ g := by omega
  nlinarith

/-- Once the pair value is below `q²`, that carry vanishes. -/
theorem pair_carry_zero {Q V ZH c8 c9 g : ℤ}
    (h : ZH + (Q - 1) * V = c8 + Q * c9 + Q ^ 2 * g)
    (hlt : ZH + (Q - 1) * V < Q ^ 2) (hQ : 0 < Q) (hc80 : 0 ≤ c8) (hc90 : 0 ≤ c9)
    (hg : 0 ≤ g) : g = 0 := by
  have hQ2 : 0 < Q ^ 2 := by positivity
  have h1 : Q ^ 2 * g < Q ^ 2 := by nlinarith
  have : g < 1 := by nlinarith
  omega

/-! ### The packed word as a Horner word -/

section Horner

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)

include hOk hP hS

set_option maxHeartbeats 1000000 in
/-- The packed word is twice a Boolean word, and equals the base-`q` Horner word of the
twelve conceptual fields — with genuine integer subtraction, before any claim that the
complements are nonnegative. -/
theorem packed_horner100 :
    ∃ e' B : ℕ, 1 ≤ e' ∧ q = 3 ^ e' ∧ Bool3 B ∧
      2 * (B : ℤ) = (Kp : ℤ) + (q : ℤ) * ((Km : ℤ) + (q : ℤ) * (((H : ℤ) - (D : ℤ))
        + (q : ℤ) * ((D : ℤ) + (q : ℤ) * (((t : ℤ) - (A0 : ℤ)) + (q : ℤ) * ((A0 : ℤ)
        + (q : ℤ) * (((t : ℤ) - (A1 : ℤ)) + (q : ℤ) * ((A1 : ℤ) + (q : ℤ) * (((z : ℤ) * (H : ℤ)
        - (PV : ℤ)) + (q : ℤ) * ((PV : ℤ) + (q : ℤ) * (((C.S : ℤ) * (H : ℤ) - (PC : ℤ))
        + (q : ℤ) * (PC : ℤ))))))))))) := by
  obtain ⟨e', he1, hqe', -, -, -, -, hP2, -, hBb⟩ := mask100 hP hS hOk.Zon_ge hOk.B0_ge
  obtain ⟨B, hBdef⟩ : ∃ y, y = r - rep (12 * e') := ⟨_, rfl⟩
  refine ⟨e', B, he1, hqe', by rw [hBdef]; exact hBb, ?_⟩
  have h8 := hS.E8
  have hPw : 2 * B
      = J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))))
        + (q ^ 2 + 1) * (H + q ^ 4 * t) + q ^ 8 * (H * (z + q ^ 2 * C.S)) := by
    rw [hBdef]; omega
  have hqZ : (q : ℤ) = (J : ℤ) + 1 := by exact_mod_cast hS.E0
  have hKpZ : (Kp : ℤ) = (H : ℤ) - (Km : ℤ) := by
    have h3 : ((Kp + Km : ℕ) : ℤ) = (H : ℤ) := by exact_mod_cast hS.E3
    push_cast at h3
    linarith
  have hid := horner_identity (q : ℤ) (J : ℤ) (Kp : ℤ) (Km : ℤ) (H : ℤ) (D : ℤ) (t : ℤ)
    (A0 : ℤ) (A1 : ℤ) (PV : ℤ) (PC : ℤ) (z : ℤ) (C.S : ℤ) hqZ hKpZ
  have hPwZ : 2 * (B : ℤ)
      = (J : ℤ) * ((Km : ℤ) + (q : ℤ) ^ 2 * ((D : ℤ) + (q : ℤ) ^ 2 * ((A0 : ℤ)
          + (q : ℤ) ^ 2 * ((A1 : ℤ) + (q : ℤ) ^ 2 * ((PV : ℤ) + (q : ℤ) ^ 2 * (PC : ℤ))))))
        + ((q : ℤ) ^ 2 + 1) * ((H : ℤ) + (q : ℤ) ^ 4 * (t : ℤ))
        + (q : ℤ) ^ 8 * ((H : ℤ) * ((z : ℤ) + (q : ℤ) ^ 2 * (C.S : ℤ))) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hPw
  exact hPwZ.trans hid.symm

end Horner

/-! ### The twelve levels -/

section Descent

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u dm pK : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

set_option maxHeartbeats 2000000 in
/-- **§§3–4.**  The carry descent through the twelve fields.  Three of the five
nonnegativity statements of `Nonneg100` follow: the zero, junk and state complements are
nonnegative.  The two guard complements are left to §5.

Beyond the system, the hypotheses are the Sidon layout of the compiled table, the width
conditions on the fixed state word, the route residue `C ≡ 2I` modulo the state modulus,
and the table's exponent layout `pK + aC < dm`. -/
theorem nonneg_upper100 (hSid : C.Sidon dm pK)
    (hdm : dm ≤ m) (hSm : C.S < 3 ^ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hI : 0 < C.I) (hIM : 2 * C.I < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hexp : ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm) :
    D ≤ H ∧ PV ≤ z * H ∧ PC ≤ C.S * H ∧
      ∃ kp km dd ddb pv pvb pc pcb, Bool3 kp ∧ Bool3 km ∧ Bool3 dd ∧ Bool3 ddb ∧
        Bool3 pv ∧ Bool3 pvb ∧ Bool3 pc ∧ Bool3 pcb ∧
        Kp = 2 * kp ∧ Km = 2 * km ∧ D = 2 * dd ∧ H - D = 2 * ddb ∧
        PV = 2 * pv ∧ z * H - PV = 2 * pvb ∧ PC = 2 * pc ∧ C.S * H - PC = 2 * pcb := by
  -- ## scalar bounds
  have hq1 : 1 ≤ q := hP.q
  have hHq := H_lt_q hOk hP hS
  have hPCq := PC_lt_q hOk hP hS hG
  have hDPC := D_lt_PC hOk hP hS
  have hSH := SH_small hOk hP hS
  have hzH := zH_small hOk hP hS
  have htrack := track_small hOk hP hS
  have hPVK := PV_lt hOk hP hS
  have hPCle := PC_le_q hOk hP hS
  have hKR := R_gt_K hOk hP hS
  have hRbig := R_big hOk hP hS
  have hZon := hOk.Zon_ge
  have hR27 : 27 ≤ R := by omega
  have hR3q : R ^ 3 ≤ q := by
    have h1 := hS.E1
    have h19 := hS.E19
    have hv : 1 ≤ v := hP.v
    calc R ^ 3 = R ^ 3 * 1 := by ring
      _ ≤ R ^ 3 * v := Nat.mul_le_mul_left _ hv
      _ = q := by rw [h1, h19]
  have h729 : 729 * R ≤ q := by
    have hsq : 729 ≤ R ^ 2 := by nlinarith
    have hmul : 729 * R ≤ R ^ 2 * R := Nat.mul_le_mul_right _ hsq
    have he3 : R ^ 2 * R = R ^ 3 := by ring
    omega
  have hE3 := hS.E3
  have hKpq : Kp < q := by omega
  have hKmq : Km < q := by omega
  have hDq : D < q := by omega
  have hD1 : 1 ≤ D := hP.D
  have hE5 := hS.E5
  have hDR : D * R ≤ q * R := Nat.mul_le_mul_right _ (by omega)
  have htqR : t < R * q := by
    have hcomm : q * R = R * q := mul_comm _ _
    omega
  have hPVKq : PV ≤ C.K * q := by
    have hmul : C.K * PC ≤ C.K * q := Nat.mul_le_mul_left _ hPCle
    omega
  -- ## the packed word as a Horner word
  obtain ⟨e', B, he1, hq3, hBool, hinv0⟩ := packed_horner100 hOk hP hS
  have hq3ge : 3 ≤ q := by
    rw [hq3]
    calc (3 : ℕ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ e' := Nat.pow_le_pow_right (by norm_num) he1
  -- ## the twelve peels
  obtain ⟨B1, c0, hb1, hq0c, hd0, hs0⟩ := peel_data hq3 hBool
  obtain ⟨g1, hx0, hinv1⟩ := peel_abstract hs0 hinv0
  obtain ⟨B2, c1, hb2, hq1c, hd1, hs1⟩ := peel_data hq3 hb1
  obtain ⟨g2, hx1, hinv2⟩ := peel_abstract hs1 hinv1
  obtain ⟨B3, c2, hb3, hq2c, hd2, hs2⟩ := peel_data hq3 hb2
  obtain ⟨g3, hx2, hinv3⟩ := peel_abstract hs2 hinv2
  obtain ⟨B4, c3, hb4, hq3c, hd3, hs3⟩ := peel_data hq3 hb3
  obtain ⟨g4, hx3, hinv4⟩ := peel_abstract hs3 hinv3
  obtain ⟨B5, c4, hb5, hq4c, hd4, hs4⟩ := peel_data hq3 hb4
  obtain ⟨g5, hx4, hinv5⟩ := peel_abstract hs4 hinv4
  obtain ⟨B6, c5, hb6, hq5c, hd5, hs5⟩ := peel_data hq3 hb5
  obtain ⟨g6, hx5, hinv6⟩ := peel_abstract hs5 hinv5
  obtain ⟨B7, c6, hb7, hq6c, hd6, hs6⟩ := peel_data hq3 hb6
  obtain ⟨g7, hx6, hinv7⟩ := peel_abstract hs6 hinv6
  obtain ⟨B8, c7, hb8, hq7c, hd7, hs7⟩ := peel_data hq3 hb7
  obtain ⟨g8, hx7, hinv8⟩ := peel_abstract hs7 hinv7
  obtain ⟨B9, c8, hb9, hq8c, hd8, hs8⟩ := peel_data hq3 hb8
  obtain ⟨g9, hx8, hinv9⟩ := peel_abstract hs8 hinv8
  obtain ⟨B10, c9, hb10, hq9c, hd9, hs9⟩ := peel_data hq3 hb9
  obtain ⟨g10, hx9, hinv10⟩ := peel_abstract hs9 hinv9
  have hinv10' : 2 * (B10 : ℤ)
      = ((C.S : ℤ) * (H : ℤ) - (PC : ℤ) + g10) + (q : ℤ) * ((PC : ℤ) + (q : ℤ) * 0) := by
    linear_combination hinv10
  obtain ⟨B11, c10, hb11, hq10c, hd10, hs10⟩ := peel_data hq3 hb10
  obtain ⟨g11, hx10, hinv11⟩ := peel_abstract hs10 hinv10'
  have hinv11' : 2 * (B11 : ℤ)
      = ((PC : ℤ) + g11) + (q : ℤ) * (0 + (q : ℤ) * 0) := by
    linear_combination hinv11
  obtain ⟨B12, c11, hb12, hq11c, hd11, hs11⟩ := peel_data hq3 hb11
  obtain ⟨g12, hx11, hinv12⟩ := peel_abstract hs11 hinv11'
  -- ## casts
  have hq0 : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hP.q
  have hq2z : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast (show 2 ≤ q by omega)
  have hHz : (H : ℤ) < (q : ℤ) := by exact_mod_cast hHq
  have hH0 : (0 : ℤ) ≤ (H : ℤ) := by positivity
  have hKp0 : (0 : ℤ) ≤ (Kp : ℤ) := by positivity
  have hKpz : (Kp : ℤ) < (q : ℤ) := by exact_mod_cast hKpq
  have hKm0 : (0 : ℤ) ≤ (Km : ℤ) := by positivity
  have hKmz : (Km : ℤ) < (q : ℤ) := by exact_mod_cast hKmq
  have hPCz : (PC : ℤ) < (q : ℤ) := by exact_mod_cast hPCq
  have hPC0z : (1 : ℤ) ≤ (PC : ℤ) := by exact_mod_cast hP.PC
  have hDz : (D : ℤ) < (q : ℤ) := by exact_mod_cast hDq
  have hD0z : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hP.D
  have hA00z : (1 : ℤ) ≤ (A0 : ℤ) := by exact_mod_cast hP.A0
  have hA10z : (1 : ℤ) ≤ (A1 : ℤ) := by exact_mod_cast hP.A1
  have htrackz : 4 * ((A0 : ℤ) + (A1 : ℤ)) < (q : ℤ) := by exact_mod_cast htrack
  have hzHz : 4 * ((z : ℤ) * (H : ℤ)) < (q : ℤ) := by exact_mod_cast hzH
  have hSHz : 16 * ((C.S : ℤ) * (H : ℤ)) < (q : ℤ) := by exact_mod_cast hSH
  have h729z : 729 * (R : ℤ) ≤ (q : ℤ) := by exact_mod_cast h729
  have hKRz : (C.K : ℤ) < (R : ℤ) := by exact_mod_cast hKR
  have hK0z : (0 : ℤ) ≤ (C.K : ℤ) := by positivity
  have ht0z : (0 : ℤ) ≤ (t : ℤ) := by positivity
  have htqRz : (t : ℤ) < (R : ℤ) * (q : ℤ) := by exact_mod_cast htqR
  have hPVKqz : (PV : ℤ) ≤ (C.K : ℤ) * (q : ℤ) := by exact_mod_cast hPVKq
  have hPV0z : (0 : ℤ) ≤ (PV : ℤ) := by positivity
  have hzH0z : (0 : ℤ) ≤ (z : ℤ) * (H : ℤ) := by positivity
  have hSH0z : (0 : ℤ) ≤ (C.S : ℤ) * (H : ℤ) := by positivity
  have hc00 : (0 : ℤ) ≤ (c0 : ℤ) := by positivity
  have hc0z : (c0 : ℤ) < (q : ℤ) := by exact_mod_cast hq0c
  have hc10 : (0 : ℤ) ≤ (c1 : ℤ) := by positivity
  have hc1z : (c1 : ℤ) < (q : ℤ) := by exact_mod_cast hq1c
  have hc20 : (0 : ℤ) ≤ (c2 : ℤ) := by positivity
  have hc2z : (c2 : ℤ) < (q : ℤ) := by exact_mod_cast hq2c
  have hc30 : (0 : ℤ) ≤ (c3 : ℤ) := by positivity
  have hc3z : (c3 : ℤ) < (q : ℤ) := by exact_mod_cast hq3c
  have hc40 : (0 : ℤ) ≤ (c4 : ℤ) := by positivity
  have hc4z : (c4 : ℤ) < (q : ℤ) := by exact_mod_cast hq4c
  have hc50 : (0 : ℤ) ≤ (c5 : ℤ) := by positivity
  have hc5z : (c5 : ℤ) < (q : ℤ) := by exact_mod_cast hq5c
  have hc60 : (0 : ℤ) ≤ (c6 : ℤ) := by positivity
  have hc6z : (c6 : ℤ) < (q : ℤ) := by exact_mod_cast hq6c
  have hc70 : (0 : ℤ) ≤ (c7 : ℤ) := by positivity
  have hc7z : (c7 : ℤ) < (q : ℤ) := by exact_mod_cast hq7c
  have hc80 : (0 : ℤ) ≤ (c8 : ℤ) := by positivity
  have hc8z : (c8 : ℤ) < (q : ℤ) := by exact_mod_cast hq8c
  have hc90 : (0 : ℤ) ≤ (c9 : ℤ) := by positivity
  have hc9z : (c9 : ℤ) < (q : ℤ) := by exact_mod_cast hq9c
  have hc100 : (0 : ℤ) ≤ (c10 : ℤ) := by positivity
  have hc10z : (c10 : ℤ) < (q : ℤ) := by exact_mod_cast hq10c
  have hc110 : (0 : ℤ) ≤ (c11 : ℤ) := by positivity
  have hc11z : (c11 : ℤ) < (q : ℤ) := by exact_mod_cast hq11c
  -- ## levels 0 and 1 : the sign pair is exact
  obtain ⟨hg1, hc0eq⟩ := carry_zero hx0 hc00 hc0z hKp0 hKpz
  rw [hg1] at hx1
  obtain ⟨hg2, -⟩ := carry_zero hx1 hc10 hc1z (by linarith) (by linarith)
  -- ## level 2 : the zero pair may borrow once
  rw [hg2] at hx2
  have hg3 := carry_borrow hx2 hc20 hc2z (by linarith) (by linarith)
  have hg3lo : (-1 : ℤ) ≤ g3 := by rcases hg3 with h' | h' <;> omega
  have hg3hi : g3 ≤ 0 := by rcases hg3 with h' | h' <;> omega
  -- ## level 3 : and emits nothing into the guard block
  obtain ⟨hg4, -⟩ := carry_zero hx3 hc30 hc3z (by linarith) (by linarith)
  -- ## levels 4 and 5 : the first guard pair
  rw [hg4] at hx4
  obtain ⟨hg5lo, hg5hi⟩ := carry_range hx4 hq0 hc40 hc4z
    (lo := -1) (hi := (R : ℤ)) (by linarith) (by linarith)
  obtain ⟨hg6, -⟩ := carry_zero hx5 hc50 hc5z (by linarith) (by linarith)
  -- ## levels 6 and 7 : the second guard pair
  rw [hg6] at hx6
  obtain ⟨hg7lo, hg7hi⟩ := carry_range hx6 hq0 hc60 hc6z
    (lo := -1) (hi := (R : ℤ)) (by linarith) (by linarith)
  obtain ⟨hg8, -⟩ := carry_zero hx7 hc70 hc7z (by linarith) (by linarith)
  -- ## levels 8 and 9 : the junk pair and its outgoing carry
  rw [hg8] at hx8
  have hpair : (z : ℤ) * (H : ℤ) + ((q : ℤ) - 1) * (PV : ℤ)
      = (c8 : ℤ) + (q : ℤ) * (c9 : ℤ) + (q : ℤ) ^ 2 * g10 := by
    linear_combination hx8 + (q : ℤ) * hx9
  have hg10_0 : 0 ≤ g10 :=
    pair_carry_nonneg (by linarith) hpair hzH0z hPV0z hc80 hc8z hc90 hc9z
  have hg10_K : g10 ≤ (C.K : ℤ) :=
    pair_carry_le hq2z hpair hzH0z (by linarith) hPV0z hPVKqz hc80 hc90
  -- ## level 10 : the state pair has at most one borrow
  have hg11 := carry_borrow hx10 hc100 hc10z (by linarith) (by linarith)
  have hg11lo : (-1 : ℤ) ≤ g11 := by rcases hg11 with h' | h' <;> omega
  have hg11hi : g11 ≤ 0 := by rcases hg11 with h' | h' <;> omega
  -- ## level 11 : the top emits nothing
  obtain ⟨hg12, hc11eq⟩ := carry_zero hx11 hc110 hc11z (by linarith) (by linarith)
  -- ## the mask and the route residue exclude the state borrow
  have hpc : Bool3 (B11 % q) := by rw [hq3]; exact hb11.mod_pow e'
  have hg11z : g11 = 0 := by
    rcases hg11 with h0 | hm1
    · exact h0
    · exfalso
      have hPCodd : PC = 2 * (B11 % q) + 1 := by
        have hz : (PC : ℤ) = ((2 * (B11 % q) : ℕ) : ℤ) + 1 := by
          rw [← hd11, ← hc11eq, hm1]; ring
        exact_mod_cast hz
      rw [hPCodd] at hcong
      exact state_residue_excludes_borrow hpc hI hIM hcong
  rw [hg11z, add_zero] at hc11eq
  rw [hg11z, mul_zero, add_zero] at hx10
  -- ## the state field, and `C ≤ S H + kappa`
  have hPCd : PC = 2 * (B11 % q) := by rw [← hd11]; exact_mod_cast hc11eq
  have hPCSHK : PC ≤ C.S * H + C.K := by
    have hz : (PC : ℤ) ≤ ((C.S * H + C.K : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hz
  -- ## the improved junk bound kills the outgoing carry
  have hPVq := PV_small hOk hP hS hPCSHK
  have hjcz := junk_carry_zero hOk hP hS hPCSHK
  have hjczZ : (z : ℤ) * (H : ℤ) + ((q : ℤ) - 1) * (PV : ℤ) < (q : ℤ) ^ 2 := by
    have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
      rw [Nat.cast_sub hq1]; push_cast; ring
    have hz : ((z * H + (q - 1) * PV : ℕ) : ℤ) < ((q ^ 2 : ℕ) : ℤ) := by exact_mod_cast hjcz
    push_cast at hz
    rw [hcast] at hz
    exact hz
  have hg10z : g10 = 0 := pair_carry_zero hpair hjczZ hq0 hc80 hc90 hg10_0
  rw [hg10z, add_zero] at hx10
  have hPVzZ : 2 * (PV : ℤ) < (q : ℤ) := by exact_mod_cast hPVq
  have hPCSH : PC ≤ C.S * H := by
    have hz : (PC : ℤ) ≤ ((C.S * H : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hz
  -- ## the junk pair has no borrow either
  have hpcbar : Bool3 (B10 % q) := by rw [hq3]; exact hb10.mod_pow e'
  have hc10n : 2 * (B10 % q) + PC = C.S * H := by
    have hz : ((2 * (B10 % q) : ℕ) : ℤ) + (PC : ℤ) = ((C.S * H : ℕ) : ℤ) := by
      rw [← hd10]; push_cast; linarith
    exact_mod_cast hz
  have hSH2 : C.S * H = 2 * (C.S * heads m u) := by rw [hG.hH]; ring
  have hsumrow : B11 % q + B10 % q = C.S * heads m u := by omega
  have hpcpos : 0 < B11 % q := by
    have hPCpos := hP.PC
    omega
  obtain ⟨aC, hlead⟩ := lead_two_of_bool hpc hpcpos
  rw [← hPCd] at hlead
  have hg9z : g9 = 0 := by
    rcases carry_borrow hx8 hc80 hc8z (by linarith) (by linarith) with h0 | hm1
    · exact h0
    · exfalso
      rw [hg10z, mul_zero, add_zero] at hx9
      have hpv : Bool3 (B9 % q) := by rw [hq3]; exact hb9.mod_pow e'
      have hPVodd : PV = 2 * (B9 % q) + 1 := by
        have hz : (PV : ℤ) = ((2 * (B9 % q) : ℕ) : ℤ) + 1 := by
          rw [← hd9, ← hx9, hm1]; ring
        exact_mod_cast hz
      exact junk_no_borrow100 hOk hP hS hG hSid hpc hpcbar hPCd hsumrow hSm hdm hMS hcong
        hlead (hexp aC hlead) hpv hPVodd
  rw [hg9z, mul_zero, add_zero] at hx8
  rw [hg10z, mul_zero, add_zero, hg9z, add_zero] at hx9
  have hPVzH : PV ≤ z * H := by
    have hz : (PV : ℤ) ≤ ((z * H : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast hz
  -- ## the parity of the route makes the zero field even
  have hKpEven : Kp % 2 = 0 := by
    have hk : Kp = 2 * (B % q) := by rw [← hd0]; exact_mod_cast hc0eq
    omega
  have hPCEven : PC % 2 = 0 := by omega
  have hPVEven : PV % 2 = 0 := by
    have hpv : PV = 2 * (B9 % q) := by rw [← hd9]; exact_mod_cast hx9
    omega
  have hRodd : R % 2 = 1 := by rw [hG.hR, Nat.pow_mod]; norm_num
  have hDEven := D_even_of_route hRodd hSid.hz_odd hPCEven hKpEven hPVEven hS.E21
  -- ## hence the zero pair has no borrow either
  have hHEven : H % 2 = 0 := by rw [hG.hH]; omega
  have hqodd : q % 2 = 1 := by rw [hq3, Nat.pow_mod]; norm_num
  have hg3z : g3 = 0 := by
    rcases hg3 with h0 | hm1
    · exact h0
    · exfalso
      have hz : ((2 * (B2 % q) : ℕ) : ℤ) + (D : ℤ) = (H : ℤ) + (q : ℤ) := by
        rw [← hd2]
        rw [hm1] at hx2
        linarith
      have hn : 2 * (B2 % q) + D = H + q := by exact_mod_cast hz
      omega
  rw [hg3z, mul_zero, add_zero] at hx2
  have hDH : D ≤ H := by
    have hz : (D : ℤ) ≤ (H : ℤ) := by linarith
    exact_mod_cast hz
  -- ## the eight exact halves
  have hbool : ∀ X : ℕ, Bool3 X → Bool3 (X % q) := fun X hX => by
    rw [hq3]; exact hX.mod_pow e'
  subst hg2 hg4 hg3z
  have hKp2 : Kp = 2 * (B % q) := by rw [← hd0]; exact_mod_cast hc0eq
  have hKm2 : Km = 2 * (B1 % q) := by
    have hz : (Km : ℤ) = ((2 * (B1 % q) : ℕ) : ℤ) := by rw [← hd1]; linarith
    exact_mod_cast hz
  have hHD2 : H - D = 2 * (B2 % q) := by
    have hz : ((H - D : ℕ) : ℤ) = ((2 * (B2 % q) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hDH, ← hd2]; linarith
    exact_mod_cast hz
  have hD2 : D = 2 * (B3 % q) := by
    have hz : (D : ℤ) = ((2 * (B3 % q) : ℕ) : ℤ) := by rw [← hd3]; linarith
    exact_mod_cast hz
  have hPV2 : PV = 2 * (B9 % q) := by rw [← hd9]; exact_mod_cast hx9
  have hZV2 : z * H - PV = 2 * (B8 % q) := by
    have hz : ((z * H - PV : ℕ) : ℤ) = ((2 * (B8 % q) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hPVzH, ← hd8]; push_cast; linarith
    exact_mod_cast hz
  have hSC2 : C.S * H - PC = 2 * (B10 % q) := by
    have hz : ((C.S * H - PC : ℕ) : ℤ) = ((2 * (B10 % q) : ℕ) : ℤ) := by
      rw [Nat.cast_sub hPCSH, ← hd10]; push_cast; linarith
    exact_mod_cast hz
  exact ⟨hDH, hPVzH, hPCSH, B % q, B1 % q, B3 % q, B2 % q, B9 % q, B8 % q, B11 % q, B10 % q,
    hbool _ hBool, hbool _ hb1, hbool _ hb3, hbool _ hb2, hbool _ hb9, hbool _ hb8, hpc, hpcbar,
    hKp2, hKm2, hD2, hHD2, hPV2, hZV2, hPCd, hSC2⟩

/-- With the two guard complements supplied by §5, the descent completes `Nonneg100`, and
`fields100` then decodes the twelve doubled fields. -/
theorem nonneg100 (hSid : C.Sidon dm pK)
    (hdm : dm ≤ m) (hSm : C.S < 3 ^ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hI : 0 < C.I) (hIM : 2 * C.I < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hexp : ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm)
    (hA0 : A0 ≤ t) (hA1 : A1 ≤ t) :
    Nonneg100 C H D t A0 A1 PV PC z := by
  obtain ⟨hD, hPV, hPC, -⟩ :=
    nonneg_upper100 hOk hP hS hG hSid hdm hSm hMS hI hIM hcong hexp
  exact ⟨hD, hA0, hA1, hPV, hPC⟩

/-- **The halved state pair.**  The descent also exhibits the state word as twice a Boolean
word whose complement is Boolean and whose sum with it is the fixed state word once per
row.  This is the state-support hypothesis of the one-hot run. -/
theorem state_halves100 (hSid : C.Sidon dm pK)
    (hdm : dm ≤ m) (hSm : C.S < 3 ^ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hI : 0 < C.I) (hIM : 2 * C.I < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hexp : ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm) :
    ∃ pc pcbar, Bool3 pc ∧ Bool3 pcbar ∧ PC = 2 * pc ∧ pc + pcbar = C.S * heads m u := by
  obtain ⟨-, -, hPCle, -, -, -, -, -, -, pc, pcb, -, -, -, -, -, -, hpc, hpcb, -, -, -, -, -, -,
    hPC2, hSC2⟩ := nonneg_upper100 hOk hP hS hG hSid hdm hSm hMS hI hIM hcong hexp
  refine ⟨pc, pcb, hpc, hpcb, hPC2, ?_⟩
  have hSH : C.S * H = 2 * (C.S * heads m u) := by rw [hG.hH]; ring
  omega

end Descent

end Jones1980
