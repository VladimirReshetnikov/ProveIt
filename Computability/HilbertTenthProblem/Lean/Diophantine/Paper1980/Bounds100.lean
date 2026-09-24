import Diophantine.Paper1980.Geometry100

/-!
# The pre-typing bounds of the 100-operation counter system

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §2.  With the compiled ROM contract `ROM100.Ok`
(the grid numeral `Zon` above `4S`, `g(I+1)`, `(K+g)(S+1)` and `81`; the spacing `B₀ ≥ 9`;
the marker `g` a power of three; `K < hz`), positivity and the outer equations give, before
any digit interpretation,

    R ≥ 8·Zon + 9,   H(R − 1) = 2(q − 1),
    16 S H < q,   4 z H < q,   4(A₀ + A₁) < q,
    P ≤ q¹² − 1,   P ≥ q¹⁰((q − 1)C + S H),   hence   C ≤ q.

With the radix geometry the cyclic route read modulo `R` gives `C ≡ 2I (mod R/g)` with
`0 < 2I < R/g`, which excludes the endpoint `C = q` and leaves `C < q`; the route itself
then bounds the zero word and the junk, `D < C` and `V < K C`.
-/

namespace Jones1980

open Ternary

/-- The contract satisfied by the compiled ROM constants. -/
structure ROM100.Ok (C : ROM100) : Prop where
  B0_ge : 9 ≤ C.B0
  Zon_ge : 81 ≤ C.Zon
  Zon_gt_S : 4 * C.S < C.Zon
  Zon_gt_gI : C.g * (C.I + 1) < C.Zon
  Zon_gt_KgS : (C.K + C.g) * (C.S + 1) < C.Zon
  S_pos : 0 < C.S
  I_pos : 0 < C.I
  g_pow : ∃ d, C.g = 3 ^ d
  K_lt_hz : C.K < C.hz
  Zon_gt_ports : 8 * (C.hs + C.hz) < C.Zon
  K_pos : 0 < C.K

section Bounds

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)

include hOk hP hS

/-! ### The grid -/

theorem R_big : 8 * C.Zon + 9 ≤ R := R_ge100 hP hS hOk.B0_ge

theorem R_gt_K : C.K < R := by
  have h1 := hOk.Zon_gt_KgS
  have h2 : C.K ≤ (C.K + C.g) * (C.S + 1) :=
    le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (by omega))
  have := R_big hOk hP hS
  omega

theorem R_gt_g : C.g < R := by
  have h1 := hOk.Zon_gt_KgS
  have h2 : C.g ≤ (C.K + C.g) * (C.S + 1) :=
    le_trans (Nat.le_add_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
  have := R_big hOk hP hS
  omega

theorem R_gt_two_gI : 2 * (C.g * C.I) < R := by
  have h1 := hOk.Zon_gt_gI
  have h2 : C.g * C.I ≤ C.g * (C.I + 1) := Nat.mul_le_mul_left _ (by omega)
  have := R_big hOk hP hS
  omega

theorem R_gt_S : 32 * C.S < R := by
  have h1 := hOk.Zon_gt_S
  have := R_big hOk hP hS
  omega

/-- The whole fixed ROM fits strictly inside one row of the grid. -/
theorem hz_lt_R : C.hz < R := by
  have hbig := R_big hOk hP hS
  have hports := hOk.Zon_gt_ports
  omega

/-- **The table times the state word fits inside a row.**  This is the routing note's
condition `W > K S`, which is what keeps one row's table output from reaching the next
row's columns. -/
theorem KS_lt_R : C.K * C.S < R := by
  have hbig := R_big hOk hP hS
  have hKgS := hOk.Zon_gt_KgS
  have hle : C.K * C.S ≤ (C.K + C.g) * (C.S + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- And so does the marker times the state word: the target columns of a row stay inside
that row. -/
theorem gS_lt_R : C.g * C.S < R := by
  have hbig := R_big hOk hP hS
  have hKgS := hOk.Zon_gt_KgS
  have hle : C.g * C.S ≤ (C.K + C.g) * (C.S + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- `H(R − 1) = 2(q − 1)`. -/
theorem head_eq100 : H * (R - 1) = 2 * (q - 1) := by
  have h2 := hS.E2
  have h0 := hS.E0
  have hq := hP.q
  have hR := hP.R
  have hsub : H * (R - 1) = H * R - H := by rw [Nat.mul_sub, mul_one]
  omega

/-! ### The three width estimates -/

/-- `16 S H < q`. -/
theorem SH_small : 16 * (C.S * H) < q := by
  have hhd := head_eq100 hOk hP hS
  have hS32 := R_gt_S hOk hP hS
  have hq := hP.q
  have h1 : H * (32 * C.S) ≤ H * (R - 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : H * (32 * C.S) = 32 * (C.S * H) := by ring
  omega

/-- `4 z H < q`. -/
theorem zH_small : 4 * (z * H) < q := by
  have hhd := head_eq100 hOk hP hS
  have h4 := hS.E4
  have hB := hOk.B0_ge
  have hZon := hOk.Zon_ge
  have hq := hP.q
  have hz := hP.z
  have h8z : 8 * z < R - 1 := by
    have h : 8 * (C.Zon + z) ≤ (C.B0 - 1) * (C.Zon + z) := Nat.mul_le_mul_right _ (by omega)
    omega
  have h1 : H * (8 * z) ≤ H * (R - 1) := Nat.mul_le_mul_left _ (by omega)
  have h2 : H * (8 * z) = 8 * (z * H) := by ring
  omega

/-- `4(A₀ + A₁) < q`. -/
theorem track_small : 4 * (A0 + A1) < q := by
  have h6 := hS.E6
  have h3 := hS.E3
  have hhd := head_eq100 hOk hP hS
  have hW := hS.E19
  have hR := R_big hOk hP hS
  have hZon := hOk.Zon_ge
  have hq0 : 0 < q := hP.q
  have hR656 : 656 ≤ R - 1 := by omega
  have hW2 : 2 ≤ W := by
    rw [hW]
    calc 2 ≤ 657 := by norm_num
      _ ≤ R := by omega
      _ ≤ R ^ 3 := Nat.le_self_pow (by norm_num) R
  have hAW : (A0 + A1) * (W - 1) + (A0 + A1) = W * (A0 + A1) := by
    have hle : A0 + A1 ≤ (A0 + A1) * W := Nat.le_mul_of_pos_right _ (by omega)
    have hcm : (A0 + A1) * W = W * (A0 + A1) := mul_comm _ _
    rw [Nat.mul_sub, mul_one]
    omega
  have hKmH : W * Km ≤ W * H := Nat.mul_le_mul_left _ (by omega)
  have hexp : W * (A0 + A1 + Kp) = W * (A0 + A1) + W * Kp := by ring
  have hA : (A0 + A1) * (W - 1) ≤ W * H := by omega
  have hmul : (A0 + A1) * (W - 1) * (R - 1) ≤ W * (2 * (q - 1)) := by
    calc (A0 + A1) * (W - 1) * (R - 1) ≤ W * H * (R - 1) := Nat.mul_le_mul_right _ hA
      _ = W * (H * (R - 1)) := by ring
      _ = W * (2 * (q - 1)) := by rw [hhd]
  by_contra hcon
  push_neg at hcon
  have hstep : (W - 1) * (R - 1) * q ≤ (8 * W) * q := by
    calc (W - 1) * (R - 1) * q ≤ (W - 1) * (R - 1) * (4 * (A0 + A1)) :=
          Nat.mul_le_mul_left _ hcon
      _ = 4 * ((A0 + A1) * (W - 1) * (R - 1)) := by ring
      _ ≤ 4 * (W * (2 * (q - 1))) := Nat.mul_le_mul_left _ hmul
      _ = 8 * (W * (q - 1)) := by ring
      _ ≤ 8 * (W * q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      _ = (8 * W) * q := by ring
  have hfinal : (W - 1) * (R - 1) ≤ 8 * W := Nat.le_of_mul_le_mul_right hstep hq0
  have hbig : 656 * (W - 1) ≤ (W - 1) * (R - 1) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hR656
  omega

/-! ### The packed word and the state field -/

/-- The packed word lies below `q¹²`. -/
theorem packed_le :
    J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))))
      + (q ^ 2 + 1) * (H + q ^ 4 * t) + q ^ 8 * (H * (z + q ^ 2 * C.S)) + 1 ≤ q ^ 12 := by
  have h8 := hS.E8
  have hr := r_lt100 hP hS
  omega

/-- The top contribution of the packed word. -/
theorem packed_ge :
    q ^ 10 * (J * PC + C.S * H)
      ≤ J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))))
        + (q ^ 2 + 1) * (H + q ^ 4 * t) + q ^ 8 * (H * (z + q ^ 2 * C.S)) := by
  have l1 : q ^ 2 * PC ≤ PV + q ^ 2 * PC := Nat.le_add_left _ _
  have l2 : q ^ 2 * (q ^ 2 * PC) ≤ A1 + q ^ 2 * (PV + q ^ 2 * PC) :=
    le_trans (Nat.mul_le_mul_left _ l1) (Nat.le_add_left _ _)
  have l3 : q ^ 2 * (q ^ 2 * (q ^ 2 * PC)) ≤ A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)) :=
    le_trans (Nat.mul_le_mul_left _ l2) (Nat.le_add_left _ _)
  have l4 : q ^ 2 * (q ^ 2 * (q ^ 2 * (q ^ 2 * PC)))
      ≤ D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC))) :=
    le_trans (Nat.mul_le_mul_left _ l3) (Nat.le_add_left _ _)
  have l5 : q ^ 2 * (q ^ 2 * (q ^ 2 * (q ^ 2 * (q ^ 2 * PC))))
      ≤ Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))) :=
    le_trans (Nat.mul_le_mul_left _ l4) (Nat.le_add_left _ _)
  have hX : q ^ 10 * PC
      ≤ Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC)))) := by
    calc q ^ 10 * PC = q ^ 2 * (q ^ 2 * (q ^ 2 * (q ^ 2 * (q ^ 2 * PC)))) := by ring
      _ ≤ _ := l5
  have hJX : J * (q ^ 10 * PC)
      ≤ J * (Km + q ^ 2 * (D + q ^ 2 * (A0 + q ^ 2 * (A1 + q ^ 2 * (PV + q ^ 2 * PC))))) :=
    Nat.mul_le_mul_left _ hX
  have hT : q ^ 8 * (H * (q ^ 2 * C.S)) ≤ q ^ 8 * (H * (z + q ^ 2 * C.S)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))
  have e1 : J * (q ^ 10 * PC) = q ^ 10 * (J * PC) := by ring
  have e2 : q ^ 8 * (H * (q ^ 2 * C.S)) = q ^ 10 * (C.S * H) := by ring
  have e3 : q ^ 10 * (J * PC + C.S * H) = q ^ 10 * (J * PC) + q ^ 10 * (C.S * H) := by ring
  omega

/-- `C ≤ q`. -/
theorem PC_le_q : PC ≤ q := by
  have hle := packed_le hOk hP hS
  have hge := packed_ge hOk hP hS
  have h0 := hS.E0
  have hHS : 1 ≤ C.S * H := Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero (by have := hOk.S_pos; omega) (by have := hP.H; omega))
  by_contra hcon
  push_neg at hcon
  have hJPC : q ^ 2 - 1 ≤ J * PC := by
    have h1 : J * (q + 1) ≤ J * PC := Nat.mul_le_mul_left _ (by omega)
    have h2 : J * (q + 1) = q ^ 2 - 1 := by
      have : q = J + 1 := h0
      subst this
      ring_nf
      omega
    omega
  have hq12 : q ^ 10 * (q ^ 2 - 1) + q ^ 10 = q ^ 12 := by
    have h1 : (1 : ℕ) ≤ q ^ 2 := Nat.one_le_pow _ _ hP.q
    rw [Nat.mul_sub, mul_one]
    have h2 : q ^ 10 * q ^ 2 = q ^ 12 := by rw [← pow_add]
    have h3 : q ^ 10 ≤ q ^ 10 * q ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hmono : q ^ 10 * ((q ^ 2 - 1) + 1) ≤ q ^ 10 * (J * PC + C.S * H) :=
    Nat.mul_le_mul_left _ (by omega)
  have he : q ^ 10 * ((q ^ 2 - 1) + 1) = q ^ 10 * (q ^ 2 - 1) + q ^ 10 := by ring
  omega

/-! ### The cyclic route -/

/-- The route bounds the junk and the zero word: `V + hs·K⁺ + hz·D < K C`. -/
theorem route_bound : PV + C.hs * Kp + C.hz * D < C.K * PC := by
  have h21 := hS.E21
  have hgpos : 0 < C.g := by obtain ⟨d, hd⟩ := hOk.g_pow; rw [hd]; positivity
  have hPC := hP.PC
  have hgPC : 0 < C.g * PC := Nat.mul_pos hgpos hPC
  have e1 : R * C.K * PC = R * (C.K * PC) := by ring
  have hlt : R * (PV + C.hs * Kp + C.hz * D) < R * (C.K * PC) := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- The zero word is below the state word. -/
theorem D_lt_PC : D < PC := by
  have h := route_bound hOk hP hS
  have hK := hOk.K_lt_hz
  have hhz : C.K * PC ≤ C.hz * PC := Nat.mul_le_mul_right _ (by omega)
  have hle : C.hz * D ≤ PV + C.hs * Kp + C.hz * D := by omega
  have hlt : C.hz * D < C.hz * PC := by omega
  exact Nat.lt_of_mul_lt_mul_left hlt

/-- The junk word is below `K C`. -/
theorem PV_lt : PV < C.K * PC := by
  have h := route_bound hOk hP hS
  omega

end Bounds

section Route

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

/-- `R ∣ q`, since `q = R^u` with `u ≥ 3`. -/
theorem R_dvd_q : R ∣ q := by
  have hqRu : q = R ^ u := by rw [hG.hq, hG.he, pow_mul, ← hG.hR]
  rw [hqRu]
  exact dvd_pow_self R (by have := hG.hu; omega)

/-- The route read modulo `R`: the state field cannot reach the endpoint `q`. -/
theorem PC_ne_q : PC ≠ q := by
  intro hPCq
  obtain ⟨qq, hqq⟩ := R_dvd_q hOk hP hS hG
  have h21 := hS.E21
  have h0 := hS.E0
  have hgpos : 0 < C.g := by obtain ⟨d, hd⟩ := hOk.g_pow; rw [hd]; positivity
  have hIpos := hOk.I_pos
  have hGI : 0 < C.g * C.I := Nat.mul_pos hgpos hIpos
  have hGIR := R_gt_two_gI hOk hP hS
  -- the route with the endpoint substituted, collecting the multiples of `R`
  have hJ2 : C.g * C.I * (2 * J) + 2 * (C.g * C.I) = 2 * (C.g * C.I) * (R * qq) := by
    have hq2 : 2 * J + 2 = 2 * q := by omega
    calc C.g * C.I * (2 * J) + 2 * (C.g * C.I) = C.g * C.I * (2 * J + 2) := by ring
      _ = C.g * C.I * (2 * q) := by rw [hq2]
      _ = 2 * (C.g * C.I) * q := by ring
      _ = 2 * (C.g * C.I) * (R * qq) := by rw [hqq]
  have e1 : R * (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D))
      = 2 * (C.g * C.I) * (R * qq) + R * (PV + C.hs * Kp + C.hz * D) := by ring
  have e2 : R * (C.K * PC) = R * C.K * PC := by ring
  have key : C.g * PC + R * (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D))
      = R * (C.K * PC) + 2 * (C.g * C.I) := by omega
  -- with `PC = q = R qq` the left side is a multiple of `R`
  have hgq : C.g * PC = R * (C.g * qq) := by rw [hPCq, hqq]; ring
  have hsum : R * (C.g * qq + (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D)))
      = R * (C.K * PC) + 2 * (C.g * C.I) := by
    have e3 : R * (C.g * qq + (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D)))
        = R * (C.g * qq) + R * (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D)) := by ring
    omega
  have hdvd : R ∣ 2 * (C.g * C.I) := by
    have h1 : R ∣ R * (C.g * qq + (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D))) :=
      Dvd.intro _ rfl
    have h2 : R ∣ R * (C.K * PC) := Dvd.intro _ rfl
    have h3 : 2 * (C.g * C.I)
        = R * (C.g * qq + (2 * (C.g * C.I) * qq + (PV + C.hs * Kp + C.hz * D)))
          - R * (C.K * PC) := by omega
    rw [h3]
    exact Nat.dvd_sub h1 h2
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- `C < q`. -/
theorem PC_lt_q : PC < q := by
  have h1 := PC_le_q hOk hP hS
  have h2 := PC_ne_q hOk hP hS hG
  omega

end Route

end Jones1980
