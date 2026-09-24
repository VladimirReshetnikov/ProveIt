import Diophantine.Paper1980.LeadingTrit
import Diophantine.Paper1980.Fields100

/-!
# The borrow exclusions of the counter route

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §§3–4.  Three arguments rule out the three
ways a conceptual field of `(1)` could have borrowed.  Each is stated here in the
elementary form the note uses, with the surrounding carry bookkeeping supplied as
hypotheses.

* **The state pair.**  A borrow would make the upper field `C − 1`, so `C = 2c + 1` for a
  Boolean `c`.  But then the residue of `C` modulo any power of three is odd or zero,
  whereas the cyclic route forces it to be the strictly positive even `2I`.
  This is `state_residue_excludes_borrow`.

* **The junk pair.**  The fixed table has a unique minimal exponent with coefficient one,
  so `K` is `1`-led; the doubled state word `C` is `2`-led; hence `KC` is `2`-led at a
  position strictly below the marker exponent `d`.  Every other term of the route is
  divisible by `3^d`, so `V` inherits that leading `2` (`lead_of_route`).  A borrow would
  make `V = 2v + 1` for a Boolean `v`, which is `1`-led — impossible
  (`junk_pair_no_borrow`).

* **The zero pair.**  With `C`, `Kplus` and `V` even and `R`, `hz` odd, the parity of the
  route forces `D` even (`D_even_of_route`); an odd normalized field is then excluded by
  the doubled mask (`Ternary.chunk_step_even`).

The surrounding carry analysis of §3 — the bound on the incoming carry `kappa` of the
state pair, its vanishing, and the absence of outgoing carries from the two guard pairs —
is the descent of `Carry100.lean`, which feeds these theorems their hypotheses and reaches
three of the five statements of `Nonneg100`.
-/

namespace Jones1980

open Ternary

/-! ### The state pair -/

/-- **§3.**  A borrowed state pair would make `C = 2c + 1` with `c` Boolean, and then the
residue of `C` modulo a power of three is odd or zero.  The cyclic route makes it the
strictly positive even `2I`, so there is no borrow. -/
theorem state_residue_excludes_borrow {c I k : ℕ} (hc : Bool3 c)
    (hI : 0 < I) (hIM : 2 * I < 3 ^ k) (h : (2 * c + 1) % 3 ^ k = 2 * I) : False := by
  have hdm := Nat.div_add_mod c (3 ^ k)
  have hx : 3 ^ k * (2 * (c / 3 ^ k)) = 2 * (3 ^ k * (c / 3 ^ k)) := by ring
  have hsplit : 2 * c + 1 = 3 ^ k * (2 * (c / 3 ^ k)) + (2 * (c % 3 ^ k) + 1) := by omega
  have hres : (2 * c + 1) % 3 ^ k = (2 * (c % 3 ^ k) + 1) % 3 ^ k := by
    rw [hsplit, Nat.mul_add_mod]
  have hle := hc.mod_le_rep k
  have hrep := two_mul_rep_add_one k
  rcases Nat.lt_or_ge (2 * (c % 3 ^ k) + 1) (3 ^ k) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hres
    omega
  · have hfull : 2 * (c % 3 ^ k) + 1 = 3 ^ k := by omega
    rw [hfull, Nat.mod_self] at hres
    omega

/-! ### The junk pair -/

/-- **§4.**  The route `KC = g·Next + V + hs·Kplus + hz·D`, with every term but `KC` and
`V` divisible by the marker `3^d`, transfers the leading trit of `KC` to `V`.  The
fixed table is `1`-led and the doubled state word is `2`-led, so `V` is `2`-led at
`p = pK + a < d`. -/
theorem lead_of_route {K C V Next Kp D pK a d g hs hz : ℕ}
    (hK : Lead pK 1 K) (hC : Lead a 2 C) (hlt : pK + a < d)
    (hg : 3 ^ d ∣ g) (hhs : 3 ^ d ∣ hs) (hhz : 3 ^ d ∣ hz)
    (hroute : K * C = g * Next + V + hs * Kp + hz * D) :
    Lead (pK + a) 2 V := by
  have hdvd : (3 : ℕ) ^ (pK + a + 1) ∣ 3 ^ d := pow_dvd_pow 3 (by omega)
  obtain ⟨G, hG⟩ : (3 : ℕ) ^ (pK + a + 1) ∣ g * Next + hs * Kp + hz * D :=
    Nat.dvd_add (Nat.dvd_add (Dvd.dvd.mul_right (hdvd.trans hg) _)
      (Dvd.dvd.mul_right (hdvd.trans hhs) _)) (Dvd.dvd.mul_right (hdvd.trans hhz) _)
  have hsplit : K * C = 3 ^ (pK + a + 1) * G + V := by omega
  have hmod : V % 3 ^ (pK + a + 1) = (K * C) % 3 ^ (pK + a + 1) := by
    rw [hsplit, Nat.mul_add_mod]
  exact (hK.mul hC).of_modEq hmod

/-- **§4.**  Hence the junk pair cannot have borrowed: its upper field would be the
`1`-led odd successor of a Boolean word, while the route makes it `2`-led. -/
theorem junk_pair_no_borrow {K C Next Kp D v pK a d g hs hz : ℕ}
    (hK : Lead pK 1 K) (hC : Lead a 2 C) (hlt : pK + a < d)
    (hg : 3 ^ d ∣ g) (hhs : 3 ^ d ∣ hs) (hhz : 3 ^ d ∣ hz) (hv : Bool3 v)
    (hroute : K * C = g * Next + (2 * v + 1) + hs * Kp + hz * D) : False :=
  Lead.not_two_odd hv (lead_of_route hK hC hlt hg hhs hhz hroute)

/-! ### The zero pair -/

theorem odd_mul_mod_two {a b : ℕ} (ha : a % 2 = 1) : a * b % 2 = b % 2 := by
  rw [Nat.mul_mod, ha, one_mul]
  omega

/-- **§4.**  With `C`, `Kplus` and `V` even and `R`, `hz` odd, the parity of the cyclic
route `(RK − g)C = 2gIJ + R(V + hs·Kplus + hz·D)` forces `D` even. -/
theorem D_even_of_route {R K g I J C V Kp D hs hz : ℕ}
    (hR : R % 2 = 1) (hhz : hz % 2 = 1) (hC : C % 2 = 0) (hKp : Kp % 2 = 0) (hV : V % 2 = 0)
    (hroute : R * K * C = g * C + g * I * (2 * J) + R * (V + hs * Kp + hz * D)) :
    D % 2 = 0 := by
  have hA : R * K * C % 2 = 0 := by rw [Nat.mul_mod, hC]; omega
  have hB : g * C % 2 = 0 := by rw [Nat.mul_mod, hC]; omega
  have hC1 : g * I * (2 * J) % 2 = 0 := by
    rw [show g * I * (2 * J) = 2 * (g * I * J) by ring]
    omega
  have hD1 : R * (V + hs * Kp + hz * D) % 2 = 0 := by omega
  rw [odd_mul_mod_two hR] at hD1
  have hE : hs * Kp % 2 = 0 := by rw [Nat.mul_mod, hKp]; omega
  have hF : hz * D % 2 = 0 := by omega
  rwa [odd_mul_mod_two hhz] at hF

/-! ### The first row of the state word -/

/-- Two Boolean words whose sum is `S` on the lowest row split that row between them:
digits `0/1` cannot carry. -/
theorem bool_pair_first_row {c cbar S m T : ℕ} (hc : Bool3 c) (hcb : Bool3 cbar)
    (hS : S < 3 ^ m) (h : c + cbar = S + 3 ^ m * T) :
    c % 3 ^ m + cbar % 3 ^ m = S := by
  have hrep := two_mul_rep_add_one m
  have h1 := hc.mod_le_rep m
  have h2 := hcb.mod_le_rep m
  have hdc := Nat.div_add_mod c (3 ^ m)
  have hdb := Nat.div_add_mod cbar (3 ^ m)
  have hx : 3 ^ m * (c / 3 ^ m) + 3 ^ m * (cbar / 3 ^ m) = 3 ^ m * (c / 3 ^ m + cbar / 3 ^ m) := by
    ring
  have hsum : c % 3 ^ m + cbar % 3 ^ m + 3 ^ m * (c / 3 ^ m + cbar / 3 ^ m) = S + 3 ^ m * T := by
    omega
  have hlt : c % 3 ^ m + cbar % 3 ^ m < 3 ^ m := by omega
  have hmod : (c % 3 ^ m + cbar % 3 ^ m) % 3 ^ m = S % 3 ^ m := by
    rw [← Nat.add_mul_mod_self_left (c % 3 ^ m + cbar % 3 ^ m) (3 ^ m)
      (c / 3 ^ m + cbar / 3 ^ m), hsum, Nat.add_mul_mod_self_left]
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hS] at hmod
  exact hmod

/-- **§4.**  Halving the state pair: both halves are Boolean and their sum is `S` times
the row-head word, so the lowest row of the state word is at most `2S`. -/
theorem state_first_row_le {c cbar S m u : ℕ} (hc : Bool3 c) (hcb : Bool3 cbar)
    (hS : S < 3 ^ m) (hu : 1 ≤ u) (h : c + cbar = S * heads m u) :
    2 * (c % 3 ^ m) ≤ 2 * S := by
  have hh : heads m u = 1 + 3 ^ m * heads m (u - 1) := by
    conv_lhs => rw [show u = (u - 1) + 1 by omega]
    exact heads_succ' m (u - 1)
  have h' : c + cbar = S + 3 ^ m * (S * heads m (u - 1)) := by
    rw [h, hh]; ring
  have := bool_pair_first_row hc hcb hS h'
  omega

/-- **§4.**  With the row bound `2S` and the route residue `2I` modulo the state modulus
`M = R/g`, the lowest row of the state word is exactly `2I`. -/
theorem state_first_row_eq {PC I M R S : ℕ} (hMR : M ∣ R) (hrow : PC % R ≤ 2 * S)
    (h2SM : 2 * S < M) (hcong : PC % M = 2 * I) : PC % R = 2 * I := by
  have h1 : PC % R % M = PC % M := Nat.mod_mod_of_dvd _ hMR
  rw [hcong] at h1
  rw [Nat.mod_eq_of_lt (by omega)] at h1
  exact h1

/-- **§4.**  The first row `2I` makes the next-state word an integer, and the cyclic route
divides by the grid width into `KC = g·Next + V + hs·Kplus + hz·D`. -/
theorem route_divided {R K g I J q PC PV Kp D hs hz : ℕ} (hR : 0 < R)
    (hq : R ∣ q) (hJ : q = J + 1) (hrow : PC % R = 2 * I)
    (hroute : R * K * PC = g * PC + g * I * (2 * J) + R * (PV + hs * Kp + hz * D)) :
    K * PC = g * (PC / R + 2 * I * (q / R)) + PV + hs * Kp + hz * D := by
  obtain ⟨q', hq'⟩ := hq
  have hdm : R * (PC / R) + PC % R = PC := Nat.div_add_mod PC R
  have hnext : PC + 2 * I * J = R * (PC / R + 2 * I * q') := by
    have hexp : R * (PC / R + 2 * I * q') = R * (PC / R) + 2 * I * (R * q') := by ring
    rw [hexp, ← hq']
    have : 2 * I * q = 2 * I * J + 2 * I := by rw [hJ]; ring
    omega
  have hcancel : R * (K * PC)
      = R * (g * (PC / R + 2 * I * q') + PV + hs * Kp + hz * D) := by
    have hg : g * PC + g * I * (2 * J) = g * (PC + 2 * I * J) := by ring
    calc R * (K * PC) = R * K * PC := by ring
      _ = g * PC + g * I * (2 * J) + R * (PV + hs * Kp + hz * D) := hroute
      _ = g * (PC + 2 * I * J) + R * (PV + hs * Kp + hz * D) := by rw [hg]
      _ = g * (R * (PC / R + 2 * I * q')) + R * (PV + hs * Kp + hz * D) := by rw [hnext]
      _ = R * (g * (PC / R + 2 * I * q') + PV + hs * Kp + hz * D) := by ring
  have hqR : q / R = q' := by rw [hq', Nat.mul_div_cancel_left _ hR]
  rw [hqR]
  exact Nat.eq_of_mul_eq_mul_left hR hcancel


/-! ### The Sidon layout and the junk-pair exclusion in the system -/

/-- The Sidon layout of the compiled table (§1, (4)): the marker is `g = 3^dm`, the sign
and zero ports sit above it, and the table's minimal exponent is unique with coefficient
one, so `K` is `1`-led. -/
structure ROM100.Sidon (Cr : ROM100) (dm pK : ℕ) : Prop where
  /-- The marker `g = 3^dm`. -/
  g_eq : Cr.g = 3 ^ dm
  /-- The sign port `hs = 3^(dm + bs)`. -/
  hs_eq : ∃ bs, Cr.hs = 3 ^ (dm + bs)
  /-- The zero-request port `hz = 3^(dm + bz)`. -/
  hz_eq : ∃ bz, Cr.hz = 3 ^ (dm + bz)
  /-- The table has a unique minimal exponent, with coefficient one. -/
  K_lead : Ternary.Lead pK 1 Cr.K

theorem ROM100.Sidon.hs_dvd {Cr : ROM100} {dm pK : ℕ} (h : Cr.Sidon dm pK) :
    3 ^ dm ∣ Cr.hs := by
  obtain ⟨bs, hbs⟩ := h.hs_eq
  rw [hbs, pow_add]
  exact ⟨3 ^ bs, rfl⟩

theorem ROM100.Sidon.hz_dvd {Cr : ROM100} {dm pK : ℕ} (h : Cr.Sidon dm pK) :
    3 ^ dm ∣ Cr.hz := by
  obtain ⟨bz, hbz⟩ := h.hz_eq
  rw [hbz, pow_add]
  exact ⟨3 ^ bz, rfl⟩

/-- The zero-request port is a power of three, hence odd. -/
theorem ROM100.Sidon.hz_odd {Cr : ROM100} {dm pK : ℕ} (h : Cr.Sidon dm pK) :
    Cr.hz % 2 = 1 := by
  obtain ⟨bz, hbz⟩ := h.hz_eq
  rw [hbz, Nat.pow_mod]
  norm_num

/-- Doubling commutes with taking a chunk of a Boolean word. -/
theorem Ternary.two_mul_mod {B m : ℕ} (hB : Bool3 B) : 2 * B % 3 ^ m = 2 * (B % 3 ^ m) := by
  have hrep := two_mul_rep_add_one m
  have hle := hB.mod_le_rep m
  have hdm := Nat.div_add_mod B (3 ^ m)
  have hx : 3 ^ m * (2 * (B / 3 ^ m)) = 2 * (3 ^ m * (B / 3 ^ m)) := by ring
  have hsplit : 2 * B = 2 * (B % 3 ^ m) + 3 ^ m * (2 * (B / 3 ^ m)) := by omega
  rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

section Junk

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u dm pK pc pcbar aC : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

/-- **§4, assembled.**  Halve the state pair, read its lowest row against the route
residue, divide the route by the grid width, and the junk field inherits the leading `2`
of `K C`.  The hypotheses left open are exactly the carry bookkeeping of §3 (that the
state pair is the actual doubled pair `2 pc`, `2 pcbar`) and the exponent layout
`pK + aC < dm` of the fixed table. -/
theorem junk_lead100 (hSid : C.Sidon dm pK)
    (hpc : Bool3 pc) (hpcb : Bool3 pcbar) (hPCeq : PC = 2 * pc)
    (hsum : pc + pcbar = C.S * heads m u) (hSm : C.S < 3 ^ m)
    (hdm : dm ≤ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hlead : Ternary.Lead aC 2 PC) (hlt : pK + aC < dm) :
    Ternary.Lead (pK + aC) 2 PV := by
  have hu1 : 1 ≤ u := by have := hG.hu; omega
  have hrow : PC % R ≤ 2 * C.S := by
    rw [hG.hR, hPCeq, Ternary.two_mul_mod hpc]
    exact state_first_row_le hpc hpcb hSm hu1 hsum
  have hMR : (3 : ℕ) ^ (m - dm) ∣ R := by rw [hG.hR]; exact pow_dvd_pow 3 (by omega)
  have hrowI : PC % R = 2 * C.I := state_first_row_eq hMR hrow hMS hcong
  have hRq : R ∣ q := R_dvd_q hOk hP hS hG
  have hR0 : 0 < R := hP.R
  have hdiv := route_divided hR0 hRq hS.E0 hrowI hS.E21
  exact lead_of_route hSid.K_lead hlead hlt (by rw [hSid.g_eq]) hSid.hs_dvd hSid.hz_dvd hdiv

/-- **§4.**  Hence the junk pair has not borrowed: its upper field is not the odd successor
of a Boolean word. -/
theorem junk_no_borrow100 (hSid : C.Sidon dm pK)
    (hpc : Bool3 pc) (hpcb : Bool3 pcbar) (hPCeq : PC = 2 * pc)
    (hsum : pc + pcbar = C.S * heads m u) (hSm : C.S < 3 ^ m)
    (hdm : dm ≤ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hlead : Ternary.Lead aC 2 PC) (hlt : pK + aC < dm)
    {pv : ℕ} (hpv : Bool3 pv) (hPV : PV = 2 * pv + 1) : False := by
  have h := junk_lead100 hOk hP hS hG hSid hpc hpcb hPCeq hsum hSm hdm hMS hcong hlead hlt
  rw [hPV] at h
  exact Ternary.Lead.not_two_odd hpv h

end Junk


/-! ### The improved bound on the junk field and the vanishing carry -/

section Carry

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)

include hOk hP hS

/-- `8 K S + 9 ≤ R`: the fixed grid is wide enough for the table and the state word. -/
theorem eight_KS_lt_R : 8 * (C.K * C.S) + 9 ≤ R := by
  have hbig := R_big hOk hP hS
  have hKS : C.K * C.S ≤ (C.K + C.g) * (C.S + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hZ := hOk.Zon_gt_KgS
  omega

/-- `4 K S H < q`: the table-scaled state word stays below a quarter of the base. -/
theorem KSH_small : 4 * (C.K * (C.S * H)) < q := by
  have hhead := head_eq100 hOk hP hS
  have hKS := eight_KS_lt_R hOk hP hS
  have hq : 1 ≤ q := hP.q
  have hmul : (8 * (C.K * C.S) + 9) * H ≤ R * H := Nat.mul_le_mul_right _ hKS
  have hexp : (8 * (C.K * C.S) + 9) * H = 8 * (C.K * (C.S * H)) + 9 * H := by ring
  have hsub : H * (R - 1) = R * H - H := by rw [Nat.mul_sub, mul_one, mul_comm]
  have hRH : H ≤ R * H := Nat.le_mul_of_pos_left _ hP.R
  omega

/-- `27 K² < q`: the table is small compared with the cube of the grid width. -/
theorem K_sq_small : 27 * C.K ^ 2 < q := by
  have hbig := R_big hOk hP hS
  have hZ := hOk.Zon_ge
  have hR27 : 27 ≤ R := by omega
  have hK := R_gt_K hOk hP hS
  have hq3 : R ^ 3 ≤ q := by
    have h1 := hS.E1
    have h19 := hS.E19
    have hv : 1 ≤ v := hP.v
    calc R ^ 3 = R ^ 3 * 1 := by ring
      _ ≤ R ^ 3 * v := Nat.mul_le_mul_left _ hv
      _ = q := by rw [h1, h19]
  have hK2 : C.K ^ 2 < R ^ 2 := Nat.pow_lt_pow_left hK (by norm_num)
  have hR3 : 27 * R ^ 2 ≤ R ^ 3 := by
    calc 27 * R ^ 2 ≤ R * R ^ 2 := Nat.mul_le_mul_right _ hR27
      _ = R ^ 3 := by ring
  omega

/-- **(11).**  Once the state field is bounded by `S H + K`, the junk field is below half
the base: `V < K C ≤ K S H + K² < q/4 + q/27`. -/
theorem PV_small (hPC : PC ≤ C.S * H + C.K) : 2 * PV < q := by
  have h1 := PV_lt hOk hP hS
  have h2 : C.K * PC ≤ C.K * (C.S * H) + C.K ^ 2 := by
    have : C.K * PC ≤ C.K * (C.S * H + C.K) := Nat.mul_le_mul_left _ (by omega)
    nlinarith [this]
  have h3 := KSH_small hOk hP hS
  have h4 := K_sq_small hOk hP hS
  omega

/-- **(9).**  Hence the junk pair emits no carry into the state pair: its two-field value
`z H + (q − 1) V` is below `q²`. -/
theorem junk_carry_zero (hPC : PC ≤ C.S * H + C.K) : z * H + (q - 1) * PV < q ^ 2 := by
  have h1 := PV_small hOk hP hS hPC
  have h2 := zH_small hOk hP hS
  have hq : 1 ≤ q := hP.q
  have hz : (q - 1) * PV ≤ (q - 1) * PV := le_refl _
  have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub hq]; push_cast; ring
  have hgoal : ((z * H + (q - 1) * PV : ℕ) : ℤ) < ((q ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [hcast]
    have h1' : 2 * (PV : ℤ) < (q : ℤ) := by exact_mod_cast h1
    have h2' : 4 * ((z : ℤ) * H) < (q : ℤ) := by exact_mod_cast h2
    have hq' : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
    have hPV0 : (0 : ℤ) ≤ (PV : ℤ) := by positivity
    have hzH0 : (0 : ℤ) ≤ (z : ℤ) * H := by positivity
    nlinarith [h1', h2', hq', hPV0, hzH0]
  exact_mod_cast hgoal

end Carry

end Jones1980
