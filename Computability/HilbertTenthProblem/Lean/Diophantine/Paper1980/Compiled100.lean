import Diophantine.Paper1980.Guard100

/-!
# What the compiled program already gives

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §§1–2.  `decode100` was stated with six side
conditions.  Five of them are not extra assumptions at all: they follow from the fixed
grid inequalities of `ROM100.Ok` together with the Sidon layout, and the sixth, the route
residue `(7)`, is the cyclic route read modulo the state modulus.

* `marker_lt_width` — the marker exponent is below the grid exponent, since `g < R`;
* `state_small` and `code_small` — `2 g S < R` and `2 g I < R` divide down to
  `2 S < M` and `2 I < M` for the state modulus `M = R/g`;
* `route_residue100` — from `(RK − g)C = 2gIJ + R(V + hs K⁺ + hz D)` the grid width
  divides `g(C + 2IJ)`, so `M ∣ C + 2I(q − 1)`; as `M ∣ q` this says `C ≡ 2I (mod M)`,
  and `0 < 2I < M` pins the residue.

What is left is the table's exponent layout — a property of the fixed compiled program,
not of any supplied witness — and the decoded-control bound `2q ≤ R D` of §5.
`decode_compiled100` is the decoding under just those two.
-/

namespace Jones1980

open Ternary

section Compiled

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u dm pK amin amax : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

/-- The marker exponent is below the grid exponent. -/
theorem marker_lt_width (hSid : C.Sidon dm pK) : dm < m := by
  have hg := R_gt_g hOk hP hS
  rw [hSid.g_eq, hG.hR] at hg
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hg

/-- The grid factors as marker times state modulus. -/
theorem width_split (hSid : C.Sidon dm pK) : R = 3 ^ dm * 3 ^ (m - dm) := by
  have hdm := marker_lt_width hOk hP hS hG hSid
  rw [hG.hR, ← pow_add]
  congr 1
  omega

/-- `2 S < M`: the fixed state word fits strictly inside one state modulus. -/
theorem state_small (hSid : C.Sidon dm pK) : 2 * C.S < 3 ^ (m - dm) := by
  have hbig := R_big hOk hP hS
  have hKgS := hOk.Zon_gt_KgS
  have hgS : C.g * C.S ≤ (C.K + C.g) * (C.S + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : 2 * (C.g * C.S) < R := by omega
  rw [width_split hOk hP hS hG hSid, hSid.g_eq] at h2
  have hexp : 2 * (3 ^ dm * C.S) = 3 ^ dm * (2 * C.S) := by ring
  rw [hexp] at h2
  exact Nat.lt_of_mul_lt_mul_left h2

/-- `2 I < M`: the cyclic code likewise. -/
theorem code_small (hSid : C.Sidon dm pK) : 2 * C.I < 3 ^ (m - dm) := by
  have h2 := R_gt_two_gI hOk hP hS
  rw [width_split hOk hP hS hG hSid, hSid.g_eq] at h2
  have hexp : 2 * (3 ^ dm * C.I) = 3 ^ dm * (2 * C.I) := by ring
  rw [hexp] at h2
  exact Nat.lt_of_mul_lt_mul_left h2

/-- And the fixed state word is below the grid width. -/
theorem state_lt_width (hSid : C.Sidon dm pK) : C.S < 3 ^ m := by
  have h := state_small hOk hP hS hG hSid
  have hdm := marker_lt_width hOk hP hS hG hSid
  have hmono : (3 : ℕ) ^ (m - dm) ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **(7).**  The cyclic route read modulo the state modulus pins the state field's lowest
row to the cyclic code. -/
theorem route_residue100 (hSid : C.Sidon dm pK) : PC % 3 ^ (m - dm) = 2 * C.I := by
  have hdm := marker_lt_width hOk hP hS hG hSid
  have hIM := code_small hOk hP hS hG hSid
  have hsplit := width_split hOk hP hS hG hSid
  have hg0 : 0 < (3 : ℕ) ^ dm := by positivity
  -- the grid width divides `g (C + 2 I J)`
  have h21 := hS.E21
  have hsum : C.g * (PC + 2 * C.I * J) + R * (PV + C.hs * Kp + C.hz * D) = R * (C.K * PC) := by
    have hexp : C.g * (PC + 2 * C.I * J) = C.g * PC + C.g * C.I * (2 * J) := by ring
    have hexp2 : R * (C.K * PC) = R * C.K * PC := by ring
    omega
  have hRY : R ∣ R * (PV + C.hs * Kp + C.hz * D) := Dvd.intro _ rfl
  have hRX : R ∣ C.g * (PC + 2 * C.I * J) := by
    have hRsum : R ∣ C.g * (PC + 2 * C.I * J) + R * (PV + C.hs * Kp + C.hz * D) := by
      rw [hsum]; exact Dvd.intro _ rfl
    exact (Nat.dvd_add_iff_left hRY).2 hRsum
  have hMX : 3 ^ (m - dm) ∣ PC + 2 * C.I * J := by
    rw [hsplit, hSid.g_eq] at hRX
    exact (mul_dvd_mul_iff_left (by positivity : (3 : ℕ) ^ dm ≠ 0)).1 hRX
  -- and it divides `q`
  have hMq : (3 : ℕ) ^ (m - dm) ∣ q := by
    rw [hG.hq, hG.he]
    have hu3 := hG.hu
    have hmu : m ≤ m * u := Nat.le_mul_of_pos_right _ (by omega)
    exact pow_dvd_pow 3 (by omega)
  -- so it divides `C − 2I`
  obtain ⟨Aq, hAq⟩ := hMX
  obtain ⟨Bq, hBq⟩ := hMq
  have hJ : (J : ℤ) = (q : ℤ) - 1 := by
    have h0 : ((q : ℕ) : ℤ) = ((J + 1 : ℕ) : ℤ) := by exact_mod_cast hS.E0
    push_cast at h0
    linarith
  have hAz : (PC : ℤ) + 2 * (C.I : ℤ) * (J : ℤ)
      = ((3 ^ (m - dm) : ℕ) : ℤ) * (Aq : ℤ) := by exact_mod_cast hAq
  have hBz : (q : ℤ) = ((3 ^ (m - dm) : ℕ) : ℤ) * (Bq : ℤ) := by exact_mod_cast hBq
  rw [hJ] at hAz
  have hz : (PC : ℤ) - 2 * (C.I : ℤ)
      = ((3 ^ (m - dm) : ℕ) : ℤ) * ((Aq : ℤ) - 2 * (C.I : ℤ) * (Bq : ℤ)) := by
    linear_combination hAz - 2 * (C.I : ℤ) * hBz
  have hmod : (PC : ℤ) % ((3 ^ (m - dm) : ℕ) : ℤ)
      = (2 * (C.I : ℤ)) % ((3 ^ (m - dm) : ℕ) : ℤ) :=
    (Int.modEq_iff_dvd.2 ⟨_, hz⟩).symm
  have h2I : (2 * (C.I : ℤ)) % ((3 ^ (m - dm) : ℕ) : ℤ) = 2 * (C.I : ℤ) :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hIM)
  rw [h2I] at hmod
  exact_mod_cast hmod

/-- **The decoding of the counter certificate, from the compiled program alone.**  Only two
facts are assumed beyond the system and the Sidon layout: the table's exponent layout, and
the decoded-control bound `2q ≤ R D` of §5. -/
theorem decode_compiled100 (hSid : C.Sidon dm pK)
    (hexp : ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm)
    (hDq : 2 * q ≤ R * D) :
    Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
    Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
    Doubled e (z * H - PV) ∧ Doubled e PV ∧ Doubled e (C.S * H - PC) ∧ Doubled e PC :=
  decode100 hOk hP hS hG hSid (le_of_lt (marker_lt_width hOk hP hS hG hSid))
    (state_lt_width hOk hP hS hG hSid) (state_small hOk hP hS hG hSid) hOk.I_pos
    (code_small hOk hP hS hG hSid) (route_residue100 hOk hP hS hG hSid) hexp hDq

/-! ### The state column layout -/

/-- The state-column layout of the fixed controller: the cyclic code is the singleton at
the minimum Sidon coordinate, the table's minimal exponent is `dm − amax`, and there are at
least two states, so the minimum coordinate is strictly below the maximum. -/
structure ROM100.Layout (Cr : ROM100) (dm pK amin amax : ℕ) : Prop where
  /-- The cyclic code is the singleton at the minimum Sidon coordinate. -/
  I_eq : Cr.I = 3 ^ amin
  /-- The table's minimal exponent is `dm − amax`, uniquely. -/
  pK_eq : pK = dm - amax
  /-- At least two states. -/
  amin_lt : amin < amax
  /-- The state coordinates lie below the marker. -/
  amax_le : amax ≤ dm

/-- **§4.**  The state field's leading trit is a `2` at the minimum Sidon coordinate: its
lowest row is `2I = 2·3^amin`, and the rest of the word starts at the state modulus. -/
theorem lead_state100 (hSid : C.Sidon dm pK) (hI : C.I = 3 ^ amin) :
    Ternary.Lead amin 2 PC := by
  have hres := route_residue100 hOk hP hS hG hSid
  have hcode := code_small hOk hP hS hG hSid
  have hamin : amin < m - dm := by
    rw [hI] at hcode
    have h1 : (3 : ℕ) ^ amin < 3 ^ (m - dm) := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  obtain ⟨Qt, hQt⟩ : ∃ y, y = PC / 3 ^ (m - dm) := ⟨_, rfl⟩
  have hdm : 3 ^ (m - dm) * Qt + 2 * 3 ^ amin = PC := by
    have hdiv := Nat.div_add_mod PC (3 ^ (m - dm))
    rw [hres, hI, ← hQt] at hdiv
    omega
  have hsplit : (3 : ℕ) ^ amin * 3 ^ (m - dm - amin) = 3 ^ (m - dm) := by
    rw [← pow_add]; congr 1; omega
  refine ⟨2 + 3 ^ (m - dm - amin) * Qt, ?_, ?_⟩
  · calc PC = 3 ^ (m - dm) * Qt + 2 * 3 ^ amin := hdm.symm
      _ = 3 ^ amin * (2 + 3 ^ (m - dm - amin) * Qt) := by rw [← hsplit]; ring
  · obtain ⟨kk, hkk⟩ : ∃ kk, m - dm - amin = kk + 1 := ⟨m - dm - amin - 1, by omega⟩
    have heq : 2 + 3 ^ (m - dm - amin) * Qt = 2 + 3 * (3 ^ kk * Qt) := by
      rw [hkk, pow_succ]; ring
    rw [heq]
    omega

/-- **§4.**  Hence the table's exponent layout: `pK + aC = (dm − amax) + amin < dm`. -/
theorem exponent_layout100 (hSid : C.Sidon dm pK) (hLay : C.Layout dm pK amin amax) :
    ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm := by
  intro aC hlead
  have hmin := lead_state100 hOk hP hS hG hSid hLay.I_eq
  have haC : aC = amin := (hlead.unique hmin (by norm_num) (by norm_num)).1
  have h1 := hLay.amin_lt
  have h2 := hLay.amax_le
  rw [haC, hLay.pK_eq]
  omega

/-- **The counter certificate decoded from the fixed program.**  Beyond the system and the
compiled controller's layout, the only remaining input is the decoded-control bound
`2q ≤ R D` of §5. -/
theorem decode_layout100 (hSid : C.Sidon dm pK) (hLay : C.Layout dm pK amin amax)
    (hDq : 2 * q ≤ R * D) :
    Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
    Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
    Doubled e (z * H - PV) ∧ Doubled e PV ∧ Doubled e (C.S * H - PC) ∧ Doubled e PC :=
  decode_compiled100 hOk hP hS hG hSid (exponent_layout100 hOk hP hS hG hSid hLay) hDq

end Compiled

end Jones1980
