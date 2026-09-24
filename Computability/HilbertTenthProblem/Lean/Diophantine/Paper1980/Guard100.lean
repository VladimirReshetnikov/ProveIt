import Diophantine.Paper1980.Carry100

/-!
# The guard complements

`EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, §5.  The carry descent of `Carry100.lean` leaves
two of the five statements of `Nonneg100` open: the guard complements `t − A₀` and
`t − A₁`.  The note obtains them from the decoded controller, but only through a single
quantitative consequence of it — that the reconstructed zero-request word `Z = H − D` is
positive forces

    D ≥ 2q/R,

since the last source carries no zero request and every positive return visits the
mandatory marked prefix.  Everything after that is arithmetic in the outer equations:

    6t = (R − 3) D  gives  3 t R ≥ q (R − 3),
    the time equation gives  A (R³ − 1) < R³ H,  and  H (R − 1) = 2(q − 1),

so `A = A₀ + A₁` satisfies `A < 3q/R` while `t ≥ q(R − 3)/(3R)`, and for `R ≥ 27` the
lower bound beats the upper one.  `guard_lt100` is that step, with `2q ≤ R D` as its
hypothesis; `nonneg_full100` then assembles the whole of `Nonneg100`, and
`decode100` runs `fields100` on it.

So the counter route's decoding is now conditional on exactly three things about the
compiled program, none of them about a supplied witness: the Sidon layout of the table,
its exponent layout `pK + aC < dm`, the route residue `C ≡ 2I` modulo the state modulus,
and the decoded-control bound `2q ≤ R D`.
-/

namespace Jones1980

open Ternary

/-- The polynomial inequality behind `R ≥ 27`: the lower bound on the gap beats the upper
bound on the two tracks. -/
theorem guard_poly {R : ℤ} (hR : 27 ≤ R) : 6 * R ^ 4 < (R - 3) * ((R ^ 3 - 1) * (R - 1)) := by
  have h0 : (0 : ℤ) ≤ R := by linarith
  have h4 : (0 : ℤ) ≤ R ^ 4 := by positivity
  have h2 : (0 : ℤ) ≤ R ^ 2 := by positivity
  have hA : 17 * R ^ 4 ≤ R ^ 5 - 10 * R ^ 4 := by nlinarith
  have hB : (0 : ℤ) < 3 * R ^ 3 - R ^ 2 + 4 * R - 3 := by nlinarith
  nlinarith

/-- The abstract form of §5's guard estimate. -/
theorem guard_key {A t D q H R : ℤ}
    (hR : 27 ≤ R) (hq : 1 ≤ q) (hA0 : 0 ≤ A) (ht0 : 0 ≤ t) (hH0 : 0 ≤ H)
    (hT : 6 * t = D * (R - 3)) (hDq : 2 * q ≤ R * D)
    (hH : H * (R - 1) = 2 * (q - 1))
    (hA : A * (R ^ 3 - 1) < R ^ 3 * H) : A < t := by
  by_contra hcon
  push_neg at hcon
  have hR0 : (0 : ℤ) < R := by linarith
  have hq0 : (0 : ℤ) < q := by linarith
  have hRsq : (729 : ℤ) ≤ R ^ 2 := by nlinarith
  have hR31 : (1 : ℤ) ≤ R ^ 3 := by nlinarith
  have hR3nn : (0 : ℤ) ≤ R ^ 3 := by positivity
  have hP : (0 : ℤ) ≤ (R ^ 3 - 1) * (R - 1) := mul_nonneg (by linarith) (by linarith)
  have e1 : 6 * t * R = (R * D) * (R - 3) := by linear_combination R * hT
  have s1 : 2 * q * (R - 3) ≤ 6 * t * R := by nlinarith
  have s2 : q * (R - 3) ≤ 3 * (A * R) := by nlinarith
  have hs3a := mul_lt_mul_of_pos_right hA (show (0 : ℤ) < R - 1 by linarith)
  have hs3b : R ^ 3 * H * (R - 1) = R ^ 3 * (2 * (q - 1)) := by rw [← hH]; ring
  have s3 : A * ((R ^ 3 - 1) * (R - 1)) < 2 * R ^ 3 * q := by nlinarith [hs3a, hs3b, hR3nn]
  have hmul1 := mul_le_mul_of_nonneg_right s2 hP
  have hmul2 := mul_lt_mul_of_pos_left s3 (show (0 : ℤ) < 3 * R by linarith)
  have hpoly := guard_poly hR
  nlinarith [hmul1, hmul2, hpoly, hq0]

section Guard

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u dm pK : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)

include hOk hP hS

/-- **§5.**  Once the decoded controller has supplied `2q ≤ R D`, the two tracks are
strictly below the gap, so both guard complements are positive. -/
theorem guard_lt100 (hDq : 2 * q ≤ R * D) : A0 + A1 < t := by
  have hRbig := R_big hOk hP hS
  have hZon := hOk.Zon_ge
  have hR27 : 27 ≤ R := by omega
  have hE3 := hS.E3
  have hx1 : 1 ≤ x := hP.x
  -- the three outer identities, in ℤ
  have hTz : 6 * (t : ℤ) = (D : ℤ) * ((R : ℤ) - 3) := by
    have h5 : ((6 * t + 3 * D : ℕ) : ℤ) = ((D * R : ℕ) : ℤ) := by exact_mod_cast hS.E5
    push_cast at h5
    linarith
  have hHz : (H : ℤ) * ((R : ℤ) - 1) = 2 * ((q : ℤ) - 1) := by
    have h2 : ((H * R : ℕ) : ℤ) = ((H + 2 * J : ℕ) : ℤ) := by exact_mod_cast hS.E2
    have h0 : ((q : ℕ) : ℤ) = ((J + 1 : ℕ) : ℤ) := by exact_mod_cast hS.E0
    push_cast at h2 h0
    linarith
  have hAz : ((A0 : ℤ) + (A1 : ℤ)) * ((R : ℤ) ^ 3 - 1) < (R : ℤ) ^ 3 * (H : ℤ) := by
    have h6 : ((W * (A0 + A1 + Kp) + 4 * x : ℕ) : ℤ) = ((A0 + A1 + W * Km : ℕ) : ℤ) := by
      exact_mod_cast hS.E6
    have h19 : ((W : ℕ) : ℤ) = ((R ^ 3 : ℕ) : ℤ) := by exact_mod_cast hS.E19
    push_cast at h6 h19
    have hKm : (Km : ℤ) ≤ (H : ℤ) := by exact_mod_cast (show Km ≤ H by omega)
    have hKp0 : (0 : ℤ) ≤ (Kp : ℤ) := by positivity
    have hx1z : (1 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hx1
    have hR3 : (0 : ℤ) ≤ (R : ℤ) ^ 3 := by positivity
    rw [h19] at h6
    nlinarith
  have hkey := guard_key (A := (A0 : ℤ) + (A1 : ℤ)) (t := (t : ℤ)) (D := (D : ℤ))
    (q := (q : ℤ)) (H := (H : ℤ)) (R := (R : ℤ))
    (by exact_mod_cast hR27) (by exact_mod_cast hP.q) (by positivity) (by positivity)
    (by positivity) hTz (by exact_mod_cast hDq) hHz hAz
  exact_mod_cast hkey

end Guard

section Full

variable {C : ROM100}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u dm pK : ℕ}
  (hOk : C.Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 C x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

/-- **§§3–5.**  All five nonnegativity statements. -/
theorem nonneg_full100 (hSid : C.Sidon dm pK)
    (hdm : dm ≤ m) (hSm : C.S < 3 ^ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hI : 0 < C.I) (hIM : 2 * C.I < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hexp : ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm)
    (hDq : 2 * q ≤ R * D) :
    Nonneg100 C H D t A0 A1 PV PC z := by
  have hguard := guard_lt100 hOk hP hS hDq
  exact nonneg100 hOk hP hS hG hSid hdm hSm hMS hI hIM hcong hexp (by omega) (by omega)

/-- **The decoding of the counter certificate.**  Every solution of `Sys100` whose compiled
ROM has the Sidon layout, and which satisfies the route residue and the decoded-control
bound, has all twelve of its conceptual fields equal to twice a Boolean ternary word below
`rep e`: the doubled coordinates of §5. -/
theorem decode100 (hSid : C.Sidon dm pK)
    (hdm : dm ≤ m) (hSm : C.S < 3 ^ m) (hMS : 2 * C.S < 3 ^ (m - dm))
    (hI : 0 < C.I) (hIM : 2 * C.I < 3 ^ (m - dm))
    (hcong : PC % 3 ^ (m - dm) = 2 * C.I)
    (hexp : ∀ aC, Ternary.Lead aC 2 PC → pK + aC < dm)
    (hDq : 2 * q ≤ R * D) :
    Doubled e Kp ∧ Doubled e Km ∧ Doubled e (H - D) ∧ Doubled e D ∧
    Doubled e (t - A0) ∧ Doubled e A0 ∧ Doubled e (t - A1) ∧ Doubled e A1 ∧
    Doubled e (z * H - PV) ∧ Doubled e PV ∧ Doubled e (C.S * H - PC) ∧ Doubled e PC :=
  fields100 hOk hP hS hG
    (nonneg_full100 hOk hP hS hG hSid hdm hSm hMS hI hIM hcong hexp hDq)

end Full

end Jones1980
