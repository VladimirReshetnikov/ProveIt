import DiophantineConsistency.ModelThirteenCarrier

/-! # The oriented thirteen-coordinate 70/170 carrier form: core, syntax, restoration

Package 192's companion `compact13/positive13_oriented.json` differs from the main
13/69/174 form (`ThirteenCarrier.value69`) in one gate: the main form takes
`L = V²` in the carrier ordinate `y = 1 + 4[h(m - L·B) - B]`, the companion takes
`L = b·V` with `b = cT - R` and `V = f²b - c` (`compact13/PROOF.md` §§0, 3, 4).

This file is port-independent. It gives

* the ring-level core `core70o` and value `value70o` (same `Core` record as
  `ThirteenCarrier.core`, only `y` and hence `gap` change);
* the literal syntax `front13o`/`expressionAt70o` and `evalRing_expressionAt70o`;
* the generalized carrier lemmas: in the y-shape the square `W²` is replaced by any
  `L` with `0 ≤ L` (`affine_pos_L`, `transport_nonneg_L`);
* soundness (`restores_positive_zero70o`) over every discretely ordered ring with
  `ModelCarrierSpheres.Facts` and the signed residue: at a positive zero,
  `b = cT - R ≠ 0` (otherwise `V = -c` and the auxiliary norm forces
  `(S²-1)(y²-c²) = c²-1` strictly between `0` and `S²-1`), `c < f²` from the strong
  norm, so `V` has the sign of `b` and `|V| ≤ bV = L`; then the main-form restoration
  goes through with `L`;
* the completion map facts `core_replace70o`, `replace_zero70o` over the generic
  `ModelThirteenCarrier.replace`.

The restoration reuses `ModelThirteenRestoration`'s `parent`, `data`, `G`,
`scale_ge_two`, `auxiliary_estimates`, `core_parent` unchanged: none of them
depends on the carrier ordinate's shape. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ThirteenOriented70
open AdaptiveEquationSyntax2011 ModelCarrierSpheres DiscreteOrderedRingFacts
open ModelThirteenRestoration

/-! ### The ring-level core and value -/

section Defs
variable {R S : Type*} [CommRing R] [CommRing S]

def core70o (p : Fin 4 → R) (v : Fin 13 → R) : ThirteenCarrier.Core R :=
  let b := p 0 * v 0
  let q := b + 1
  let C := q - v 1 - v 2
  let X := v 7 * q
  let Y := v 6 * q ^ 3
  let E := X * Y
  let k := v 9 + v 10
  let ell := E * k * Y
  let c := k * Y + v 9
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + v 12 * H
  let rank := (b * (q - v 1) + v 2) * (q ^ 2 - 1) + (p 2 + q * p 3) * v 0
  let tau := E * v 8 + k - rank
  let f := v 3
  let ob := c * v 5 - rank
  let V := f ^ 2 * ob - c
  let L := ob * V
  let G := (p 1 + v 7) * C - v 1
  let y := 1 + 4 * (b * (v 11 - L * G) - G)
  ⟨a, delta, b * v 4 * c ^ 2, f, V ^ 2 - y ^ 2, y,
    tau ^ 2 - ell * (ell + k), D ^ 2 - delta * c ^ 2⟩

/-- The oriented 13/70/170 value. -/
def value70o (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let b := core70o p v
  let S := b.delta * b.t
  b.P * b.Q * (S ^ 2 * b.gap + b.y ^ 2) * (b.delta * b.f ^ 2 - S ^ 2) - b.delta

theorem value70o_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 13 → R) :
    φ (value70o p v) = value70o (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value70o, core70o, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

end Defs

/-! ### Literal thirteen-coordinate syntax -/

/-- The oriented front: `front13` with the single gate `L = (cT - R)·V` in place of `V²`,
followed by `final P Q S f δ gap y t`. -/
def front13o (p : Fin 4 → ℤ)
    (final : Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) →
      Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13) → Expr (Fin 13)) :
    Expr (Fin 13) :=
  let J : Expr (Fin 13) := .var 0
  let F : Expr (Fin 13) := .var 1
  let alpha : Expr (Fin 13) := .var 2
  let f : Expr (Fin 13) := .var 3
  let i : Expr (Fin 13) := .var 4
  let T : Expr (Fin 13) := .var 5
  let s : Expr (Fin 13) := .var 6
  let w : Expr (Fin 13) := .var 7
  let n : Expr (Fin 13) := .var 8
  let eta : Expr (Fin 13) := .var 9
  let zeta : Expr (Fin 13) := .var 10
  let m : Expr (Fin 13) := .var 11
  let gamma : Expr (Fin 13) := .var 12
  let b := Expr.constant (p 0) * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) +
    (Expr.constant (p 2) + q * Expr.constant (p 3)) * J
  let tau := E * n + k - rank
  let ob := c * T - rank
  let V := f ^ 2 * ob - c
  let L := ob * V
  let G := (Expr.constant (p 1) + w) * C - F
  let y := 1 + 4 * (b * (m - L * G) - G)
  final (tau ^ 2 - ell * (ell + k)) (D ^ 2 - delta * c ^ 2) (delta * (b * i * c ^ 2))
    f delta (V ^ 2 - y ^ 2) y (b * i * c ^ 2)

/-- The oriented 13/70/170 polynomial. -/
def expressionAt70o (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  front13o p fun P Q S f delta gap y _ =>
    P * Q * (S ^ 2 * gap + y ^ 2) * (delta * f ^ 2 - S ^ 2) - delta

theorem evalRing_expressionAt70o {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) :
    (expressionAt70o p).evalRing v = value70o (fun j => (p j : R)) v := by
  simp only [expressionAt70o, front13o, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_pow, Expr.evalRing_var,
    Expr.evalRing_constant, Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one,
    value70o, core70o]

/-! ### Restoration data (the parent map of `ModelThirteenRestoration`) -/

section RestoreDefs
variable {R : Type*} [CommRing R]

/-- The oriented factor `b = cT - R` of the restoration data. -/
def ob (p : Fin 4 → R) (v : Fin 13 → R) : R := (data p v).c * v 5 - (data p v).rank

/-- The oriented carrier multiplier `L = b·V`. -/
def Lo (p : Fin 4 → R) (v : Fin 13 → R) : R := ob p v * (data p v).V

def signedY70 (p : Fin 4 → R) (v : Fin 13 → R) : R := (core70o p v).y

def auxiliary70 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  (data p v).S ^ 2 * ((data p v).V ^ 2 - signedY70 p v ^ 2) + signedY70 p v ^ 2

theorem signedY70_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    signedY70 p v = 1 + 4 * (b p v * (v 11 - Lo p v * G p v) - G p v) := rfl

theorem V_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    (data p v).V = (data p v).f ^ 2 * ob p v - (data p v).c := rfl

theorem scale_shape70 (p : Fin 4 → R) (v : Fin 13 → R) :
    (core70o p v).delta * (core70o p v).t = (data p v).S := by
  change (data p v).delta * (b p v * v 4 * (data p v).c ^ 2) =
    (b p v * v 4) * (data p v).delta * (data p v).c ^ 2
  ring

theorem value70o_scaled (p : Fin 4 → R) (v : Fin 13 → R) :
    value70o p v = (data p v).delta *
      ((data p v).P * (data p v).Q * auxiliary70 p v * Carrier65.strong (data p v) - 1) := by
  dsimp only [value70o]
  rw [scale_shape70]
  change (data p v).P * (data p v).Q * auxiliary70 p v *
    ((data p v).delta * (data p v).f ^ 2 - (data p v).S ^ 2) - (data p v).delta = _
  change (data p v).P * (data p v).Q * auxiliary70 p v *
    (data p v).Z - (data p v).delta = _
  rw [show (data p v).Z = (data p v).delta * Carrier65.strong (data p v) from
    Carrier65.strong_scale p (parent p v 1 1)]
  ring

end RestoreDefs

/-! ### Generalized carrier lemmas and soundness over a discretely ordered ring -/

section Generic
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- `affine_carrier_pos` with the square `W²` replaced by any `L ≥ 0`. -/
theorem affine_pos_L (F : Facts R) {b G L y m : R} (hb : 0 < b) (hG : 0 < G) (hL : 0 ≤ L)
    (hsmall : -2 * L < y) (hy : y = 1 + 4 * (b * (m - L * G) - G)) : 0 < m := by
  by_contra hm
  push_neg at hm
  have hb1 : 1 ≤ b := F.discrete _ hb
  have hG1 : 1 ≤ G := F.discrete _ hG
  have hbm := mul_nonpos_of_nonneg_of_nonpos hb.le hm
  have hbG : 1 ≤ b * G := one_le_mul_of_one_le_of_one_le hb1 hG1
  have hLbG := mul_nonneg hL (show (0:R) ≤ b * G - 1 by linarith)
  nlinarith only [hy, hsmall, hbm, hLbG, hG1, hL]

/-- `transport_nonneg` with the square `W²` replaced by any `L ≥ 0` bounding `|y|/2`. -/
theorem transport_nonneg_L (F : Facts R) {b m G L y : R} (hb : 0 < b) (hm : 0 < m)
    (hL : 0 ≤ L) (hy : y = 1 + 4 * (b * (m - L * G) - G)) (hsmall : |y| < 2 * L) :
    0 ≤ G := by
  by_contra hG
  push_neg at hG
  have hsmall' : -2 * L < 2 - y := by
    have := le_abs_self y
    linarith
  have hreflect : 2 - y = 1 + 4 * (b * (-m - L * -G) - -G) := by linear_combination -hy
  have := affine_pos_L F hb (show (0:R) < -G by linarith) hL hsmall' hreflect
  linarith

/-- With `c < f²` and `o ≠ 0`, `V = f²o - c` has the sign of `o`, so `|V| ≤ oV`. -/
theorem abs_le_oriented (F : Facts R) {o f c V : R} (ho : o ≠ 0) (hc : 0 < c)
    (hf : c < f ^ 2) (hV : V = f ^ 2 * o - c) : |V| ≤ o * V := by
  have hf0 : 0 ≤ f ^ 2 := sq_nonneg f
  rcases lt_or_gt_of_ne ho with h | h
  · have h1 : o ≤ -1 := by
      have := F.discrete (-o) (by linarith)
      linarith
    have hm := mul_le_mul_of_nonneg_left h1 hf0
    have hVneg : V < 0 := by rw [hV]; linarith
    rw [abs_of_neg hVneg]
    have := mul_nonneg_of_nonpos_of_nonpos (show o + 1 ≤ 0 by linarith) hVneg.le
    linarith
  · have h1 : 1 ≤ o := F.discrete _ h
    have hm := mul_le_mul_of_nonneg_left h1 hf0
    have hVpos : 0 < V := by rw [hV]; linarith
    rw [abs_of_pos hVpos]
    have := mul_nonneg (show 0 ≤ o - 1 by linarith) hVpos.le
    linarith

/-- The centred case `V = -c` of the auxiliary norm is impossible when `2 ≤ c < S`:
`(S²-1)(y²-c²) = c²-1` would lie strictly between `0` and `S²-1`. -/
theorem centered_impossible (F : Facts R) {S c y : R} (hc : 2 ≤ c) (hSc : c < S)
    (hn : S ^ 2 * c ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1) : False := by
  have hS1 : 0 < S ^ 2 - 1 := by nlinarith
  have hcs : c ^ 2 < S ^ 2 := by nlinarith
  have hd : (S ^ 2 - 1) * (y ^ 2 - c ^ 2) = c ^ 2 - 1 := by linear_combination -hn
  have hpos : 0 < y ^ 2 - c ^ 2 := by
    by_contra h
    push_neg at h
    have := mul_nonpos_of_nonneg_of_nonpos hS1.le h
    nlinarith
  have h1 : 1 ≤ y ^ 2 - c ^ 2 := F.discrete _ hpos
  have := mul_le_mul_of_nonneg_left h1 hS1.le
  nlinarith

variable (F : Facts R) (p : Fin 4 → R) (v : Fin 13 → R) (hb : 0 < p 0) (hv : ∀ j, 0 < v j)
include F hb hv

theorem norms_of_zero70 (hz : value70o p v = 0) :
    (data p v).P = 1 ∧ (data p v).Q = 1 ∧ auxiliary70 p v = 1 ∧
      Carrier65.strong (data p v) = 1 := by
  have hp := parent_pos1 F p v hb hv
  have hd := ModelCarrierScaled.delta_pos F.discrete p (parent p v 1 1) hb hp
  obtain ⟨hP, hQ, hs⟩ := negative_unit_exclusions F p (parent p v 1 1) hb hp
  have hu : auxiliary70 p v ≠ -1 := square_aux_ne_neg_one F _ _ _
  rw [value70o_scaled, mul_eq_zero] at hz
  have hprod : (data p v).P * (data p v).Q * auxiliary70 p v *
      Carrier65.strong (data p v) = 1 := sub_eq_zero.mp (hz.resolve_left hd.ne')
  set P := (data p v).P; set Q := (data p v).Q; set U := auxiliary70 p v
  set S := Carrier65.strong (data p v)
  have hS1 : S = 1 := unit_eq_one F.discrete (show S * (P*Q*U) = 1 by linear_combination hprod) hs
  have hP1 : P = 1 := unit_eq_one F.discrete (show P * (Q*U*S) = 1 by linear_combination hprod) hP
  have hQ1 : Q = 1 := unit_eq_one F.discrete (show Q * (P*U*S) = 1 by linear_combination hprod) hQ
  refine ⟨hP1, hQ1, ?_, hS1⟩
  rw [hP1, hQ1, hS1] at hprod; linear_combination hprod

/-- The scale facts used by the orientation step: `2 ≤ c < S`, `1 ≤ δ`, `1 ≤ i`. -/
theorem scale_facts : 2 ≤ (data p v).c ∧ (data p v).c < (data p v).S ∧
    1 ≤ (data p v).delta ∧ 1 ≤ (data p v).i := by
  have hp := parent_pos1 F p v hb hv
  obtain ⟨_, _, hY, _, _⟩ := scales_pos F p (parent p v 1 1) hb hp
  have hd := ModelCarrierScaled.delta_pos F.discrete p (parent p v 1 1) hb hp
  have hd1 : 1 ≤ (data p v).delta := F.discrete _ hd
  have hi : 0 < (data p v).i := mul_pos (mul_pos hb (hv 0)) (hv 4)
  have hi1 : 1 ≤ (data p v).i := F.discrete _ hi
  have h9 : 1 ≤ v 9 := F.discrete _ (hv 9)
  have h10 : 1 ≤ v 10 := F.discrete _ (hv 10)
  have hY1 : 1 ≤ (data p v).Y := F.discrete _ hY
  have hk : 2 ≤ (data p v).k := by change 2 ≤ v 9 + v 10; linarith
  have hc : 2 ≤ (data p v).c := by
    change 2 ≤ (data p v).k * (data p v).Y + v 9
    nlinarith
  have hid : 1 ≤ (data p v).i * (data p v).delta := by nlinarith
  refine ⟨hc, ?_, hd1, hi1⟩
  change (data p v).c < ((data p v).i * (data p v).delta) * (data p v).c ^ 2
  have hc2 : (data p v).c < (data p v).c ^ 2 := by nlinarith
  have := le_mul_of_one_le_left (sq_nonneg (data p v).c) hid
  linarith

omit F hb hv in
theorem auxiliary_norm70 (hu : auxiliary70 p v = 1) :
    (data p v).S ^ 2 * (data p v).V ^ 2 -
      ((data p v).S ^ 2 - 1) * signedY70 p v ^ 2 = 1 := by
  unfold auxiliary70 at hu
  linear_combination hu

/-- At a zero, the oriented multiplier dominates `|V|`: `0 ≤ |V| ≤ L = (cT - R)·V`. -/
theorem oriented_bound (hu : auxiliary70 p v = 1) (hs : Carrier65.strong (data p v) = 1) :
    |(data p v).V| ≤ Lo p v := by
  obtain ⟨hc2, hcS, hd1, hi1⟩ := scale_facts F p v hb hv
  have hn := auxiliary_norm70 p v hu
  have hob : ob p v ≠ 0 := by
    intro h0
    have hV : (data p v).V = -(data p v).c := by
      rw [V_shape, h0]; ring
    rw [hV] at hn
    exact centered_impossible F (y := signedY70 p v) hc2 hcS (by linear_combination hn)
  have hfc : (data p v).c < (data p v).f ^ 2 := by
    have hs' : (data p v).f ^ 2 =
        1 + (data p v).delta * ((data p v).i * (data p v).c ^ 2) ^ 2 := by
      unfold Carrier65.strong at hs
      linear_combination hs
    have hc1 : (1 : R) ≤ (data p v).c := by linarith
    have hcc : (data p v).c ≤ (data p v).c ^ 2 := by nlinarith
    have hic : (data p v).c ^ 2 ≤ (data p v).i * (data p v).c ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hi1
    have hic1 : 1 ≤ (data p v).i * (data p v).c ^ 2 := by linarith
    have h2 : (data p v).i * (data p v).c ^ 2 ≤ ((data p v).i * (data p v).c ^ 2) ^ 2 := by
      nlinarith
    have h3 : ((data p v).i * (data p v).c ^ 2) ^ 2 ≤
        (data p v).delta * ((data p v).i * (data p v).c ^ 2) ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hd1
    linarith
  exact abs_le_oriented F hob (by linarith) hfc (V_shape p v)

theorem base_dvd_transport70 (hres : SignedResidue R) (hu : auxiliary70 p v = 1) :
    ∃ g, G p v = b p v * g := by
  have hs := scale_ge_two F p v hb hv
  have hn := auxiliary_norm70 p v hu
  obtain ⟨u, hu4⟩ := hres _ _ _ hs hn
    ⟨b p v * (v 11 - Lo p v * G p v) - G p v,
      by rw [signedY70_shape]; ring⟩
  rw [signedY70_shape] at hu4
  refine ⟨(v 11 - Lo p v * G p v) -
    b p v * (v 4 * (data p v).delta * (data p v).c ^ 2) ^ 2 * u, ?_⟩
  have hS : (data p v).S = b p v * (v 4 * (data p v).delta * (data p v).c ^ 2) := by
    change (b p v * v 4) * (data p v).delta * (data p v).c ^ 2 = _
    ring
  rw [hS] at hu4
  have h4 : (4:R) * (G p v - b p v * ((v 11 - Lo p v * G p v) -
      b p v * (v 4 * (data p v).delta * (data p v).c ^ 2) ^ 2 * u)) = 0 := by
    linear_combination -hu4
  rcases mul_eq_zero.mp h4 with h | h
  · exact absurd h (by norm_num)
  · linear_combination h

/-- The restored fourteen-coordinate assignment, with an explicit quotient. -/
def restoredWith70 (g : R) : Fin 14 → R := parent p v (g + 1) |signedY70 p v|

/-- **Soundness**: a positive zero of the oriented 70 form restores to a positive
Carrier65 zero. -/
theorem restores_positive_zero70o (hres : SignedResidue R)
    (hz : value70o p v = 0) :
    ∃ w : Fin 14 → R, (∀ j, 0 < w j) ∧ Carrier65.value p w = 0 := by
  obtain ⟨hP, hQ, hu, hs⟩ := norms_of_zero70 F p v hb hv hz
  have hbv : 0 < b p v := mul_pos hb (hv 0)
  obtain ⟨hyne, hsmall⟩ :=
    auxiliary_estimates F (scale_ge_two F p v hb hv) (auxiliary_norm70 p v hu)
  have hL := oriented_bound F p v hb hv hu hs
  have hL0 : 0 ≤ Lo p v := le_trans (abs_nonneg _) hL
  have hsmallL : |signedY70 p v| < 2 * Lo p v := by linarith
  have hG := transport_nonneg_L F hbv (hv 11) hL0 (signedY70_shape p v) hsmallL
  obtain ⟨g, hg⟩ := base_dvd_transport70 F p v hb hv hres hu
  have hg0 : 0 ≤ g := by
    by_contra hneg; push_neg at hneg
    have := mul_neg_of_pos_of_neg hbv hneg
    linarith
  have hzpos : 0 < g + 1 := by linarith
  have hW : G p v + (data p v).q - (g + 1) * b p v = 1 := by
    change G p v + (b p v + 1) - (g + 1) * b p v = 1
    rw [hg]; ring
  have hZ : (data p v).Z = (data p v).delta := by
    change (Carrier65.core p (parent p v 1 1)).Z = _
    rw [Carrier65.strong_scale]
    change (data p v).delta * Carrier65.strong (data p v) = (data p v).delta
    rw [hs, mul_one]
  refine ⟨restoredWith70 p v g, parent_pos F p v hb hv hzpos (abs_pos.mpr hyne), ?_⟩
  unfold restoredWith70 Carrier65.value
  rw [core_parent]
  change (data p v).P * (data p v).Q *
    ((data p v).S ^ 2 * ((data p v).V ^ 2 - |signedY70 p v| ^ 2) + |signedY70 p v| ^ 2) *
    (G p v + (data p v).q - (g + 1) * b p v) * (data p v).Z -
    (data p v).delta = 0
  rw [sq_abs]
  change (data p v).P * (data p v).Q * auxiliary70 p v *
    (G p v + (data p v).q - (g + 1) * b p v) * (data p v).Z -
    (data p v).delta = 0
  rw [hP, hQ, hu, hW, hZ]
  ring

end Generic

/-! ### The completion map (generic ring facts over `ModelThirteenCarrier.replace`) -/

section Replace
variable {R : Type*} [CommRing R]
open ModelThirteenCarrier (transport replace)

theorem core_replace70o (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R) :
    let b := Carrier65.core p v
    let V := f ^ 2 * (b.c * T - b.rank) - b.c
    let L := (b.c * T - b.rank) * V
    let y := 1 + 4 * (p 0 * v 0 * (m - L * transport p v) - transport p v)
    core70o p (replace v f i T m) =
      ⟨b.a, b.delta, p 0 * v 0 * i * b.c ^ 2, f, V ^ 2 - y ^ 2, y, b.P, b.Q⟩ := rfl

/-- A completion zero, with the scale `S`, the ordinate root `V` and the signed carrier
ordinate `y` passed as abstract values. -/
theorem replace_zero70o (p : Fin 4 → R) (v : Fin 14 → R) (f i T m S V y : R)
    (hP : (Carrier65.core p v).P = 1) (hQ : (Carrier65.core p v).Q = 1)
    (hs : f ^ 2 - (Carrier65.core p v).delta *
      (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2) ^ 2 = 1)
    (hS : (Carrier65.core p v).delta * (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2) = S)
    (hV : f ^ 2 * ((Carrier65.core p v).c * T - (Carrier65.core p v).rank) -
      (Carrier65.core p v).c = V)
    (hy : 1 + 4 * (p 0 * v 0 * (m - ((Carrier65.core p v).c * T -
      (Carrier65.core p v).rank) * V * transport p v) - transport p v) = y)
    (hu : S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1) :
    value70o p (replace v f i T m) = 0 := by
  dsimp only [value70o]
  rw [core_replace70o]
  dsimp only
  rw [hV, hy, hP, hQ, hS, hu]
  linear_combination (Carrier65.core p v).delta * hs +
    ((Carrier65.core p v).delta * (p 0 * v 0 * i * (Carrier65.core p v).c ^ 2) + S) * hS

end Replace

end DiophantineConsistency.ThirteenOriented70

#print axioms DiophantineConsistency.ThirteenOriented70.evalRing_expressionAt70o
#print axioms DiophantineConsistency.ThirteenOriented70.affine_pos_L
#print axioms DiophantineConsistency.ThirteenOriented70.transport_nonneg_L
#print axioms DiophantineConsistency.ThirteenOriented70.oriented_bound
#print axioms DiophantineConsistency.ThirteenOriented70.restores_positive_zero70o
#print axioms DiophantineConsistency.ThirteenOriented70.replace_zero70o
