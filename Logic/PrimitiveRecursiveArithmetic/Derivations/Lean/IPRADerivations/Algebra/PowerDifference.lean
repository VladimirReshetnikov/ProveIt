import IPRADerivations.Core.SumOrder
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.AnalyticNumberTheory.Order

/-!
# The finite toolkit of the constructive fundamental theorem of algebra

Packet: `algebra/FTA_iPRA` (the list of finite tools: `eq:power-diff`, the Bernoulli instance,
finite geometric sums; and the algebra of the half-angle construction of `lem:direction`).

* `gd x y i = ∑_{r<i} x^(i−1−r) y^r`, by the recursion `gd (i + 1) = x · gd i + y^i`;
* `power_diff` (`eq:power-diff`): `x^i − y^i = (x − y) · gd x y i`, written
  `x^i + y · gd = y^i + x · gd`;
* `geom_sum`: the case `y = 1`, `x^i + gd x 1 i = 1 + x · gd x 1 i`, i.e.
  `(x − 1) ∑_{r<i} x^r = x^i − 1`;
* `gd_le`: for `x, y ≤ R`, `gd x y (i + 1) ≤ (i + 1) R^i`; with `power_diff` this is the Lipschitz
  estimate `abs(x^i − y^i) ≤ i R^(i−1) abs(x − y)` behind `eq:poly-lipschitz`;
* `bernoulli_lin`: `1 + m x ≤ (1 + x)^m`;
* `half_angle_norm`, `half_angle_re`, `half_angle_im`: if `2 s² = D (D + A)` and
  `2 t² = D (D − A)` (so `s/D`, `t/D` are the half-angle cosine and sine for the cosine `A/D`),
  then `2 (s² + t²) = 2 D²`, `2 (s² − t²) = 2 D A` and `(2 s t)² = D² (D² − A²)`: the point
  `v = (s + i t)/D` has norm one and `v²` has real part `A/D`;
* `eighth_power_diff`: `x⁸ − y⁸ = (x − y)(x + y)(x² + y²)(x⁴ + y⁴)`;
* `sqrt_truncation₂`, `sqrt_truncation₃`, `cbrt_truncation₂`: instances of the finite binomial
  identity `P_N(T)^k ≡ 1 + T (mod T^(N+1))` for `(k, N) = (2, 2), (2, 3), (3, 2)`, cleared of
  denominators.

The bisection square roots, the direction lemma itself, the descent and the root construction are
not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.PowerDifference

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
local notation "𝔷" t:max => ZT.toZ _ t

/-! ## The geometric-type sum -/

/-- Step of `gd`: variables `0 = i`, `1 = gd i`, `2 = ⟨x, y⟩`. -/
abbrev gdStep : PTm 3 := fstT (var 2) * var 1 + pw (sndT (var 2)) (var 0)
abbrev gdF : PR 2 := rec2 zero gdStep

/-- `gd x y i = ∑_{r<i} x^(i−1−r) y^r`. -/
abbrev gd (x y i : PTm n) : PTm n := ap2 gdF i (pairT x y)

theorem gd_zero (x y : PTm n) : Γ ⊢[PRAAx] gd x y zero ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero gdStep (pairT x y)
  simpa using h

theorem gd_succ (x y i : PTm n) : Γ ⊢[PRAAx] gd x y (succ i) ≐ x * gd x y i + pw y i := by
  have h := rec2_succ (Γ := Γ) zero gdStep i (pairT x y)
  have e : Syn.subst ![i, ap2 gdF i (pairT x y), pairT x y] gdStep =
      fstT (pairT x y) * gd x y i + pw (sndT (pairT x y)) i := by simp
  rw [e] at h
  exact h.eqTrans (congrAdd (congrMul (fst_pair _ _) (.eqRefl _))
    (congrAp2 powF (.eqRefl _) (snd_pair _ _)))

/-! ## The power difference -/

theorem pd_base (x y : PTm n) :
    Γ ⊢[PRAAx] pw x zero + y * gd x y zero ≐ pw y zero + x * gd x y zero := by
  ipra_lc natEq (pw_zero (Γ := Γ) x) - natEq (pw_zero (Γ := Γ) y) + (𝔞(y) - 𝔞(x)) * natEq (gd_zero (Γ := Γ) x y)

theorem pd_step {x y i : PTm n} (ih : Γ ⊢[PRAAx] pw x i + y * gd x y i ≐ pw y i + x * gd x y i) :
    Γ ⊢[PRAAx] pw x (succ i) + y * gd x y (succ i) ≐ pw y (succ i) + x * gd x y (succ i) := by
  ipra_lc 𝔞(x) * natEq ih + natEq (pw_succ (Γ := Γ) x i) - natEq (pw_succ (Γ := Γ) y i) +
    (𝔞(y) - 𝔞(x)) * natEq (gd_succ (Γ := Γ) x y i)

/-- Variables: `0 = i` (induction), `1 = x`, `2 = y`. -/
private abbrev pdF : Fm PTm 3 :=
  pw (var 1) (var 0) + var 2 * gd (var 1) (var 2) (var 0) ≐
    pw (var 2) (var 0) + var 1 * gd (var 1) (var 2) (var 0)

private theorem pd₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] pdF := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact pd_base _ _
  · exact pd_step Prf.hyp0

/-- `eq:power-diff`: `x^i + y · gd x y i = y^i + x · gd x y i`. -/
theorem power_diff (x y i : PTm n) :
    Γ ⊢[PRAAx] pw x i + y * gd x y i ≐ pw y i + x * gd x y i := by
  have h := inst (Γ := Γ) pd₀ (![i, x, y] : Fin 3 → PTm n)
  simpa using h

/-- The finite geometric sum: `x^i + G = 1 + x G` with `G = ∑_{r<i} x^r`. -/
theorem geom_sum (x i : PTm n) :
    Γ ⊢[PRAAx] pw x i + gd x one i ≐ one + x * gd x one i := by
  ipra_lc natEq (power_diff (Γ := Γ) x one i) + natEq (pw_one_base (Γ := Γ) i)

/-! ## The Lipschitz bound -/

theorem gd_le_base (x y R : PTm n) :
    Γ ⊢[PRAAx] le (gd x y (succ zero)) (succ zero * pw R zero) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc natEq (pw_zero (Γ := Γ) R) - natEq (gd_succ (Γ := Γ) x y zero) - 𝔞(x) * natEq (gd_zero (Γ := Γ) x y) -
    natEq (pw_zero (Γ := Γ) y)

theorem gd_le_step {x y R i : PTm n} (hx : Γ ⊢[PRAAx] le x R) (hy : Γ ⊢[PRAAx] le y R)
    (ih : Γ ⊢[PRAAx] le (gd x y (succ i)) (succ i * pw R i)) :
    Γ ⊢[PRAAx] le (gd x y (succ (succ i))) (succ (succ i) * pw R (succ i)) := by
  have m := add_le_add₂ (le_mul_mono hx ih) (pw_le_pw (succ i) hy)
  refine le_congr (gd_succ x y (succ i)).eqSymm ?_ m
  ipra_lc -(𝔞(i) + 1) * natEq (pw_succ (Γ := Γ) R i)

/-- Variables: `0 = i` (induction), `1 = x`, `2 = y`, `3 = R`. -/
private abbrev glF : Fm PTm 4 :=
  le (var 1) (var 3) ⟶ (le (var 2) (var 3) ⟶
    le (gd (var 1) (var 2) (succ (var 0))) (succ (var 0) * pw (var 3) (var 0)))

private theorem gl₀ : ([] : List (Fm PTm 4)) ⊢[PRAAx] glF := by
  ipra_ind (⟨le_QF _ _, ⟨le_QF _ _, le_QF _ _⟩⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (.impI (gd_le_base _ _ _))
  · refine .impI (.impI ?_)
    exact gd_le_step Prf.hyp1 Prf.hyp0 (.impE (.impE Prf.hyp1.wk Prf.hyp1) Prf.hyp0)

/-- For `x, y ≤ R`: `∑_{r<i+1} x^(i−r) y^r ≤ (i + 1) R^i`. -/
theorem gd_le {x y R : PTm n} (i : PTm n) (hx : Γ ⊢[PRAAx] le x R) (hy : Γ ⊢[PRAAx] le y R) :
    Γ ⊢[PRAAx] le (gd x y (succ i)) (succ i * pw R i) := by
  have h := inst (Γ := Γ) gl₀ (![i, x, y, R] : Fin 4 → PTm n)
  simp at h
  exact .impE (.impE h hx) hy

/-! ## Bernoulli -/

theorem bern_lin_step {x m : PTm n} (ih : Γ ⊢[PRAAx] le (one + m * x) (pw (succ x) m)) :
    Γ ⊢[PRAAx] le (one + succ m * x) (pw (succ x) (succ m)) := by
  refine le_trans (le_of_eq_add (d := m * x * x) ?_)
    (le_congr (.eqRefl _) (pw_succ _ _).eqSymm (mul_le_mul_right (succ x) ih))
  ipra_ring

/-- Variables: `0 = m` (induction), `1 = x`. -/
private abbrev blF : Fm PTm 2 := le (one + var 0 * var 1) (pw (succ (var 1)) (var 0))

private theorem bl₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] blF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · refine le_of_eq_add (d := zero) ?_
    ipra_lc natEq (pw_zero (Γ := []) (succ (var 0 : PTm 1)))
  · exact bern_lin_step Prf.hyp0

/-- `1 + m x ≤ (1 + x)^m`. -/
theorem bernoulli_lin (x m : PTm n) : Γ ⊢[PRAAx] le (one + m * x) (pw (succ x) m) := by
  have h := inst (Γ := Γ) bl₀ (![m, x] : Fin 2 → PTm n)
  simpa using h

/-! ## The half-angle algebra -/

section HalfAngle

variable {s t A D : ZT n}

/-- `2 (s² + t²) = 2 D²`: the half-angle point has norm one. -/
theorem half_angle_norm (hs : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (s * s)) (D * (D + A)))
    (ht : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (t * t)) (D * (D - A))) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (s * s + t * t)) (ZT.natLit 2 * (D * D)) := by
  ipra_lc ZT.toZ_eq hs + ZT.toZ_eq ht

/-- `2 (s² − t²) = 2 D A`: the real part of the square is the given cosine. -/
theorem half_angle_re (hs : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (s * s)) (D * (D + A)))
    (ht : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (t * t)) (D * (D - A))) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (s * s - t * t)) (ZT.natLit 2 * (D * A)) := by
  ipra_lc ZT.toZ_eq hs - ZT.toZ_eq ht

/-- `(2 s t)² = D² (D² − A²)`: the imaginary part of the square is the sine, up to sign. -/
theorem half_angle_im (hs : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (s * s)) (D * (D + A)))
    (ht : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * (t * t)) (D * (D - A))) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sq (ZT.natLit 2 * s * t)) (D * D * (D * D - A * A)) := by
  ipra_lc 2 * 𝔷(t) * 𝔷(t) * ZT.toZ_eq hs + 𝔷(D) * (𝔷(D) + 𝔷(A)) * ZT.toZ_eq ht

end HalfAngle

/-! ## Closed polynomial identities -/

section Closed

abbrev X : ZT 4 := .var2 0 1
abbrev Y : ZT 4 := .var2 2 3

abbrev p2 {k : ℕ} (u : ZT k) : ZT k := u * u
abbrev p3 {k : ℕ} (u : ZT k) : ZT k := u * u * u
abbrev p4 {k : ℕ} (u : ZT k) : ZT k := u * u * u * u
abbrev p8 {k : ℕ} (u : ZT k) : ZT k := p4 u * p4 u

def eighthFormula : Fm PTm 4 :=
  ZT.eq (p8 X - p8 Y) ((X - Y) * (X + Y) * (p2 X + p2 Y) * (p4 X + p4 Y))

/-- `P₂(T) = 1 + T/2 − T²/8`, cleared by `8`: `(8 + 4T − T²)² = 64 (1 + T) + T³ (T − 8)`. -/
def sqrt2Formula : Fm PTm 4 :=
  ZT.eq (p2 (ZT.natLit 8 + ZT.natLit 4 * X - p2 X))
    (ZT.natLit 64 * (ZT.natLit 1 + X) + p3 X * (X - ZT.natLit 8))

/-- `P₃(T) = 1 + T/2 − T²/8 + T³/16`, cleared by `16`:
`(16 + 8T − 2T² + T³)² = 256 (1 + T) + T⁴ (20 − 4T + T²)`. -/
def sqrt3Formula : Fm PTm 4 :=
  ZT.eq (p2 (ZT.natLit 16 + ZT.natLit 8 * X - ZT.natLit 2 * p2 X + p3 X))
    (ZT.natLit 256 * (ZT.natLit 1 + X) + p4 X * (ZT.natLit 20 - ZT.natLit 4 * X + p2 X))

/-- `P₂(T) = 1 + T/3 − T²/9` for the cube root, cleared by `9`:
`(9 + 3T − T²)³ = 729 (1 + T) + T³ (9T² − T³ − 135)`. -/
def cbrt2Formula : Fm PTm 4 :=
  ZT.eq (p3 (ZT.natLit 9 + ZT.natLit 3 * X - p2 X))
    (ZT.natLit 729 * (ZT.natLit 1 + X) + p3 X * (ZT.natLit 9 * p2 X - p3 X - ZT.natLit 135))

theorem eighth_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] eighthFormula := by
  unfold eighthFormula; ipra_ring

theorem sqrt2_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] sqrt2Formula := by
  unfold sqrt2Formula; ipra_ring

theorem sqrt3_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] sqrt3Formula := by
  unfold sqrt3Formula; ipra_ring

theorem cbrt2_open : ([] : List (Fm PTm 4)) ⊢[PRAAx] cbrt2Formula := by
  unfold cbrt2Formula; ipra_ring

/-- `x⁸ − y⁸ = (x − y)(x + y)(x² + y²)(x⁴ + y⁴)`. -/
theorem eighth_power_diff : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 eighthFormula := closeAll 4 eighth_open

theorem sqrt_truncation₂ : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 sqrt2Formula := closeAll 4 sqrt2_open

theorem sqrt_truncation₃ : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 sqrt3Formula := closeAll 4 sqrt3_open

theorem cbrt_truncation₂ : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 4 cbrt2Formula := closeAll 4 cbrt2_open

end Closed

end LeanProofs.IPRA.Algebra.PowerDifference
