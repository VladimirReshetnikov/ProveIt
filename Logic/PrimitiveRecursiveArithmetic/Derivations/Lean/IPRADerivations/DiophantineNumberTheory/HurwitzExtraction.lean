import IPRADerivations.DiophantineNumberTheory.HurwitzMargin
import IPRADerivations.Foundations.IntervalPacking

/-!
# Bounded-precision extraction of a continued-fraction digit (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `hurwitz.tex`, §"Why the continued-fraction prefix
can be obtained primitively recursively": "By (hw-floor-gap), the two quotients have the same integer part.
Thus exact rational division and flooring of the quotient at `y` gives `a_n`."

All quantities are cleared of denominators. A positive rational `t = a/d` (`d ≥ 1`) and its approximation
`t' = a'/d'` (`d' ≥ 1`) with `f = ⌊t'⌋`:

* `floor_stable`: if `|t − t'| ≤ L/6` (`6 L_d |ad' − a'd| ≤ L_n dd'`, `L = L_n/L_d`, `L_n ≥ 1`) and `t` is at
  distance `≥ L` from the integers `f` and `f + 1` (`L_n d ≤ L_d |a − fd|`, `L_n d ≤ L_d |a − (f+1)d|`), then
  `f ≤ t < f + 1`, i.e. `⌊t⌋ = ⌊t'⌋`;
* `floor_eq`: the same conclusion as `quo a d = quo a' d'`.

Absolute differences are `|x − y| = (x ∸ y) + (y ∸ x)` (`adist`). Each half is a contradiction certificate:
in the wrong case `6 L_n dd' ≤ L_n dd'` would follow, against `L_n dd' ≥ 1`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.HurwitzExtraction

open_ipra exports

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `|x − y| = (x ∸ y) + (y ∸ x)`. -/
abbrev adist (x y : PTm n) : PTm n := monus x y + monus y x

/-- `x ≤ y` gives `|x − y| = y − x` as two equations: `x ∸ y = 0` and `y = x + (y ∸ x)`. -/
theorem adist_of_le {x y : PTm n} (h : Γ ⊢[PRAAx] le x y) :
    Γ ⊢[PRAAx] (monus x y ≐ zero) ⋏ (y ≐ x + monus y x) :=
  .andI h (eq_add_of_le h)

/-- The lower half: `f d ≤ a`. -/
theorem floor_low {a d a' d' Ln Ld f : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hd' : Γ ⊢[PRAAx] le one d')
    (hLn : Γ ⊢[PRAAx] le one Ln) (hf : Γ ⊢[PRAAx] le (f * d') a')
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')))
    (sep : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (f * d))) : Γ ⊢[PRAAx] le (f * d) a := by
  refine .orE (lt_or_le a (f * d)) ?_ Prf.hyp0
  let Θ : List (Fm PTm n) := lt a (f * d) :: Γ
  have h : Θ ⊢[PRAAx] lt a (f * d) := Prf.hyp0
  have hle : Θ ⊢[PRAAx] le (a * d') (a' * d) := by
    have hf' : Θ ⊢[PRAAx] le (f * d') a' := hf.wk
    ipra_le 𝔞 d * sl hf' + 𝔞 d' * sl h + 𝔞 d'
  have q1 := adist_of_le hle
  have q2 := adist_of_le (le_of_lt h)
  have e1 := natEq (Prf.andE₁ q1)
  have e2 := natEq (Prf.andE₂ q1)
  have e3 := natEq (Prf.andE₁ q2)
  have e4 := natEq (Prf.andE₂ q2)
  have c' : Θ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')) := close.wk
  have s' : Θ ⊢[PRAAx] le (Ln * d) (Ld * adist a (f * d)) := sep.wk
  have hf' : Θ ⊢[PRAAx] le (f * d') a' := hf.wk
  have hpos : Θ ⊢[PRAAx] le one (Ln * (d * d')) := by
    have a1 : Θ ⊢[PRAAx] le one Ln := hLn.wk
    have a2 : Θ ⊢[PRAAx] le one d := hd.wk
    have a3 : Θ ⊢[PRAAx] le one d' := hd'.wk
    ipra_le sl a1 + 𝔞 Ln * sl a2 + 𝔞 Ln * 𝔞 d * sl a3
  have hz : Θ ⊢[PRAAx] le one zero := by
    ipra_le sl c' + 5 * sl hpos + 4 + 6 * 𝔞 d' * sl s' + 6 * 𝔞 Ld * 𝔞 d * sl hf'
      with 6 * 𝔞 Ld * (e1 - e2) + 6 * 𝔞 Ld * 𝔞 d' * (e4 - e3)
  exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- The upper half: `a < (f + 1) d`. -/
theorem floor_high {a d a' d' Ln Ld f : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hd' : Γ ⊢[PRAAx] le one d')
    (hLn : Γ ⊢[PRAAx] le one Ln) (hf : Γ ⊢[PRAAx] lt a' (succ f * d'))
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')))
    (sep : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (succ f * d))) : Γ ⊢[PRAAx] lt a (succ f * d) := by
  refine .orE (lt_or_le a (succ f * d)) Prf.hyp0 ?_
  let Θ : List (Fm PTm n) := le (succ f * d) a :: Γ
  have h : Θ ⊢[PRAAx] le (succ f * d) a := Prf.hyp0
  have hf' : Θ ⊢[PRAAx] lt a' (succ f * d') := hf.wk
  have hle : Θ ⊢[PRAAx] le (a' * d) (a * d') := by
    ipra_le 𝔞 d * sl hf' + 𝔞 d' * sl h + 𝔞 d
  have q1 := adist_of_le hle
  have q2 := adist_of_le h
  have e1 := natEq (Prf.andE₁ q1)
  have e2 := natEq (Prf.andE₂ q1)
  have e3 := natEq (Prf.andE₁ q2)
  have e4 := natEq (Prf.andE₂ q2)
  have c' : Θ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')) := close.wk
  have s' : Θ ⊢[PRAAx] le (Ln * d) (Ld * adist a (succ f * d)) := sep.wk
  have hpos : Θ ⊢[PRAAx] le one (Ln * (d * d')) := by
    have a1 : Θ ⊢[PRAAx] le one Ln := hLn.wk
    have a2 : Θ ⊢[PRAAx] le one d := hd.wk
    have a3 : Θ ⊢[PRAAx] le one d' := hd'.wk
    ipra_le sl a1 + 𝔞 Ln * sl a2 + 𝔞 Ln * 𝔞 d * sl a3
  have hz : Θ ⊢[PRAAx] le one zero := by
    ipra_le sl c' + 5 * sl hpos + 4 + 6 * 𝔞 d' * sl s' + 6 * 𝔞 Ld * 𝔞 d * sl hf' + 6 * 𝔞 Ld * 𝔞 d
      with 6 * 𝔞 Ld * (e1 - e2) + 6 * 𝔞 Ld * 𝔞 d' * (e4 - e3)
  exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- Floor stability: `f = ⌊a'/d'⌋` and `t = a/d` within `L/6` of `t'`, at distance `≥ L` from `f`, `f + 1`,
give `f ≤ t < f + 1`. -/
theorem floor_stable {a d a' d' Ln Ld : PTm n} (hd : Γ ⊢[PRAAx] le one d) (hd' : Γ ⊢[PRAAx] d' ≐ succ (pred d'))
    (hLn : Γ ⊢[PRAAx] le one Ln)
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (a * d') (a' * d)) (Ln * (d * d')))
    (sep0 : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (quo a' d' * d)))
    (sep1 : Γ ⊢[PRAAx] le (Ln * d) (Ld * adist a (succ (quo a' d') * d))) :
    Γ ⊢[PRAAx] le (quo a' d' * d) a ⋏ lt a (succ (quo a' d') * d) := by
  have dm := div_mod_at (Γ := Γ) (x := a') hd'
  have e := natEq (Prf.andE₁ dm)
  have hr : Γ ⊢[PRAAx] lt (rem a' d') d' := Prf.andE₂ dm
  have hd1 : Γ ⊢[PRAAx] le one d' := by have e' := natEq hd'; ipra_le 𝔞 (pred d') with e'
  have hlo : Γ ⊢[PRAAx] le (quo a' d' * d') a' := by ipra_le 𝔞 (rem a' d') with e
  have hhi : Γ ⊢[PRAAx] lt a' (succ (quo a' d') * d') := by ipra_le sl hr with e
  exact .andI (floor_low hd hd1 hLn hlo close sep0) (floor_high hd hd1 hLn hhi close sep1)

/-! ## The Möbius update of the complete quotient

For the convergents `P/Q`, `P'/Q'` (determinant `P'Q − PQ' = ±1`) and two rational approximations
`y = Y/W`, `z = Z/V` of `x` in the region `Qx > P`, `P' > Q'x`, the complete quotient
`t = (P' − Q'x)/(Qx − P)` is approximated by `t(y) = A/Dn`, `A = P'W − Q'Y`, `Dn = QY − PW` and
`t(z) = A'/Dn'`. The determinant identity
`(P'W − Q'Y)(QZ − PV) − (P'V − Q'Z)(QY − PW) = (P'Q − PQ')(WZ − VY)` gives
`|A Dn' − A' Dn| = |WZ − VY|` (`mobius_cross`), so the two quotients differ by
`|y − z| / (|Qy − P| |Qz − P|)`: the exact difference formula of the packet. -/

/-- `a + d = b + c` gives `|a − b| = |c − d|`. -/
theorem adist_of_eq {a b c d : PTm n} (h : Γ ⊢[PRAAx] a + d ≐ b + c) : Γ ⊢[PRAAx] adist a b ≐ adist c d := by
  refine .orE (le_total a b) ?_ ?_
  · let Θ : List (Fm PTm n) := le a b :: Γ
    have hab : Θ ⊢[PRAAx] le a b := Prf.hyp0
    have hcd : Θ ⊢[PRAAx] le c d := by have e' := natEq (h.wk : Θ ⊢[PRAAx] _); ipra_le sl hab with e'
    have q1 := adist_of_le hab
    have q2 := adist_of_le hcd
    have e1 := natEq (Prf.andE₁ q1)
    have e2 := natEq (Prf.andE₂ q1)
    have e3 := natEq (Prf.andE₁ q2)
    have e4 := natEq (Prf.andE₂ q2)
    ipra_lc e1 - e2 - e3 + e4 - natEq (h.wk : Θ ⊢[PRAAx] _)
  · let Θ : List (Fm PTm n) := le b a :: Γ
    have hba : Θ ⊢[PRAAx] le b a := Prf.hyp0
    have hdc : Θ ⊢[PRAAx] le d c := by have e' := natEq (h.wk : Θ ⊢[PRAAx] _); ipra_le sl hba with e'
    have q1 := adist_of_le hba
    have q2 := adist_of_le hdc
    have e1 := natEq (Prf.andE₁ q1)
    have e2 := natEq (Prf.andE₂ q1)
    have e3 := natEq (Prf.andE₁ q2)
    have e4 := natEq (Prf.andE₂ q2)
    ipra_lc e1 - e2 - e3 + e4 + natEq (h.wk : Θ ⊢[PRAAx] _)

/-- The determinant identity in the region `Qx > P`, `P' > Q'x` (both approximations on the same side),
for `P'Q = PQ' + 1`: `A Dn' + VY = A' Dn + WZ`. -/
theorem mobius_identity {P Q P' Q' Y W Z V A Dn A' Dn' : PTm n}
    (hdet : Γ ⊢[PRAAx] P' * Q ≐ P * Q' + one)
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn)
    (hA' : Γ ⊢[PRAAx] P' * V ≐ Q' * Z + A') (hD' : Γ ⊢[PRAAx] Q * Z ≐ P * V + Dn') :
    Γ ⊢[PRAAx] A * Dn' + V * Y ≐ A' * Dn + W * Z := by
  have ed := natEq hdet
  have eA := natEq hA
  have eD := natEq hD
  have eA' := natEq hA'
  have eD' := natEq hD'
  apply deriveNat; ipra_simps
  linear_combination (𝔞 W * 𝔞 Z - 𝔞 V * 𝔞 Y) * ed - 𝔞 Dn' * eA - (𝔞 P' * 𝔞 W - 𝔞 Q' * 𝔞 Y) * eD' +
    𝔞 Dn * eA' + (𝔞 P' * 𝔞 V - 𝔞 Q' * 𝔞 Z) * eD

/-- The same for `PQ' = P'Q + 1`: `A Dn' + WZ = A' Dn + VY`. -/
theorem mobius_identity' {P Q P' Q' Y W Z V A Dn A' Dn' : PTm n}
    (hdet : Γ ⊢[PRAAx] P * Q' ≐ P' * Q + one)
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn)
    (hA' : Γ ⊢[PRAAx] P' * V ≐ Q' * Z + A') (hD' : Γ ⊢[PRAAx] Q * Z ≐ P * V + Dn') :
    Γ ⊢[PRAAx] A * Dn' + W * Z ≐ A' * Dn + V * Y := by
  have ed := natEq hdet
  have eA := natEq hA
  have eD := natEq hD
  have eA' := natEq hA'
  have eD' := natEq hD'
  apply deriveNat; ipra_simps
  linear_combination (𝔞 V * 𝔞 Y - 𝔞 W * 𝔞 Z) * ed - 𝔞 Dn' * eA - (𝔞 P' * 𝔞 W - 𝔞 Q' * 𝔞 Y) * eD' +
    𝔞 Dn * eA' + (𝔞 P' * 𝔞 V - 𝔞 Q' * 𝔞 Z) * eD

/-- The exact difference formula, cleared: `|A Dn' − A' Dn| = |WZ − VY|` (either determinant sign). -/
theorem mobius_cross {P Q P' Q' Y W Z V A Dn A' Dn' : PTm n}
    (hdet : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one))
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn)
    (hA' : Γ ⊢[PRAAx] P' * V ≐ Q' * Z + A') (hD' : Γ ⊢[PRAAx] Q * Z ≐ P * V + Dn') :
    Γ ⊢[PRAAx] adist (A * Dn') (A' * Dn) ≐ adist (W * Z) (V * Y) := by
  refine .orE hdet ?_ ?_
  · exact adist_of_eq (mobius_identity Prf.hyp0 hA.wk hD.wk hA'.wk hD'.wk)
  · have h := adist_of_eq (mobius_identity' Prf.hyp0 hA.wk hD.wk hA'.wk hD'.wk)
    -- `|A Dn' − A' Dn| = |VY − WZ| = |WZ − VY|`
    exact h.eqTrans (add_comm _ _)

/-! ## Separation from the integers and the assembled digit step -/

/-- `t(y) − k = ((P' + kP) − (Q' + kQ) y)/(Qy − P)`, cleared: `|A − k Dn| = |(P' + kP)W − (Q' + kQ)Y|`. -/
theorem sep_numerator {P Q P' Q' Y W A Dn k : PTm n}
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn) :
    Γ ⊢[PRAAx] adist A (k * Dn) ≐ adist ((P' + k * P) * W) ((Q' + k * Q) * Y) := by
  refine adist_of_eq ?_
  ipra_lc -natEq hA + 𝔞 k * natEq hD

/-- The digit step: two approximations `Y/W`, `Z/V` of `x` (same region, determinant `±1`) whose difference is
small (`6 L_d |WZ − VY| ≤ L_n Dn Dn'`), with `Y/W` separated from the two fractions
`(P' + fP)/(Q' + fQ)`, `(P' + (f+1)P)/(Q' + (f+1)Q)` for `f = ⌊t(z)⌋`, give the same digit:
`⌊t(z)⌋ ≤ t(y) < ⌊t(z)⌋ + 1`. -/
theorem digit_stable {P Q P' Q' Y W Z V A Dn A' Dn' Ln Ld : PTm n}
    (hdet : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one))
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn)
    (hA' : Γ ⊢[PRAAx] P' * V ≐ Q' * Z + A') (hD' : Γ ⊢[PRAAx] Q * Z ≐ P * V + Dn')
    (hDn : Γ ⊢[PRAAx] le one Dn) (hDn' : Γ ⊢[PRAAx] Dn' ≐ succ (pred Dn')) (hLn : Γ ⊢[PRAAx] le one Ln)
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (W * Z) (V * Y)) (Ln * (Dn * Dn')))
    (sep0 : Γ ⊢[PRAAx] le (Ln * Dn) (Ld * adist ((P' + quo A' Dn' * P) * W) ((Q' + quo A' Dn' * Q) * Y)))
    (sep1 : Γ ⊢[PRAAx] le (Ln * Dn)
      (Ld * adist ((P' + succ (quo A' Dn') * P) * W) ((Q' + succ (quo A' Dn') * Q) * Y))) :
    Γ ⊢[PRAAx] le (quo A' Dn' * Dn) A ⋏ lt A (succ (quo A' Dn') * Dn) := by
  have mc := mobius_cross hdet hA hD hA' hD'
  have close' : Γ ⊢[PRAAx] le (num 6 * Ld * adist (A * Dn') (A' * Dn)) (Ln * (Dn * Dn')) :=
    le_congr (congrMul (.eqRefl _) mc).eqSymm (.eqRefl _) close
  have s0 : Γ ⊢[PRAAx] le (Ln * Dn) (Ld * adist A (quo A' Dn' * Dn)) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) (sep_numerator hA hD)).eqSymm sep0
  have s1 : Γ ⊢[PRAAx] le (Ln * Dn) (Ld * adist A (succ (quo A' Dn') * Dn)) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) (sep_numerator hA hD)).eqSymm sep1
  exact floor_stable hDn hDn' hLn close' s0 s1

/-! ## The loop invariants

One extraction step replaces `(P, Q, P', Q')` by `(aP + P', aQ + Q', P, Q)`. The determinant changes sign
(`det_step`, `det_step'`), and with `a Dn ≤ A` (the digit `a = ⌊A/Dn⌋`) the approximation moves to the other
sign region, with new numerator `Dn` and new denominator `A − a Dn`: the complete quotient becomes
`t_{n+1} = Dn/(A − a Dn) = 1/(t_n − a_n)` (`region_flip`, `region_flip'`). In region 2 (`Qx < P`,
`P' < Q'x`) the digit step is the region-1 step with `P ↔ Q`, `P' ↔ Q'`, `Y ↔ W`, `Z ↔ V`
(`digit_stable₂`). -/

/-- `P'Q = PQ' + 1` gives `(aP + P')Q = P(aQ + Q') + 1` for the next state. -/
theorem det_step {P Q P' Q' a : PTm n} (h : Γ ⊢[PRAAx] P' * Q ≐ P * Q' + one) :
    Γ ⊢[PRAAx] (a * P + P') * Q ≐ P * (a * Q + Q') + one := by
  ipra_lc natEq h

/-- `PQ' = P'Q + 1` gives `P(aQ + Q') = (aP + P')Q + 1` for the next state. -/
theorem det_step' {P Q P' Q' a : PTm n} (h : Γ ⊢[PRAAx] P * Q' ≐ P' * Q + one) :
    Γ ⊢[PRAAx] P * (a * Q + Q') ≐ (a * P + P') * Q + one := by
  ipra_lc natEq h

/-- From region 1 (`P'W = Q'Y + A`, `QY = PW + Dn`) with `a Dn ≤ A`, the next state is in region 2:
`(aP + P')W = (aQ + Q')Y + (A − a Dn)` and `QY = PW + Dn`. -/
theorem region_flip {P Q P' Q' Y W A Dn a : PTm n}
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn)
    (ha : Γ ⊢[PRAAx] le (a * Dn) A) :
    Γ ⊢[PRAAx] (a * P + P') * W ≐ (a * Q + Q') * Y + monus A (a * Dn) := by
  ipra_lc natEq hA - 𝔞 a * natEq hD + natEq (eq_add_of_le ha)

/-- From region 2 (`Q'Y = P'W + A`, `PW = QY + Dn`) with `a Dn ≤ A`, the next state is in region 1:
`(aQ + Q')Y = (aP + P')W + (A − a Dn)` and `PW = QY + Dn`. -/
theorem region_flip' {P Q P' Q' Y W A Dn a : PTm n}
    (hA : Γ ⊢[PRAAx] Q' * Y ≐ P' * W + A) (hD : Γ ⊢[PRAAx] P * W ≐ Q * Y + Dn)
    (ha : Γ ⊢[PRAAx] le (a * Dn) A) :
    Γ ⊢[PRAAx] (a * Q + Q') * Y ≐ (a * P + P') * W + monus A (a * Dn) := by
  ipra_lc natEq hA - 𝔞 a * natEq hD + natEq (eq_add_of_le ha)

/-- The digit step in region 2 (`Qx < P`, `P' < Q'x`): the region-1 step with `P ↔ Q`, `P' ↔ Q'`,
`Y ↔ W`, `Z ↔ V`. -/
theorem digit_stable₂ {P Q P' Q' Y W Z V A Dn A' Dn' Ln Ld : PTm n}
    (hdet : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one))
    (hA : Γ ⊢[PRAAx] Q' * Y ≐ P' * W + A) (hD : Γ ⊢[PRAAx] P * W ≐ Q * Y + Dn)
    (hA' : Γ ⊢[PRAAx] Q' * Z ≐ P' * V + A') (hD' : Γ ⊢[PRAAx] P * V ≐ Q * Z + Dn')
    (hDn : Γ ⊢[PRAAx] le one Dn) (hDn' : Γ ⊢[PRAAx] Dn' ≐ succ (pred Dn')) (hLn : Γ ⊢[PRAAx] le one Ln)
    (close : Γ ⊢[PRAAx] le (num 6 * Ld * adist (Y * V) (Z * W)) (Ln * (Dn * Dn')))
    (sep0 : Γ ⊢[PRAAx] le (Ln * Dn) (Ld * adist ((Q' + quo A' Dn' * Q) * Y) ((P' + quo A' Dn' * P) * W)))
    (sep1 : Γ ⊢[PRAAx] le (Ln * Dn)
      (Ld * adist ((Q' + succ (quo A' Dn') * Q) * Y) ((P' + succ (quo A' Dn') * P) * W))) :
    Γ ⊢[PRAAx] le (quo A' Dn' * Dn) A ⋏ lt A (succ (quo A' Dn') * Dn) := by
  have hdet' : Γ ⊢[PRAAx] (Q' * P ≐ Q * P' + one) ⋎ (Q * P' ≐ Q' * P + one) := by
    refine .orE hdet ?_ ?_
    · exact .orI₂ ((mul_comm _ _).eqTrans (Prf.hyp0.eqTrans (congrAdd (mul_comm _ _) (.eqRefl _))))
    · exact .orI₁ ((mul_comm _ _).eqTrans (Prf.hyp0.eqTrans (congrAdd (mul_comm _ _) (.eqRefl _))))
  exact digit_stable (P := Q) (Q := P) (P' := Q') (Q' := P') (Y := W) (W := Y) (Z := V) (V := Z)
    hdet' hA hD hA' hD' hDn hDn' hLn close sep0 sep1

/-! ## From a separated Cauchy name to the step hypotheses

The packet's input is a primitive recursive Cauchy name with an irrationality modulus: at the working precision
the approximation `y = Y/W` satisfies `|p − q y| ≥ σ = σ_n/σ_d` for the finitely many fractions `p/q` that
occur, and `|Qy − P| ≤ E`. Then `L = σ/E` is a valid gap (`sep_transfer`), and a Cauchy bound
`|WZ − VY| ≤ C` for a second approximation with `6 L_d C ≤ L_n Dn Dn'` gives the closeness hypothesis
(`close_from_cauchy`). `digit_from_name` is the digit step with these name-level hypotheses. -/

/-- `|p − qy| ≥ σ` (`σ_n W ≤ σ_d |pW − qY|`) and `|Qy − P| ≤ E` (`Dn ≤ E W`) give the gap hypothesis
`σ_n Dn ≤ (σ_d E) |pW − qY|` of `L = σ/E`. -/
theorem sep_transfer {σn σd W X Dn E : PTm n} (hs : Γ ⊢[PRAAx] le (σn * W) (σd * X))
    (hE : Γ ⊢[PRAAx] le Dn (E * W)) : Γ ⊢[PRAAx] le (σn * Dn) (σd * E * X) := by
  ipra_le 𝔞 E * sl hs + 𝔞 σn * sl hE

/-- A Cauchy bound `|WZ − VY| ≤ C` with `6 L_d C ≤ L_n Dn Dn'` gives the closeness hypothesis. -/
theorem close_from_cauchy {W Z V Y C Ld Ln Dn Dn' : PTm n} (hc : Γ ⊢[PRAAx] le (adist (W * Z) (V * Y)) C)
    (h6 : Γ ⊢[PRAAx] le (num 6 * Ld * C) (Ln * (Dn * Dn'))) :
    Γ ⊢[PRAAx] le (num 6 * Ld * adist (W * Z) (V * Y)) (Ln * (Dn * Dn')) := by
  ipra_le 6 * 𝔞 Ld * sl hc + sl h6

/-- The digit step from name-level hypotheses (region 1): a separation `σ` of `Y/W` from the two neighbouring
fractions, `|Qy − P| ≤ E`, and a Cauchy bound `C` with `6 σ_d E C ≤ σ_n Dn Dn'`. -/
theorem digit_from_name {P Q P' Q' Y W Z V A Dn A' Dn' σn σd E C : PTm n}
    (hdet : Γ ⊢[PRAAx] (P' * Q ≐ P * Q' + one) ⋎ (P * Q' ≐ P' * Q + one))
    (hA : Γ ⊢[PRAAx] P' * W ≐ Q' * Y + A) (hD : Γ ⊢[PRAAx] Q * Y ≐ P * W + Dn)
    (hA' : Γ ⊢[PRAAx] P' * V ≐ Q' * Z + A') (hD' : Γ ⊢[PRAAx] Q * Z ≐ P * V + Dn')
    (hDn : Γ ⊢[PRAAx] le one Dn) (hDn' : Γ ⊢[PRAAx] Dn' ≐ succ (pred Dn')) (hσ : Γ ⊢[PRAAx] le one σn)
    (hE : Γ ⊢[PRAAx] le Dn (E * W)) (hc : Γ ⊢[PRAAx] le (adist (W * Z) (V * Y)) C)
    (h6 : Γ ⊢[PRAAx] le (num 6 * (σd * E) * C) (σn * (Dn * Dn')))
    (hs0 : Γ ⊢[PRAAx] le (σn * W) (σd * adist ((P' + quo A' Dn' * P) * W) ((Q' + quo A' Dn' * Q) * Y)))
    (hs1 : Γ ⊢[PRAAx] le (σn * W)
      (σd * adist ((P' + succ (quo A' Dn') * P) * W) ((Q' + succ (quo A' Dn') * Q) * Y))) :
    Γ ⊢[PRAAx] le (quo A' Dn' * Dn) A ⋏ lt A (succ (quo A' Dn') * Dn) :=
  digit_stable (Ld := σd * E) hdet hA hD hA' hD' hDn hDn' hσ (close_from_cauchy hc h6)
    (sep_transfer hs0 hE) (sep_transfer hs1 hE)

end LeanProofs.IPRA.DiophantineNumberTheory.HurwitzExtraction
