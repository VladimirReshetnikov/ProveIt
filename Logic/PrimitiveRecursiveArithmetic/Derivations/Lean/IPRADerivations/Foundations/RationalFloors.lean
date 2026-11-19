import IPRADerivations.Topology.DimensionUnits

/-!
# Floors of rationals with different denominators

Framework for passing from a table of rationals to a table of naturals by `⌊D·value/h⌋` (packet
`topology/dimension_invariance_ipra`, the reduction of a rational table to natural units used by
`thm:finite`; reusable wherever rational comparisons are turned into comparisons of floors).

Quotients `A/r`, `B/s` with positive denominators `r = succ cr`, `s = succ cs`:

* `quo_far`: `A s = B r + D r s + E` (that is, `A/r ≥ B/s + D`) gives `⌊B/s⌋ + D ≤ ⌊A/r⌋`;
* `quo_le_succ`: `A s < B r + r s` (that is, `A/r < B/s + 1`) gives `⌊A/r⌋ ≤ ⌊B/s⌋ + 1`;
* `quo_near`: both bounds give `|⌊A/r⌋ − ⌊B/s⌋| ≤ 1`;
* `le_dist_of_le_add`: `y + D ≤ x` gives `D ≤ |x − y|`.

A rational is coded by three naturals as `(P − Q)/(R + 1)` and the unit by `h = (h₁ + 1)/(h₂ + 1)`.
With an offset `S ≥ Q` (the same `S` for every entry of a table) the natural value

  `⌊D (h₂+1)(P + (S (h₁+1)(R+1) ∸ Q)) / ((h₁+1)(R+1))⌋ = ⌊D (P − Q)/((R+1) h)⌋ + D (h₂+1) S`

(`numer`/`denom`) is a floor of `D·value/h` up to a common translation. Two values `u`, `v` differ by
`(X − Y)/((R_u+1)(R_v+1))` with the cross terms `X = P_u (R_v+1) + Q_v (R_u+1)`,
`Y = P_v (R_u+1) + Q_u (R_v+1)` (`crossX`, `crossY`), so every rational comparison is a comparison of
naturals:

* `rat_far`: `|value_u − value_v| ≥ h`, i.e. `h₁' (R_u+1)(R_v+1) ≤ h₂' |X − Y|`, gives floors at
  distance `≥ D`;
* `rat_near`: `D |value_u − value_v| < h`, i.e. `D h₂' |X − Y| < h₁' (R_u+1)(R_v+1)`, gives floors at
  distance `≤ 1`.
-/

namespace LeanProofs.IPRA.Foundations.RationalFloors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.StaggeredCells (near dist)
open LeanProofs.IPRA.Topology.DimensionUnits (dist_of_add dist_comm dist_le_one_of_near)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Two quotients -/

/-- `A/r ≥ B/s + D` gives `⌊B/s⌋ + D ≤ ⌊A/r⌋`. -/
theorem quo_far {A B r s Dn E cr cs : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ cr) (hs : Γ ⊢[PRAAx] s ≐ succ cs)
    (h : Γ ⊢[PRAAx] A * s ≐ B * r + Dn * (r * s) + E) :
    Γ ⊢[PRAAx] le (quo B s + Dn) (quo A r) := by
  refine .orE (lt_or_le (quo A r) (quo B s + Dn)) ?_ Prf.hyp0
  let Δ : List (Fm PTm n) := lt (quo A r) (quo B s + Dn) :: Γ
  have dA := div_mod_at (Γ := Δ) (x := A) hr.wk
  have dB := div_mod_at (Γ := Δ) (x := B) hs.wk
  have e0 := natEq (Γ := Δ) h.wk
  have e1 := natEq (Prf.andE₁ dA)
  have e2 := natEq (Prf.andE₁ dB)
  have e3 := natEq (eq_add_of_le (Prf.andE₂ dA))
  have e4 := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
  have e5 := natEq (Γ := Δ) hs.wk
  refine .botE _ (succ_ne_zero (a := cs + monus r (succ (rem A r)) * s +
    monus (quo B s + Dn) (succ (quo A r)) * (r * s) + rem B s * r + E) ?_)
  apply deriveNat; ipra_simps
  linear_combination -e0 + 𝔞 s * e1 - 𝔞 r * e2 - 𝔞 s * e3 - (𝔞 r * 𝔞 s) * e4 - e5

/-- `A/r < B/s + 1` gives `⌊A/r⌋ ≤ ⌊B/s⌋ + 1`. -/
theorem quo_le_succ {A B r s cr cs : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ cr) (hs : Γ ⊢[PRAAx] s ≐ succ cs)
    (h : Γ ⊢[PRAAx] lt (A * s) (B * r + r * s)) :
    Γ ⊢[PRAAx] le (quo A r) (succ (quo B s)) := by
  refine .orE (lt_or_le (succ (quo B s)) (quo A r)) ?_ Prf.hyp0
  let Δ : List (Fm PTm n) := lt (succ (quo B s)) (quo A r) :: Γ
  have dA := div_mod_at (Γ := Δ) (x := A) hr.wk
  have dB := div_mod_at (Γ := Δ) (x := B) hs.wk
  have e0 := natEq (eq_add_of_le (Γ := Δ) h.wk)
  have e1 := natEq (Prf.andE₁ dA)
  have e2 := natEq (Prf.andE₁ dB)
  have e3 := natEq (eq_add_of_le (Prf.andE₂ dB))
  have e4 := natEq (eq_add_of_le (Γ := Δ) Prf.hyp0)
  refine .botE _ (succ_ne_zero (a := r + monus s (succ (rem B s)) * r +
    monus (quo A r) (succ (succ (quo B s))) * (r * s) + rem A r * s +
    monus (B * r + r * s) (succ (A * s))) ?_)
  apply deriveNat; ipra_simps
  linear_combination -e0 + 𝔞 r * e2 - 𝔞 s * e1 - (𝔞 r * 𝔞 s) * e4 - 𝔞 r * e3

/-- `|A/r − B/s| < 1` gives `|⌊A/r⌋ − ⌊B/s⌋| ≤ 1`. -/
theorem quo_near {A B r s cr cs : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ cr) (hs : Γ ⊢[PRAAx] s ≐ succ cs)
    (h₁ : Γ ⊢[PRAAx] lt (A * s) (B * r + r * s)) (h₂ : Γ ⊢[PRAAx] lt (B * r) (A * s + s * r)) :
    Γ ⊢[PRAAx] le (dist (quo A r) (quo B s)) one :=
  dist_le_one_of_near (.andI (quo_le_succ hr hs h₁) (quo_le_succ hs hr h₂))

/-- `y + D ≤ x` gives `D ≤ |x − y|`. -/
theorem le_dist_of_le_add {x y Dn : PTm n} (h : Γ ⊢[PRAAx] le (y + Dn) x) : Γ ⊢[PRAAx] le Dn (dist x y) := by
  have e : Γ ⊢[PRAAx] x ≐ y + (Dn + monus x (y + Dn)) := by
    have a := natEq (eq_add_of_le h)
    apply deriveNat; ipra_simps; linear_combination a
  exact le_congr (.eqRefl _) (dist_of_add e).eqSymm (le_add_right _ _)

/-! ## Rational values with a common offset -/

/-- The numerator `D h₂' (P + (S h₁' R' ∸ Q))` of the scaled, translated value. -/
def numer (Dn h₁ h₂ S P Q R : PTm n) : PTm n :=
  Dn * succ h₂ * (P + monus (S * succ h₁ * succ R) Q)

/-- The denominator `h₁' R'`. -/
def denom (h₁ R : PTm n) : PTm n := succ h₁ * succ R

/-- The cross term `P_u R_v' + Q_v R_u'`. -/
def crossX (Pu _Qu Ru _Pv Qv Rv : PTm n) : PTm n := Pu * succ Rv + Qv * succ Ru

/-- The cross term `P_v R_u' + Q_u R_v'`. -/
def crossY (_Pu Qu Ru Pv _Qv Rv : PTm n) : PTm n := Pv * succ Ru + Qu * succ Rv

@[simp] theorem subst_numer {k : ℕ} (σ : Fin n → PTm k) (Dn h₁ h₂ S P Q R : PTm n) :
    Syn.subst σ (numer Dn h₁ h₂ S P Q R) =
      numer (Syn.subst σ Dn) (Syn.subst σ h₁) (Syn.subst σ h₂) (Syn.subst σ S) (Syn.subst σ P)
        (Syn.subst σ Q) (Syn.subst σ R) := by
  simp [numer]

@[simp] theorem subst_denom {k : ℕ} (σ : Fin n → PTm k) (h₁ R : PTm n) :
    Syn.subst σ (denom h₁ R) = denom (Syn.subst σ h₁) (Syn.subst σ R) := by
  simp [denom]

@[simp] theorem subst_crossX {k : ℕ} (σ : Fin n → PTm k) (Pu Qu Ru Pv Qv Rv : PTm n) :
    Syn.subst σ (crossX Pu Qu Ru Pv Qv Rv) = crossX (Syn.subst σ Pu) (Syn.subst σ Qu) (Syn.subst σ Ru)
      (Syn.subst σ Pv) (Syn.subst σ Qv) (Syn.subst σ Rv) := by
  simp [crossX]

@[simp] theorem subst_crossY {k : ℕ} (σ : Fin n → PTm k) (Pu Qu Ru Pv Qv Rv : PTm n) :
    Syn.subst σ (crossY Pu Qu Ru Pv Qv Rv) = crossY (Syn.subst σ Pu) (Syn.subst σ Qu) (Syn.subst σ Ru)
      (Syn.subst σ Pv) (Syn.subst σ Qv) (Syn.subst σ Rv) := by
  simp [crossY]

theorem crossX_swap (Pu Qu Ru Pv Qv Rv : PTm n) :
    crossX Pv Qv Rv Pu Qu Ru = crossY Pu Qu Ru Pv Qv Rv := rfl

theorem crossY_swap (Pu Qu Ru Pv Qv Rv : PTm n) :
    crossY Pv Qv Rv Pu Qu Ru = crossX Pu Qu Ru Pv Qv Rv := rfl

theorem denom_succ (h₁ R : PTm n) : Γ ⊢[PRAAx] denom h₁ R ≐ succ (h₁ + R * succ h₁) := by
  apply deriveNat; simp only [denom]; ipra_simps; ring

/-- `Q ≤ S` gives `S h₁' R' = Q + (S h₁' R' ∸ Q)`. -/
theorem offset_eq {S Q h₁ R : PTm n} (hQ : Γ ⊢[PRAAx] le Q S) :
    Γ ⊢[PRAAx] S * succ h₁ * succ R ≐ Q + monus (S * succ h₁ * succ R) Q := by
  refine eq_add_of_le (le_trans hQ (le_of_eq_add (d := S * (h₁ * R + h₁ + R)) ?_))
  apply deriveNat; ipra_simps; ring

section Pair

variable {Dn h₁ h₂ S Pu Qu Ru Pv Qv Rv : PTm n}

/-- The far case for `Y ≤ X`. -/
private theorem rat_far_le (hQu : Γ ⊢[PRAAx] le Qu S) (hQv : Γ ⊢[PRAAx] le Qv S)
    (hle : Γ ⊢[PRAAx] le (crossY Pu Qu Ru Pv Qv Rv) (crossX Pu Qu Ru Pv Qv Rv))
    (h : Γ ⊢[PRAAx] le (succ h₁ * (succ Ru * succ Rv))
      (succ h₂ * dist (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv))) :
    Γ ⊢[PRAAx] le Dn (dist (quo (numer Dn h₁ h₂ S Pu Qu Ru) (denom h₁ Ru))
      (quo (numer Dn h₁ h₂ S Pv Qv Rv) (denom h₁ Rv))) := by
  have hX := eq_add_of_le hle
  have hd := dist_of_add hX
  have hε := eq_add_of_le (le_congr (.eqRefl _) (congrMul (.eqRefl _) hd) h)
  have kU := natEq (offset_eq (h₁ := h₁) (R := Ru) hQu)
  have kV := natEq (offset_eq (h₁ := h₁) (R := Rv) hQv)
  have eX := natEq hX
  have eε := natEq hε
  refine le_dist_of_le_add (quo_far (denom_succ h₁ Ru) (denom_succ h₁ Rv)
    (E := Dn * succ h₁ * monus (succ h₂ * monus (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv))
      (succ h₁ * (succ Ru * succ Rv))) ?_)
  apply deriveNat
  simp only [numer, denom, crossX, crossY] at kU kV eX eε ⊢
  ipra_simps
  linear_combination
    -(𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1) * (𝔞 Rv + 1)) * kU +
      (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1) * (𝔞 Ru + 1)) * kV +
      (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1)) * eX + (𝔞 Dn * (𝔞 h₁ + 1)) * eε

/-- `|value_u − value_v| ≥ h` gives floors at distance `≥ D`. -/
theorem rat_far (hQu : Γ ⊢[PRAAx] le Qu S) (hQv : Γ ⊢[PRAAx] le Qv S)
    (h : Γ ⊢[PRAAx] le (succ h₁ * (succ Ru * succ Rv))
      (succ h₂ * dist (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv))) :
    Γ ⊢[PRAAx] le Dn (dist (quo (numer Dn h₁ h₂ S Pu Qu Ru) (denom h₁ Ru))
      (quo (numer Dn h₁ h₂ S Pv Qv Rv) (denom h₁ Rv))) := by
  refine .orE (le_total (crossY Pu Qu Ru Pv Qv Rv) (crossX Pu Qu Ru Pv Qv Rv))
    (rat_far_le hQu.wk hQv.wk Prf.hyp0 h.wk) ?_
  have h' : (le (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv) :: Γ) ⊢[PRAAx]
      le (succ h₁ * (succ Rv * succ Ru)) (succ h₂ * dist (crossX Pv Qv Rv Pu Qu Ru) (crossY Pv Qv Rv Pu Qu Ru)) := by
    rw [crossX_swap, crossY_swap]
    exact le_congr (congrMul (.eqRefl _) (mul_comm _ _)) (congrMul (.eqRefl _) (dist_comm _ _)) h.wk
  have r := rat_far_le (Dn := Dn) (h₂ := h₂) hQv.wk hQu.wk (by rw [crossX_swap, crossY_swap]; exact Prf.hyp0) h'
  exact le_congr (.eqRefl _) (dist_comm _ _) r

/-- The near case for `Y ≤ X`. -/
private theorem rat_near_le (hQu : Γ ⊢[PRAAx] le Qu S) (hQv : Γ ⊢[PRAAx] le Qv S)
    (hle : Γ ⊢[PRAAx] le (crossY Pu Qu Ru Pv Qv Rv) (crossX Pu Qu Ru Pv Qv Rv))
    (h : Γ ⊢[PRAAx] lt (Dn * succ h₂ * dist (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv))
      (succ h₁ * (succ Ru * succ Rv))) :
    Γ ⊢[PRAAx] le (dist (quo (numer Dn h₁ h₂ S Pu Qu Ru) (denom h₁ Ru))
      (quo (numer Dn h₁ h₂ S Pv Qv Rv) (denom h₁ Rv))) one := by
  have hX := eq_add_of_le hle
  have hd := dist_of_add hX
  have hε := eq_add_of_le (lt_congr (congrMul (.eqRefl _) hd) (.eqRefl _) h)
  have kU := natEq (offset_eq (h₁ := h₁) (R := Ru) hQu)
  have kV := natEq (offset_eq (h₁ := h₁) (R := Rv) hQv)
  have eX := natEq hX
  have eε := natEq hε
  let δ := monus (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv)
  let ε := monus (succ h₁ * (succ Ru * succ Rv)) (succ (Dn * succ h₂ * δ))
  refine quo_near (denom_succ h₁ Ru) (denom_succ h₁ Rv) ?_ ?_
  · refine le_of_eq_add (d := h₁ + succ h₁ * ε) ?_
    apply deriveNat
    simp only [numer, denom, crossX, crossY, δ, ε] at kU kV eX eε ⊢
    ipra_simps
    linear_combination
      (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1) * (𝔞 Rv + 1)) * kU -
        (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1) * (𝔞 Ru + 1)) * kV -
        (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1)) * eX + (𝔞 h₁ + 1) * eε
  · refine le_of_eq_add (d := Dn * succ h₁ * succ h₂ * δ + Dn * succ h₁ * succ h₂ * δ + h₁ + succ h₁ * ε) ?_
    apply deriveNat
    simp only [numer, denom, crossX, crossY, δ, ε] at kU kV eX eε ⊢
    ipra_simps
    linear_combination
      -(𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1) * (𝔞 Rv + 1)) * kU +
        (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1) * (𝔞 Ru + 1)) * kV +
        (𝔞 Dn * (𝔞 h₁ + 1) * (𝔞 h₂ + 1)) * eX + (𝔞 h₁ + 1) * eε

/-- `D |value_u − value_v| < h` gives floors at distance `≤ 1`. -/
theorem rat_near (hQu : Γ ⊢[PRAAx] le Qu S) (hQv : Γ ⊢[PRAAx] le Qv S)
    (h : Γ ⊢[PRAAx] lt (Dn * succ h₂ * dist (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv))
      (succ h₁ * (succ Ru * succ Rv))) :
    Γ ⊢[PRAAx] le (dist (quo (numer Dn h₁ h₂ S Pu Qu Ru) (denom h₁ Ru))
      (quo (numer Dn h₁ h₂ S Pv Qv Rv) (denom h₁ Rv))) one := by
  refine .orE (le_total (crossY Pu Qu Ru Pv Qv Rv) (crossX Pu Qu Ru Pv Qv Rv))
    (rat_near_le hQu.wk hQv.wk Prf.hyp0 h.wk) ?_
  have h' : (le (crossX Pu Qu Ru Pv Qv Rv) (crossY Pu Qu Ru Pv Qv Rv) :: Γ) ⊢[PRAAx]
      lt (Dn * succ h₂ * dist (crossX Pv Qv Rv Pu Qu Ru) (crossY Pv Qv Rv Pu Qu Ru)) (succ h₁ * (succ Rv * succ Ru)) := by
    rw [crossX_swap, crossY_swap]
    exact lt_congr (congrMul (.eqRefl _) (dist_comm _ _)) (congrMul (.eqRefl _) (mul_comm _ _)) h.wk
  have r := rat_near_le (S := S) hQv.wk hQu.wk (by rw [crossX_swap, crossY_swap]; exact Prf.hyp0) h'
  exact le_congr (dist_comm _ _) (.eqRefl _) r

end Pair

end LeanProofs.IPRA.Foundations.RationalFloors
