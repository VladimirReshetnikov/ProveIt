import IPRADerivations.Core.Tactic
import IPRADerivations.Core.Powers

/-!
# Localization witnesses and the power-cover constructor

Packet: `geometry/ipra_algebraic_geometry_framework_2026-11-15` (Sections "Localization as a
certified setoid", `thm:localization-calculus`, and "The explicit power-cover lemma",
`thm:power-cover`). The ring is the integers; a fraction `a / f^n` is a pair, and an equality
witness from `a / f^n` to `b / f^m` is a killing exponent `k` with `f^k (f^m a − f^n b) = 0`.

The rules of the calculus do not use that the multipliers are powers of one element, so they are
stated for arbitrary multipliers `Pk, Pm, Pn, …` standing for `f^k, f^m, f^n, …`:

* `loc_refl`, `loc_symm`, `loc_weaken`;
* `loc_trans`: witnesses `Pk (Pm a − Pn b) = 0` and `Pl (Pr b − Pm c) = 0` give
  `Pk Pl Pm (Pr a − Pn c) = 0`;
* `loc_trans_pow`: the same for powers of a natural number `f`, with the killing exponent
  `k + l + m` of the packet;
* `loc_add`, `loc_mul`: addition and multiplication of fractions respect the witnesses;
* `loc_universal`: with inverse witnesses `Vk Pk = Vm Pm = Vn Pn = 1`, a witness gives
  `a Vn = b Vm`, the equality of the images under `a / f^n ↦ φ(a) v^n`.

The power-cover constructor, for a cover certificate `∑ cᵢ fᵢ = 1`:

* `cover22_id`, `cover23_id`, `cover32_id`: the bucketed expansions
  `∑ dᵢ fᵢ^N = (∑ cᵢ fᵢ)^M`, `M = r (N − 1) + 1`, for `(r, N) = (2, 2), (2, 3), (3, 2)`, with
  the coefficients `dᵢ` of the packet's formula;
* `cover22`, `cover23`, `cover32`: hence `∑ dᵢ fᵢ^N = 1`;
* `cover_step`: for two generators and every exponent, an explicit update of the coefficients
  turns a certificate for the powers `N + 1` into one for `N + 2`;
* `cover_example`: for `f = (2, 3)`, `c = (−1, 1)` and `N = 2` the constructor returns
  `d = (7, −3)`, and `7 · 2² − 3 · 3² = 1`.

For two generators every `N` is reached by iterating `cover_step`; the statement for all `N`
is `Geometry/PowerCover`. More generators, quotient presentations and the gluing theorems are
not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.LocalizationWitness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔷" t:max => ZT.toZ _ t
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The witness calculus -/

section Calculus

variable {a b c a' b' Pk Pl Pm Pn Pr Pm' Pn' Pj Vk Vm Vn : ZT n}

/-- Reflexivity, with killing exponent `0`. -/
theorem loc_refl (a Pn : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 1 * (Pn * a - Pn * a)) (ZT.natLit 0) := by
  ipra_ring

theorem loc_symm (h : Γ ⊢[PRAAx] ZT.eq (Pk * (Pm * a - Pn * b)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (Pk * (Pn * b - Pm * a)) (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  linear_combination -e

/-- A killing exponent may be enlarged. -/
theorem loc_weaken (Pj : ZT n) (h : Γ ⊢[PRAAx] ZT.eq (Pk * (Pm * a - Pn * b)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (Pj * Pk * (Pm * a - Pn * b)) (ZT.natLit 0) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  linear_combination 𝔷(Pj) * e

/-- Transitivity: `a / f^n ~ b / f^m` and `b / f^m ~ c / f^r` give `a / f^n ~ c / f^r`. -/
theorem loc_trans (h₁ : Γ ⊢[PRAAx] ZT.eq (Pk * (Pm * a - Pn * b)) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Pl * (Pr * b - Pm * c)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (Pk * Pl * Pm * (Pr * a - Pn * c)) (ZT.natLit 0) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  linear_combination 𝔷(Pl) * 𝔷(Pr) * e₁ + 𝔷(Pk) * 𝔷(Pn) * e₂

/-- Addition: `a / f^n ~ a' / f^n'` and `b / f^m ~ b' / f^m'` give
`(f^m a + f^n b) / f^(n+m) ~ (f^m' a' + f^n' b') / f^(n'+m')`. -/
theorem loc_add (h₁ : Γ ⊢[PRAAx] ZT.eq (Pk * (Pn' * a - Pn * a')) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Pl * (Pm' * b - Pm * b')) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq
      (Pk * Pl * (Pn' * Pm' * (Pm * a + Pn * b) - Pn * Pm * (Pm' * a' + Pn' * b'))) (ZT.natLit 0) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  linear_combination 𝔷(Pl) * 𝔷(Pm) * 𝔷(Pm') * e₁ + 𝔷(Pk) * 𝔷(Pn) * 𝔷(Pn') * e₂

/-- Multiplication: the same witnesses give `a b / f^(n+m) ~ a' b' / f^(n'+m')`. -/
theorem loc_mul (h₁ : Γ ⊢[PRAAx] ZT.eq (Pk * (Pn' * a - Pn * a')) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (Pl * (Pm' * b - Pm * b')) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (Pk * Pl * (Pn' * Pm' * (a * b) - Pn * Pm * (a' * b'))) (ZT.natLit 0) := by
  have e₁ := ZT.toZ_eq h₁; have e₂ := ZT.toZ_eq h₂
  apply ZT.derive
  ipra_simps
  linear_combination 𝔷(Pl) * 𝔷(Pm') * 𝔷(b) * e₁ + 𝔷(Pk) * 𝔷(Pn) * 𝔷(a') * e₂

/-- The universal property on a witness: if the multipliers have inverses `Vk, Vm, Vn`, then
`a / f^n ~ b / f^m` gives `a Vn = b Vm`. -/
theorem loc_universal (hk : Γ ⊢[PRAAx] ZT.eq (Vk * Pk) (ZT.natLit 1))
    (hm : Γ ⊢[PRAAx] ZT.eq (Vm * Pm) (ZT.natLit 1)) (hn : Γ ⊢[PRAAx] ZT.eq (Vn * Pn) (ZT.natLit 1))
    (h : Γ ⊢[PRAAx] ZT.eq (Pk * (Pm * a - Pn * b)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (a * Vn) (b * Vm) := by
  have ek := ZT.toZ_eq hk; have em := ZT.toZ_eq hm; have en := ZT.toZ_eq hn; have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  linear_combination 𝔷(Vk) * 𝔷(Vn) * 𝔷(Vm) * e -
    𝔷(Vn) * 𝔷(Vm) * (𝔷(Pm) * 𝔷(a) - 𝔷(Pn) * 𝔷(b)) * ek - 𝔷(Vn) * 𝔷(a) * em + 𝔷(Vm) * 𝔷(b) * en

end Calculus

/-! ## Powers of a natural number -/

/-- `f^k` as an integer. -/
abbrev fp {n : ℕ} (f k : PTm n) : ZT n := ZT.ofNat (pw f k)

/-- Transitivity with the killing exponent `k + l + m` of the packet. -/
theorem loc_trans_pow {f k l m r s : PTm n} {a b c : ZT n}
    (h₁ : Γ ⊢[PRAAx] ZT.eq (fp f k * (fp f m * a - fp f s * b)) (ZT.natLit 0))
    (h₂ : Γ ⊢[PRAAx] ZT.eq (fp f l * (fp f r * b - fp f m * c)) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (fp f (k + l + m) * (fp f r * a - fp f s * c)) (ZT.natLit 0) := by
  have e := ZT.toZ_eq (loc_trans h₁ h₂)
  have p₁ := natEq (pw_add (Γ := Γ) f (k + l) m); have p₂ := natEq (pw_add (Γ := Γ) f k l)
  apply ZT.derive
  ipra_simps
  linear_combination e + (𝔞(pw f r) * 𝔷(a) - 𝔞(pw f s) * 𝔷(c)) * p₁ +
    𝔞(pw f m) * (𝔞(pw f r) * 𝔷(a) - 𝔞(pw f s) * 𝔷(c)) * p₂

/-! ## The power-cover constructor -/

section PowerCover

abbrev p2 {n : ℕ} (u : ZT n) : ZT n := u * u
abbrev p3 {n : ℕ} (u : ZT n) : ZT n := u * u * u
abbrev p4 {n : ℕ} (u : ZT n) : ZT n := u * u * u * u
abbrev p5 {n : ℕ} (u : ZT n) : ZT n := u * u * u * u * u

variable (c₀ c₁ c₂ f₀ f₁ f₂ : ZT n)

/-- `r = 2`, `N = 2`: the bucket of `f₀²` in `(c₀ f₀ + c₁ f₁)³`. -/
abbrev d22₀ : ZT n := p3 c₀ * f₀ + ZT.natLit 3 * (p2 c₀ * c₁ * f₁)
/-- `r = 2`, `N = 2`: the bucket of `f₁²`. -/
abbrev d22₁ : ZT n := ZT.natLit 3 * (c₀ * p2 c₁ * f₀) + p3 c₁ * f₁

/-- `r = 2`, `N = 3`: the bucket of `f₀³` in `(c₀ f₀ + c₁ f₁)⁵`. -/
abbrev d23₀ : ZT n :=
  p5 c₀ * p2 f₀ + ZT.natLit 5 * (p4 c₀ * c₁ * f₀ * f₁) + ZT.natLit 10 * (p3 c₀ * p2 c₁ * p2 f₁)
/-- `r = 2`, `N = 3`: the bucket of `f₁³`. -/
abbrev d23₁ : ZT n :=
  ZT.natLit 10 * (p2 c₀ * p3 c₁ * p2 f₀) + ZT.natLit 5 * (c₀ * p4 c₁ * f₀ * f₁) + p5 c₁ * p2 f₁

/-- `r = 3`, `N = 2`: the bucket of `f₀²` in `(u + v + w)⁴`, `u = c₀ f₀`, `v = c₁ f₁`,
`w = c₂ f₂`. A term goes to the least index whose exponent is at least `2`. -/
abbrev d32₀ : ZT n :=
  p2 c₀ * (p2 (c₀ * f₀) + ZT.natLit 4 * ((c₀ * f₀) * (c₁ * f₁)) + ZT.natLit 4 * ((c₀ * f₀) * (c₂ * f₂)) +
    ZT.natLit 6 * p2 (c₁ * f₁) + ZT.natLit 6 * p2 (c₂ * f₂) + ZT.natLit 12 * ((c₁ * f₁) * (c₂ * f₂)))
abbrev d32₁ : ZT n :=
  p2 c₁ * (ZT.natLit 4 * ((c₀ * f₀) * (c₁ * f₁)) + p2 (c₁ * f₁) + ZT.natLit 4 * ((c₁ * f₁) * (c₂ * f₂)) +
    ZT.natLit 12 * ((c₀ * f₀) * (c₂ * f₂)) + ZT.natLit 6 * p2 (c₂ * f₂))
abbrev d32₂ : ZT n :=
  p2 c₂ * (ZT.natLit 4 * ((c₀ * f₀) * (c₂ * f₂)) + ZT.natLit 4 * ((c₁ * f₁) * (c₂ * f₂)) + p2 (c₂ * f₂) +
    ZT.natLit 12 * ((c₀ * f₀) * (c₁ * f₁)))

theorem cover22_id : Γ ⊢[PRAAx] ZT.eq (d22₀ c₀ c₁ f₀ f₁ * p2 f₀ + d22₁ c₀ c₁ f₀ f₁ * p2 f₁)
    (p3 (c₀ * f₀ + c₁ * f₁)) := by
  ipra_ring

theorem cover23_id : Γ ⊢[PRAAx] ZT.eq (d23₀ c₀ c₁ f₀ f₁ * p3 f₀ + d23₁ c₀ c₁ f₀ f₁ * p3 f₁)
    (p5 (c₀ * f₀ + c₁ * f₁)) := by
  ipra_ring

theorem cover32_id : Γ ⊢[PRAAx] ZT.eq
    (d32₀ c₀ c₁ c₂ f₀ f₁ f₂ * p2 f₀ + d32₁ c₀ c₁ c₂ f₀ f₁ f₂ * p2 f₁ + d32₂ c₀ c₁ c₂ f₀ f₁ f₂ * p2 f₂)
    (p4 (c₀ * f₀ + c₁ * f₁ + c₂ * f₂)) := by
  ipra_ring

variable {c₀ c₁ c₂ f₀ f₁ f₂}

/-- `thm:power-cover` for two generators and squares. -/
theorem cover22 (h : Γ ⊢[PRAAx] ZT.eq (c₀ * f₀ + c₁ * f₁) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (d22₀ c₀ c₁ f₀ f₁ * p2 f₀ + d22₁ c₀ c₁ f₀ f₁ * p2 f₁) (ZT.natLit 1) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  linear_combination ((𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁)) ^ 2 + (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁)) + 1) * e

/-- `thm:power-cover` for two generators and cubes. -/
theorem cover23 (h : Γ ⊢[PRAAx] ZT.eq (c₀ * f₀ + c₁ * f₁) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (d23₀ c₀ c₁ f₀ f₁ * p3 f₀ + d23₁ c₀ c₁ f₀ f₁ * p3 f₁) (ZT.natLit 1) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  linear_combination ((𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁)) ^ 4 + (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁)) ^ 3 +
    (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁)) ^ 2 + (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁)) + 1) * e

/-- `thm:power-cover` for three generators and squares. -/
theorem cover32 (h : Γ ⊢[PRAAx] ZT.eq (c₀ * f₀ + c₁ * f₁ + c₂ * f₂) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      (d32₀ c₀ c₁ c₂ f₀ f₁ f₂ * p2 f₀ + d32₁ c₀ c₁ c₂ f₀ f₁ f₂ * p2 f₁ + d32₂ c₀ c₁ c₂ f₀ f₁ f₂ * p2 f₂)
      (ZT.natLit 1) := by
  have e := ZT.toZ_eq h
  apply ZT.derive
  ipra_simps
  linear_combination ((𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁) + 𝔷(c₂) * 𝔷(f₂)) ^ 3 +
    (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁) + 𝔷(c₂) * 𝔷(f₂)) ^ 2 +
    (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁) + 𝔷(c₂) * 𝔷(f₂)) + 1) * e

/-- The inductive step of `thm:power-cover` for two generators, for every exponent. With
`P = f₀^N`, `Q = f₁^N` and a certificate `d₀ f₀^(N+1) + d₁ f₁^(N+1) = 1`, the updated
coefficients

  `d₀' = d₀ c₀ + d₀² c₁ P f₁ + d₀ d₁ c₀ f₁ Q`,  `d₁' = d₁ c₁ + d₀ d₁ c₁ f₀ P + d₁² c₀ f₀ Q`

satisfy `d₀' f₀^(N+2) + d₁' f₁^(N+2) = 1`. Starting from `d = c`, `P = Q = 1`, iteration gives
the certificate for every power, by a primitive-recursive update. -/
theorem cover_step {d₀ d₁ P Q : ZT n} (hu : Γ ⊢[PRAAx] ZT.eq (c₀ * f₀ + c₁ * f₁) (ZT.natLit 1))
    (hS : Γ ⊢[PRAAx] ZT.eq (d₀ * (f₀ * P) + d₁ * (f₁ * Q)) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      ((d₀ * c₀ + d₀ * d₀ * c₁ * P * f₁ + d₀ * d₁ * c₀ * (f₁ * Q)) * (f₀ * (f₀ * P)) +
        (d₁ * c₁ + d₀ * d₁ * c₁ * (f₀ * P) + d₁ * d₁ * c₀ * f₀ * Q) * (f₁ * (f₁ * Q)))
      (ZT.natLit 1) := by
  have eu := ZT.toZ_eq hu; have eS := ZT.toZ_eq hS
  apply ZT.derive
  ipra_simps
  linear_combination (𝔷(c₀) * 𝔷(f₀) + 𝔷(c₁) * 𝔷(f₁) + 𝔷(d₀) * 𝔷(c₁) * 𝔷(f₁) * (𝔷(f₀) * 𝔷(P)) +
    𝔷(d₁) * 𝔷(c₀) * 𝔷(f₀) * (𝔷(f₁) * 𝔷(Q))) * eS + eu

end PowerCover

/-! ## Closed forms -/

section Closed

abbrev C₀ : ZT 12 := .var2 0 1
abbrev C₁ : ZT 12 := .var2 2 3
abbrev C₂ : ZT 12 := .var2 4 5
abbrev F₀ : ZT 12 := .var2 6 7
abbrev F₁ : ZT 12 := .var2 8 9
abbrev F₂ : ZT 12 := .var2 10 11

def cover22Formula : Fm PTm 12 :=
  ZT.eq (C₀ * F₀ + C₁ * F₁) (ZT.natLit 1) ⟶
    ZT.eq (d22₀ C₀ C₁ F₀ F₁ * p2 F₀ + d22₁ C₀ C₁ F₀ F₁ * p2 F₁) (ZT.natLit 1)

def cover23Formula : Fm PTm 12 :=
  ZT.eq (C₀ * F₀ + C₁ * F₁) (ZT.natLit 1) ⟶
    ZT.eq (d23₀ C₀ C₁ F₀ F₁ * p3 F₀ + d23₁ C₀ C₁ F₀ F₁ * p3 F₁) (ZT.natLit 1)

def cover32Formula : Fm PTm 12 :=
  ZT.eq (C₀ * F₀ + C₁ * F₁ + C₂ * F₂) (ZT.natLit 1) ⟶
    ZT.eq (d32₀ C₀ C₁ C₂ F₀ F₁ F₂ * p2 F₀ + d32₁ C₀ C₁ C₂ F₀ F₁ F₂ * p2 F₁ +
      d32₂ C₀ C₁ C₂ F₀ F₁ F₂ * p2 F₂) (ZT.natLit 1)

theorem cover22_all : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 cover22Formula :=
  closeAll 12 (.impI (cover22 Prf.hyp0))

theorem cover23_all : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 cover23Formula :=
  closeAll 12 (.impI (cover23 Prf.hyp0))

theorem cover32_all : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 12 cover32Formula :=
  closeAll 12 (.impI (cover32 Prf.hyp0))

/-- The packet's example: `f = (2, 3)`, `c = (−1, 1)`, `N = 2` gives `d = (7, −3)` and
`7 · 2² − 3 · 3² = 1`. -/
def exampleFormula : Fm PTm 0 :=
  (ZT.eq (d22₀ (-(ZT.natLit 1)) (ZT.natLit 1) (ZT.natLit 2) (ZT.natLit 3)) (ZT.natLit 7)) ⋏
    ((ZT.eq (d22₁ (-(ZT.natLit 1)) (ZT.natLit 1) (ZT.natLit 2) (ZT.natLit 3)) (-(ZT.natLit 3))) ⋏
      ZT.eq (ZT.natLit 7 * p2 (ZT.natLit 2) + -(ZT.natLit 3) * p2 (ZT.natLit 3)) (ZT.natLit 1))

theorem cover_example : ([] : List (Fm PTm 0)) ⊢[PRAAx] exampleFormula := by
  unfold exampleFormula
  exact .andI (by ipra_ring) (.andI (by ipra_ring) (by ipra_ring))

end Closed

end LeanProofs.IPRA.Geometry.LocalizationWitness
