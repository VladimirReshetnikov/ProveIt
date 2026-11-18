import IPRADerivations.Core.PolynomialImplications

/-!
# Common zeros give norm zeros (`ipra_presentations_to_witnesses`, `lem:norm-intersection-vanishing`)

Packet: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-intersection-vanishing`:
"Put `v = (1, b, …, b^{m-1})`. Evaluating each monic reduction identity at `(a, b)` gives
`v M_G(a) = G(a, b) v = 0`. The adjugate identity, proved by finite determinant expansion,
yields `v M_G(a) adj(M_G(a)) = N_G(a) v`. Its first coordinate is `N_G(a)`, because `v_0 = 1`. It
therefore vanishes."

The linear-algebra step, over the integers, for `m = 2` and `m = 3` and an arbitrary row vector
`v` (the packet's `v` has first coordinate `1`): if `v M = 0` then `v_1 det M = 0`.

* `norm_vanish_2`: `v_1 (M_11 M_22 - M_12 M_21) = 0` from the two coordinates of `v M = 0`;
* `norm_vanish_3`: `v_1 det M = 0` from the three coordinates of `v M = 0`.

Each is one polynomial certificate: the combination of the coordinates of `v M` with the
cofactors of the first row of `M` (the first column of the adjugate), the other two rows
contributing zero by the expansion along alien cofactors.

Not derived: the statement for a variable `m` (it needs the determinant as a sum over
permutations), the construction of the matrices `M_G(a)` from the reduction identities, and the
enumeration theorem `thm:norm-complete-intersection`.
-/

namespace LeanProofs.IPRA.Foundations.NormVanishing

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ZExp

/-! ## `m = 2` -/

section Two

local notation "v1" => (ZExp.var 0 : ZExp 6)
local notation "v2" => (ZExp.var 1 : ZExp 6)
local notation "m11" => (ZExp.var 2 : ZExp 6)
local notation "m12" => (ZExp.var 3 : ZExp 6)
local notation "m21" => (ZExp.var 4 : ZExp 6)
local notation "m22" => (ZExp.var 5 : ZExp 6)

/-- `v M = 0` for a `2 × 2` matrix. -/
abbrev null2 : List (ZExp 6 × ZExp 6) :=
  [(v1 * m11 + v2 * m21, 0), (v1 * m12 + v2 * m22, 0)]

/-- A left null vector annihilates the determinant: `v_1 det M = 0`. -/
theorem norm_vanish_2 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 6)
      (imp null2 (v1 * (m11 * m22 - m12 * m21), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂⟩ := h
    linear_combination ρ 5 * h₁ - ρ 4 * h₂)

end Two

/-! ## `m = 3` -/

section Three

local notation "v1" => (ZExp.var 0 : ZExp 12)
local notation "v2" => (ZExp.var 1 : ZExp 12)
local notation "v3" => (ZExp.var 2 : ZExp 12)
local notation "m11" => (ZExp.var 3 : ZExp 12)
local notation "m12" => (ZExp.var 4 : ZExp 12)
local notation "m13" => (ZExp.var 5 : ZExp 12)
local notation "m21" => (ZExp.var 6 : ZExp 12)
local notation "m22" => (ZExp.var 7 : ZExp 12)
local notation "m23" => (ZExp.var 8 : ZExp 12)
local notation "m31" => (ZExp.var 9 : ZExp 12)
local notation "m32" => (ZExp.var 10 : ZExp 12)
local notation "m33" => (ZExp.var 11 : ZExp 12)

/-- `v M = 0` for a `3 × 3` matrix. -/
abbrev null3 : List (ZExp 12 × ZExp 12) :=
  [(v1 * m11 + v2 * m21 + v3 * m31, 0), (v1 * m12 + v2 * m22 + v3 * m32, 0),
    (v1 * m13 + v2 * m23 + v3 * m33, 0)]

/-- A left null vector annihilates the determinant: `v_1 det M = 0`. -/
theorem norm_vanish_3 :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ (2 * 12)
      (imp null3
        (v1 * (m11 * (m22 * m33 - m23 * m32) - m12 * (m21 * m33 - m23 * m31) +
          m13 * (m21 * m32 - m22 * m31)), 0)) :=
  derive_imp _ _ (by
    ipra_poly R ρ h
    obtain ⟨h₁, h₂, h₃⟩ := h
    linear_combination (ρ 7 * ρ 11 - ρ 8 * ρ 10) * h₁ - (ρ 6 * ρ 11 - ρ 8 * ρ 9) * h₂ +
      (ρ 6 * ρ 10 - ρ 7 * ρ 9) * h₃)

end Three

end LeanProofs.IPRA.Foundations.NormVanishing
