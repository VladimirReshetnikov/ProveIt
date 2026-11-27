import IPRADerivations.DiophantineNumberTheory.FourSquaresDescent

/-!
# The two-square descent

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/quadratic.tex`, Lemma
`qr:two-descent`: for a prime `p` and `1 < m < p`, from `x² + y² = m p` one computes `u`, `v` and
`1 ≤ m' < m` with `u² + v² = m' p`.

It is the four-square descent `FourSquaresDescent.descent` at the tuple `(x, y, 0, 0)`: the signed residues of
the two zero coordinates are zero, so the third and the fourth coordinates of the new tuple vanish (each is an
absolute difference of two expressions that are zero), and the first two give the new representation.

* `av_zero`, `sgn_zero`, `uv_zero`: the residue data of the coordinate `0`;
* `ad_zero`: `|P − Q| = 0` when `P = Q = 0`;
* `z3a`, `z3b`, `z4a`, `z4b`: the four expressions of `w₃`, `w₄` vanish;
* **`two_descent`**: `u² + v² = m' p` and `1 ≤ m' < m`, with `u = w₁`, `v = w₂`, `m' = mq` of the four-square
  step at `(x, y, 0, 0)`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresDescent

open_ipra exports
open LeanProofs.IPRA.Combinatorics.LegendreDigits (quo_small)
open LeanProofs.IPRA.DiophantineNumberTheory.ThueGrid (ad)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresAlgebra (N4 ad_sq w1 w2 w3 w4)
open LeanProofs.IPRA.DiophantineNumberTheory.FourSquaresDescent (sgn av uv res_low Af sf Uf mq descent)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The residue data of a zero coordinate -/

theorem zero_res {m : PTm k} :
    Γ ⊢[PRAAx] (sgn (zero : PTm k) m ≐ zero) ⋏ (av (zero : PTm k) m ≐ rem zero m) :=
  res_low (le_congr (rem_zero m).eqSymm (.eqRefl _) (zero_le _))

theorem sgn_zero (m : PTm k) : Γ ⊢[PRAAx] sgn (zero : PTm k) m ≐ zero := Prf.andE₁ zero_res

theorem av_zero (m : PTm k) : Γ ⊢[PRAAx] av (zero : PTm k) m ≐ zero :=
  (Prf.andE₂ zero_res).eqTrans (rem_zero m)

theorem uv_zero {m : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) : Γ ⊢[PRAAx] uv (zero : PTm k) m ≐ zero :=
  (congrAdd (quo_small hm (zero_lt' hm)) (sgn_zero m)).eqTrans (zero_add zero)

/-! ## Vanishing absolute differences -/

theorem sq_of_zero {W P Q : PTm k} (e : Γ ⊢[PRAAx] W * W + two * (P * Q) ≐ P * P + Q * Q)
    (hP : Γ ⊢[PRAAx] P ≐ zero) (hQ : Γ ⊢[PRAAx] Q ≐ zero) : Γ ⊢[PRAAx] W * W + zero ≐ zero := by
  ipra_lc natEq e + (𝔞 P - 2 * 𝔞 Q) * natEq hP + 𝔞 Q * natEq hQ

theorem sq_zero_alg {a p X : PTm k} (ha : Γ ⊢[PRAAx] a ≐ succ p) (h : Γ ⊢[PRAAx] a * a + X ≐ zero) :
    Γ ⊢[PRAAx] Fm.bot := by
  have product := (congrMul ha (.eqRefl a)).eqSymm.eqTrans (add_eq_zero_left h)
  exact succ_ne_zero (ha.eqSymm.eqTrans (eq_zero_of_succ_mul product))

/-- `|P − Q| = 0` when `P = Q = 0`. -/
theorem ad_zero {P Q : PTm k} (hP : Γ ⊢[PRAAx] P ≐ zero) (hQ : Γ ⊢[PRAAx] Q ≐ zero) :
    Γ ⊢[PRAAx] ad P Q ≐ zero :=
  .orE (zero_or_zero_of_mul (add_eq_zero_left (sq_of_zero (ad_sq P Q) hP hQ))) Prf.hyp0 Prf.hyp0

section Zeros

variable {a0 a1 a2 a3 u0 u1 u2 u3 s0 s1 s2 s3 : PTm k}
  (hu2 : Γ ⊢[PRAAx] u2 ≐ zero) (hu3 : Γ ⊢[PRAAx] u3 ≐ zero)
  (ha2 : Γ ⊢[PRAAx] a2 ≐ zero) (ha3 : Γ ⊢[PRAAx] a3 ≐ zero)
include hu2 hu3 ha2 ha3

theorem z3a : Γ ⊢[PRAAx] a0 * u2 + two * (a1 * u3 * s1) + (two * (a2 * u0 * s2) + a3 * u1) ≐ zero := by
  ipra_lc 𝔞 a0 * natEq hu2 + 2 * 𝔞 a1 * 𝔞 s1 * natEq hu3 + 2 * 𝔞 u0 * 𝔞 s2 * natEq ha2 + 𝔞 u1 * natEq ha3

theorem z3b : Γ ⊢[PRAAx] two * (a0 * u2 * s0) + a1 * u3 + (a2 * u0 + two * (a3 * u1 * s3)) ≐ zero := by
  ipra_lc 2 * 𝔞 a0 * 𝔞 s0 * natEq hu2 + 𝔞 a1 * natEq hu3 + 𝔞 u0 * natEq ha2 + 2 * 𝔞 u1 * 𝔞 s3 * natEq ha3

theorem z4a : Γ ⊢[PRAAx] a0 * u3 + a1 * u2 + (two * (a2 * u1 * s2) + two * (a3 * u0 * s3)) ≐ zero := by
  ipra_lc 𝔞 a0 * natEq hu3 + 𝔞 a1 * natEq hu2 + 2 * 𝔞 u1 * 𝔞 s2 * natEq ha2 + 2 * 𝔞 u0 * 𝔞 s3 * natEq ha3

theorem z4b : Γ ⊢[PRAAx] two * (a0 * u3 * s0) + two * (a1 * u2 * s1) + (a2 * u1 + a3 * u0) ≐ zero := by
  ipra_lc 2 * 𝔞 a0 * 𝔞 s0 * natEq hu3 + 2 * 𝔞 a1 * 𝔞 s1 * natEq hu2 + 𝔞 u1 * natEq ha2 + 𝔞 u0 * natEq ha3

end Zeros

/-! ## The descent -/

theorem n1_alg {x y M : PTm k} (h : Γ ⊢[PRAAx] x * x + y * y ≐ M) :
    Γ ⊢[PRAAx] N4 x y zero zero ≐ M := by
  ipra_lc natEq h

theorem two_alg {W1 W2 W3 W4 M : PTm k} (h : Γ ⊢[PRAAx] N4 W1 W2 W3 W4 ≐ M) (h3 : Γ ⊢[PRAAx] W3 ≐ zero)
    (h4 : Γ ⊢[PRAAx] W4 ≐ zero) : Γ ⊢[PRAAx] W1 * W1 + W2 * W2 ≐ M := by
  ipra_lc natEq h - 𝔞 W3 * natEq h3 - 𝔞 W4 * natEq h4

/-- The tuple `(x, y, 0, 0)`. -/
abbrev xs (x y : PTm k) : Fin 4 → PTm k := ![x, y, zero, zero]

/-- **`qr:two-descent`**: for a prime `p`, `2 ≤ m < p` and `x² + y² = m p`, the explicit `u`, `v`, `m'`
satisfy `u² + v² = m' p` and `1 ≤ m' < m`. -/
theorem two_descent {p m x y : PTm k} (hp : Γ ⊢[PRAAx] prime p) (hm2 : Γ ⊢[PRAAx] le two m)
    (hmp : Γ ⊢[PRAAx] lt m p) (h : Γ ⊢[PRAAx] x * x + y * y ≐ m * p) :
    Γ ⊢[PRAAx]
      (w1 (Af (xs x y) m) (sf (xs x y) m) (Uf (xs x y) m) (mq (xs x y) m) *
          w1 (Af (xs x y) m) (sf (xs x y) m) (Uf (xs x y) m) (mq (xs x y) m) +
        w2 (Af (xs x y) m) (sf (xs x y) m) (Uf (xs x y) m) *
          w2 (Af (xs x y) m) (sf (xs x y) m) (Uf (xs x y) m) ≐ mq (xs x y) m * p) ⋏
      (le one (mq (xs x y) m) ⋏ lt (mq (xs x y) m) m) := by
  have hm := p_pos hm2
  have n1 : Γ ⊢[PRAAx] N4 (xs x y 0) (xs x y 1) (xs x y 2) (xs x y 3) ≐ m * p := n1_alg h
  have d := descent (x := xs x y) hp hm2 hmp n1
  have hu2 : Γ ⊢[PRAAx] Uf (xs x y) m 2 ≐ zero := uv_zero hm
  have hu3 : Γ ⊢[PRAAx] Uf (xs x y) m 3 ≐ zero := uv_zero hm
  have ha2 : Γ ⊢[PRAAx] Af (xs x y) m 2 ≐ zero := av_zero m
  have ha3 : Γ ⊢[PRAAx] Af (xs x y) m 3 ≐ zero := av_zero m
  have h3 : Γ ⊢[PRAAx] w3 (Af (xs x y) m) (sf (xs x y) m) (Uf (xs x y) m) ≐ zero :=
    ad_zero (z3a hu2 hu3 ha2 ha3) (z3b hu2 hu3 ha2 ha3)
  have h4 : Γ ⊢[PRAAx] w4 (Af (xs x y) m) (sf (xs x y) m) (Uf (xs x y) m) ≐ zero :=
    ad_zero (z4a hu2 hu3 ha2 ha3) (z4b hu2 hu3 ha2 ha3)
  exact .andI (two_alg (Prf.andE₁ d) h3 h4) (Prf.andE₂ d)

end LeanProofs.IPRA.DiophantineNumberTheory.TwoSquaresDescent
