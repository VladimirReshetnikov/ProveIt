import IPRADerivations.Algebra.QuinticPrincipal

/-!
# The four-resolvent product

Packet: `algebra/bring_quintic_ipra_2026-11-16`, Theorem `thm:four-resolvent`: for
`r_j = ω^j u_1 + ω^{2j} u_2 + ω^{3j} u_3 + ω^{4j} u_4` the five values are the roots of
`T⁵ − 5UT³ − 5VT² + 5WT + 5(X_0 − Y_0) − Z`, with `U, V, W, X_0, Y_0, Z` the displayed polynomials in the `u_i`.

* `four_resolvent`: for every `ω` with `ω⁵ = 1` (all five powers `ω^j` of a primitive fifth root, and `1`),
  `r = ω u_1 + ω² u_2 + ω³ u_3 + ω⁴ u_4` is a root. The polynomial `P(r(ω))` is divisible by `ω⁵ − 1` as a
  polynomial in `ω`; the quotient (107 monomials) was computed with `sympy` and is the certificate. This is the
  packet's "reduce every power of `ω`" calculation, done in the ring of differences of integer terms.
* `four_resolvent_special` (`cor:four-resolvent-specialization`): if `U = V = 0`, `5W = a`, `5(X_0 − Y_0) − Z = b`,
  every such `r` satisfies `r⁵ + ar + b = 0`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.FourResolvent

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

section
variable (u1 u2 u3 u4 : ZT n)
/-- `U = u_1u_4 + u_2u_3`. -/
abbrev UU : ZT n := u1 * u4 + u2 * u3
/-- `V`. -/
abbrev VV : ZT n := u1 * (u2 * u2) + u2 * (u4 * u4) + u3 * (u1 * u1) + u4 * (u3 * u3)
/-- `W`. -/
abbrev WW : ZT n := u1 * u1 * (u4 * u4) + u2 * u2 * (u3 * u3) - u1 * u1 * u1 * u2 - u2 * u2 * u2 * u4 -
  u3 * u3 * u3 * u1 - u4 * u4 * u4 * u3 - u1 * u2 * u3 * u4
/-- `X_0`. -/
abbrev XX : ZT n := u1 * u1 * u1 * u3 * u4 + u2 * u2 * u2 * u1 * u3 + u3 * u3 * u3 * u2 * u4 + u4 * u4 * u4 * u1 * u2
/-- `Y_0`. -/
abbrev YY : ZT n := u1 * (u3 * u3) * (u4 * u4) + u2 * (u1 * u1) * (u3 * u3) + u3 * (u2 * u2) * (u4 * u4) +
  u4 * (u1 * u1) * (u2 * u2)
/-- `Z`. -/
abbrev ZZ : ZT n := u1 * u1 * u1 * u1 * u1 + u2 * u2 * u2 * u2 * u2 + u3 * u3 * u3 * u3 * u3 + u4 * u4 * u4 * u4 * u4
end

/-- `r(ω) = ω u_1 + ω² u_2 + ω³ u_3 + ω⁴ u_4`. -/
abbrev rr (w u1 u2 u3 u4 : ZT n) : ZT n := w * u1 + w * w * u2 + w * w * w * u3 + w * w * w * w * u4

/-- `thm:four-resolvent`: `r(ω)` is a root of `T⁵ − 5UT³ − 5VT² + 5WT + 5(X_0 − Y_0) − Z` when `ω⁵ = 1`. -/
theorem four_resolvent {w u1 u2 u3 u4 : ZT n} (hw : Γ ⊢[PRAAx] ZT.eq (w * w * w * w * w) (ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq
      (rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 -
        ZT.natLit 5 * UU u1 u2 u3 u4 * (rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4) -
        ZT.natLit 5 * VV u1 u2 u3 u4 * (rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4) +
        ZT.natLit 5 * WW u1 u2 u3 u4 * rr w u1 u2 u3 u4 +
        ZT.natLit 5 * (XX u1 u2 u3 u4 - YY u1 u2 u3 u4) - ZZ u1 u2 u3 u4) (ZT.natLit 0) := by
  have e := ZT.toZ_eq hw
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at e ⊢
  push_cast at e ⊢
  generalize ZT.toZ Γ w = ω at e ⊢
  generalize ZT.toZ Γ u1 = A at e ⊢
  generalize ZT.toZ Γ u2 = B at e ⊢
  generalize ZT.toZ Γ u3 = C at e ⊢
  generalize ZT.toZ Γ u4 = D at e ⊢
  linear_combination (A^5 + 5*A^4*B*ω + 5*A^4*C*ω^2 + 5*A^4*D*ω^3 + 10*A^3*B^2*ω^2 + 20*A^3*B*C*ω^3 + 20*A^3*B*D*ω^4 + 10*A^3*C^2*ω^4 + 20*A^3*C*D*ω^5 - 5*A^3*C*D + 10*A^3*D^2*ω^6 - 5*A^3*D^2*ω + 10*A^2*B^3*ω^3 + 30*A^2*B^2*C*ω^4 + 30*A^2*B^2*D*ω^5 + 5*A^2*B^2*D + 30*A^2*B*C^2*ω^5 + 5*A^2*B*C^2 + 60*A^2*B*C*D*ω^6 + 5*A^2*B*C*D*ω + 30*A^2*B*D^2*ω^7 + 10*A^2*C^3*ω^6 + 5*A^2*C^3*ω + 30*A^2*C^2*D*ω^7 + 5*A^2*C^2*D*ω^2 + 30*A^2*C*D^2*ω^8 - 5*A^2*C*D^2*ω^3 + 10*A^2*D^3*ω^9 - 5*A^2*D^3*ω^4 + 5*A*B^4*ω^4 + 20*A*B^3*C*ω^5 - 5*A*B^3*C + 20*A*B^3*D*ω^6 + 5*A*B^3*D*ω + 30*A*B^2*C^2*ω^6 - 5*A*B^2*C^2*ω + 60*A*B^2*C*D*ω^7 + 5*A*B^2*C*D*ω^2 + 30*A*B^2*D^2*ω^8 + 10*A*B^2*D^2*ω^3 + 20*A*B*C^3*ω^7 + 5*A*B*C^3*ω^2 + 60*A*B*C^2*D*ω^8 + 15*A*B*C^2*D*ω^3 + 60*A*B*C*D^2*ω^9 + 15*A*B*C*D^2*ω^4 + 20*A*B*D^3*ω^10 + 5*A*B*D^3*ω^5 - 5*A*B*D^3 + 5*A*C^4*ω^8 + 5*A*C^4*ω^3 + 20*A*C^3*D*ω^9 + 15*A*C^3*D*ω^4 + 30*A*C^2*D^2*ω^10 + 15*A*C^2*D^2*ω^5 + 5*A*C^2*D^2 + 20*A*C*D^3*ω^11 + 5*A*C*D^3*ω^6 + 5*A*C*D^3*ω + 5*A*D^4*ω^12 + B^5*ω^5 + B^5 + 5*B^4*C*ω^6 + 5*B^4*D*ω^7 + 5*B^4*D*ω^2 + 10*B^3*C^2*ω^7 - 5*B^3*C^2*ω^2 + 20*B^3*C*D*ω^8 + 5*B^3*C*D*ω^3 + 10*B^3*D^2*ω^9 + 10*B^3*D^2*ω^4 + 10*B^2*C^3*ω^8 - 5*B^2*C^3*ω^3 + 30*B^2*C^2*D*ω^9 + 30*B^2*C*D^2*ω^10 + 15*B^2*C*D^2*ω^5 + 5*B^2*C*D^2 + 10*B^2*D^3*ω^11 + 10*B^2*D^3*ω^6 + 5*B*C^4*ω^9 + 20*B*C^3*D*ω^10 + 5*B*C^3*D*ω^5 - 5*B*C^3*D + 30*B*C^2*D^2*ω^11 + 15*B*C^2*D^2*ω^6 + 20*B*C*D^3*ω^12 + 15*B*C*D^3*ω^7 + 5*B*C*D^3*ω^2 + 5*B*D^4*ω^13 + 5*B*D^4*ω^8 + C^5*ω^10 + C^5*ω^5 + C^5 + 5*C^4*D*ω^11 + 5*C^4*D*ω^6 + 10*C^3*D^2*ω^12 + 10*C^3*D^2*ω^7 + 10*C^2*D^3*ω^13 + 10*C^2*D^3*ω^8 + 5*C^2*D^3*ω^3 + 5*C*D^4*ω^14 + 5*C*D^4*ω^9 + 5*C*D^4*ω^4 + D^5*ω^15 + D^5*ω^10 + D^5*ω^5 + D^5) * e

/-- `cor:four-resolvent-specialization`: with `U = V = 0`, `5W = a`, `5(X_0 − Y_0) − Z = b`, `r⁵ + ar + b = 0`. -/
theorem four_resolvent_special {w u1 u2 u3 u4 a b : ZT n}
    (hw : Γ ⊢[PRAAx] ZT.eq (w * w * w * w * w) (ZT.natLit 1))
    (hU : Γ ⊢[PRAAx] ZT.eq (UU u1 u2 u3 u4) (ZT.natLit 0)) (hV : Γ ⊢[PRAAx] ZT.eq (VV u1 u2 u3 u4) (ZT.natLit 0))
    (hW : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 5 * WW u1 u2 u3 u4) a)
    (hb : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 5 * (XX u1 u2 u3 u4 - YY u1 u2 u3 u4) - ZZ u1 u2 u3 u4) b) :
    Γ ⊢[PRAAx] ZT.eq (rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 * rr w u1 u2 u3 u4 *
      rr w u1 u2 u3 u4 + a * rr w u1 u2 u3 u4 + b) (ZT.natLit 0) := by
  have e := ZT.toZ_eq (four_resolvent (u1 := u1) (u2 := u2) (u3 := u3) (u4 := u4) hw)
  have eU := ZT.toZ_eq hU
  have eV := ZT.toZ_eq hV
  have eW := ZT.toZ_eq hW
  have eb := ZT.toZ_eq hb
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit] at e eU eV eW eb ⊢
  push_cast at e eU eV eW eb ⊢
  linear_combination e + 5 * (ZT.toZ Γ w * ZT.toZ Γ u1 + ZT.toZ Γ w ^ 2 * ZT.toZ Γ u2 + ZT.toZ Γ w ^ 3 * ZT.toZ Γ u3 + ZT.toZ Γ w ^ 4 * ZT.toZ Γ u4) ^ 3 * eU + 5 * (ZT.toZ Γ w * ZT.toZ Γ u1 + ZT.toZ Γ w ^ 2 * ZT.toZ Γ u2 + ZT.toZ Γ w ^ 3 * ZT.toZ Γ u3 + ZT.toZ Γ w ^ 4 * ZT.toZ Γ u4) ^ 2 * eV -
    (ZT.toZ Γ w * ZT.toZ Γ u1 + ZT.toZ Γ w ^ 2 * ZT.toZ Γ u2 + ZT.toZ Γ w ^ 3 * ZT.toZ Γ u3 +
      ZT.toZ Γ w ^ 4 * ZT.toZ Γ u4) * eW - eb

end LeanProofs.IPRA.Algebra.FourResolvent
