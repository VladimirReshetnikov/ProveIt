import IPRADerivations.Analysis.PolynomialTaylor
import IPRADerivations.Core.IntCertificates

/-!
# The second-order Taylor estimate for polynomials with signed coefficients

Packets: `analysis/calculus_ipra` (the polynomial derivative certificates behind `eq:Pfinitebounds`:
`|ΔP_j − h P_{j−1}(t)| ≤ D₂ h²` "follows from `eq:monomialremainder`" for polynomials with rational coefficients of
both signs) and `analysis/ipra_certified_continuation_2026-11-19` (signed coefficient arrays).

`PolynomialTaylor` bounds `P(a + h) − P(a) − h P′(a)` for natural coefficients. A polynomial with integer
coefficients is the difference `P = P⁺ − P⁻` of two with natural coefficients `c⁺, c⁻` (bodies over `(j, x)`).
With `P^±(Z) = Σ_{j<D} c^±_j Z^j`, `P^±′(a) = Σ c^±_j j a^{j−1}` and the majorants
`Q^±(R) = Σ c^±_j (j − 1) j R^{j−1}`, as integer terms (`ZT`):

* `signed_taylor_upper`: `2R (P(a + h) − P(a) − h P′(a)) ≤ h² Q⁺(R)`;
* `signed_taylor_lower`: `−h² Q⁻(R) ≤ 2R (P(a + h) − P(a) − h P′(a))`;

for `a + h ≤ R`. Hence `|ΔP − h P′| ≤ h² max(Q⁺, Q⁻)/(2R)`, the signed remainder estimate with explicit constants.
Each bound is an integer certificate (`zle_of_comb`) from the natural Taylor slacks of the two parts.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.SignedTaylor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialLipschitz (polyB lipB)
open LeanProofs.IPRA.Analysis.PolynomialTaylor (d2B LowInv UpInv taylor_lower taylor_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Signed

variable (cp cn : PTm 2)

/-- `P^±(Z) = Σ_{j<D} c^±_j Z^j`. -/
abbrev Pv (c : PTm 2) (D Z x : PTm n) : PTm n := ap2 (sumF (polyB c)) D (pairT Z x)
/-- `P^±′(a) = Σ_{j<D} c^±_j j a^{j−1}`. -/
abbrev Lv (c : PTm 2) (D a x : PTm n) : PTm n := ap2 (sumF (lipB c)) D (pairT a x)
/-- `Q^±(R) = Σ_{j<D} c^±_j (j − 1) j R^{j−1}`. -/
abbrev Qv (c : PTm 2) (D R x : PTm n) : PTm n := ap2 (sumF (d2B c)) D (pairT R x)

/-- The signed residual `2R (P(a + h) − P(a) − h P′(a))` with `P = P⁺ − P⁻`. -/
def resZ (D a h R x : PTm n) : ZT n :=
  ZT.ofNat (two * R) *
    ((ZT.ofNat (Pv cp D (a + h) x) - ZT.ofNat (Pv cn D (a + h) x)) -
      (ZT.ofNat (Pv cp D a x) - ZT.ofNat (Pv cn D a x)) -
      ZT.ofNat h * (ZT.ofNat (Lv cp D a x) - ZT.ofNat (Lv cn D a x)))

/-- `2R (P(a + h) − P(a) − h P′(a)) ≤ h² Q⁺(R)`. -/
theorem signed_taylor_upper {a h R x : PTm n} (hR : Γ ⊢[PRAAx] le (a + h) R) (D : PTm n) :
    Γ ⊢[PRAAx] zle (resZ cp cn D a h R x) (ZT.ofNat (h * h * Qv cp D R x)) := by
  have up := taylor_upper (Γ := Γ) (c := cp) (x := x) hR D
  have lo := taylor_lower (Γ := Γ) (c := cn) a h x D
  refine zle_of_comb (sl up + Groth.ι (Q.mk Γ (two * R)) * sl lo) ?_ (nn_add (nn_sl _) (nn_mul (nn_term _) (nn_sl _)))
  simp only [resZ, sl_def, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]
  ring

/-- `−h² Q⁻(R) ≤ 2R (P(a + h) − P(a) − h P′(a))`. -/
theorem signed_taylor_lower {a h R x : PTm n} (hR : Γ ⊢[PRAAx] le (a + h) R) (D : PTm n) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (h * h * Qv cn D R x)) (resZ cp cn D a h R x) := by
  have up := taylor_upper (Γ := Γ) (c := cn) (x := x) hR D
  have lo := taylor_lower (Γ := Γ) (c := cp) a h x D
  refine zle_of_comb (sl up + Groth.ι (Q.mk Γ (two * R)) * sl lo) ?_ (nn_add (nn_sl _) (nn_mul (nn_term _) (nn_sl _)))
  simp only [resZ, sl_def, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]
  ring

end Signed

end LeanProofs.IPRA.Analysis.SignedTaylor
