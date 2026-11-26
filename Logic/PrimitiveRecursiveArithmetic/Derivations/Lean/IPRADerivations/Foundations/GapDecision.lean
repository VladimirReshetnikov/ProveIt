import IPRADerivations.Core.IntOrder
import IPRADerivations.Probability.MedianWeighted
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Exactness from a gap

Packet: `foundations/ipra_kernel_finite_use_framework_2026-11-15`, Theorem `thm:gap` (Gap decision):
if `z = 0 ∨ |z| ≥ δ` and `|q − z| < δ/3`, then the decidable test `|q| < δ/2` tells the two
branches apart.

The statement is homogeneous in `z, q, δ`, so after multiplying by a common denominator the
rationals become integers: `z, q` are integer terms (`ZT`) and `δ` is a natural-number term. The
absolute value of an integer term is the natural-number term `|u| = ad u⁺ u⁻`. The hypothesis
`|q − z| < δ/3` reads `3 |q − z| < δ`, and the test `|q| < δ/2` reads `2 |q| < δ`.

* `zabs_congr`, `zabs_tri`: `|·|` depends only on the integer value and satisfies the triangle
  inequality (`ad_add_le`);
* `gap_zero`: `z = 0` gives `2 |q| < δ` (the packet's `|q| < δ/3 < δ/2`);
* `gap_far`: `|z| ≥ δ` gives `δ < 2 |q|` (the reverse triangle inequality,
  `|q| ≥ |z| − |q − z| > 2δ/3 > δ/2`);
* `gap_decide`: under the disjunction, `z = 0` holds exactly when `2 |q| < δ`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.GapDecision

open_ipra
open LeanProofs.IPRA.Probability.Variance (ad ad_sq)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_add_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `|u|` for an integer term, as a natural-number term. -/
abbrev zabs (u : ZT n) : PTm n := ad u.pos u.neg

ipra_subst zabs [ad, ZT.subst]

theorem zabs_sq (u : ZT n) : Groth.ι (Q.mk Γ (zabs u * zabs u)) = ZT.toZ Γ u * ZT.toZ Γ u := by
  rw [← sq_nat, ZT.toZ_sq, pow_two]

/-- `|u|` depends only on the value of `u`. -/
theorem zabs_congr {u v : ZT n} (h : ZT.toZ Γ u = ZT.toZ Γ v) : Γ ⊢[PRAAx] zabs u ≐ zabs v := by
  have e : Γ ⊢[PRAAx] zabs u * zabs u ≐ zabs v * zabs v := by
    have a := zabs_sq (Γ := Γ) u; have b := zabs_sq (Γ := Γ) v
    apply deriveNat
    rw [a, b, h]
  exact le_antisymm (nat_sqrt_mono (le_congr (.eqRefl _) e (le_refl _)))
    (nat_sqrt_mono (le_congr (.eqRefl _) e.eqSymm (le_refl _)))

/-- The triangle inequality: `w = u + v` gives `|w| ≤ |u| + |v|`. -/
theorem zabs_tri {u v w : ZT n} (h : ZT.toZ Γ w = ZT.toZ Γ u + ZT.toZ Γ v) :
    Γ ⊢[PRAAx] le (zabs w) (zabs u + zabs v) :=
  le_congr (zabs_congr (u := u + v) (by rw [ZT.toZ_add, h])) (.eqRefl _) (ad_add_le u.pos v.pos u.neg v.neg)

/-- `|−u| = |u|`. -/
theorem zabs_neg (u : ZT n) : Γ ⊢[PRAAx] zabs (-u) ≐ zabs u := add_comm _ _

variable {z q : ZT n} {δ : PTm n}

/-- The branch `z = 0`: `3 |q − z| < δ` gives `2 |q| < δ`. -/
theorem gap_zero (hz : Γ ⊢[PRAAx] ZT.eq z (ZT.natLit 0)) (hq : Γ ⊢[PRAAx] lt (num 3 * zabs (q - z)) δ) :
    Γ ⊢[PRAAx] lt (two * zabs q) δ := by
  have z0 := ZT.toZ_eq hz
  refine le_trans (le_of_eq_add (d := zabs (q - z)) ?_) hq
  ipra_lc -2 * natEq (zabs_congr (Γ := Γ) (u := q) (v := q - z) (by rw [ZT.toZ_sub, z0]; simp))

/-- The branch `|z| ≥ δ`: `3 |q − z| < δ` gives `δ < 2 |q|`. -/
theorem gap_far (hz : Γ ⊢[PRAAx] le δ (zabs z)) (hq : Γ ⊢[PRAAx] lt (num 3 * zabs (q - z)) δ) :
    Γ ⊢[PRAAx] lt δ (two * zabs q) := by
  have t : Γ ⊢[PRAAx] le (zabs z) (zabs q + zabs (-(q - z))) :=
    zabs_tri (by simp only [ZT.toZ_neg, ZT.toZ_sub]; ring)
  refine .orE (lt_or_le δ (two * zabs q)) Prf.hyp0 ?_
  refine succ_ne_zero' _ (a := δ + num 6 * monus (zabs z) δ +
    num 6 * monus (zabs q + zabs (-(q - z))) (zabs z) + num 3 * monus δ (two * zabs q) +
    two * monus δ (succ (num 3 * zabs (q - z))) + one) ?_
  ipra_lc -6 * natEq (eq_add_of_le (hz.wk (ψ := le (two * zabs q) δ))) -
    6 * natEq (eq_add_of_le (t.wk (ψ := le (two * zabs q) δ))) +
    6 * natEq ((zabs_neg (Γ := le (two * zabs q) δ :: Γ) (q - z))) -
    3 * natEq (eq_add_of_le (Prf.hyp0 : (le (two * zabs q) δ :: Γ) ⊢[PRAAx] _)) -
    2 * natEq (eq_add_of_le (hq.wk (ψ := le (two * zabs q) δ)))

/-- `thm:gap`: under `z = 0 ∨ |z| ≥ δ` and `3 |q − z| < δ`, `z = 0` holds exactly when `2 |q| < δ`. -/
theorem gap_decide (hz : Γ ⊢[PRAAx] ZT.eq z (ZT.natLit 0) ⋎ le δ (zabs z))
    (hq : Γ ⊢[PRAAx] lt (num 3 * zabs (q - z)) δ) :
    Γ ⊢[PRAAx] (ZT.eq z (ZT.natLit 0) ⟶ lt (two * zabs q) δ) ⋏ (lt (two * zabs q) δ ⟶ ZT.eq z (ZT.natLit 0)) := by
  refine .andI (.impI (gap_zero Prf.hyp0 hq.wk)) (.impI ?_)
  refine .orE hz.wk Prf.hyp0 ?_
  have f := gap_far (Prf.hyp0 : (le δ (zabs z) :: lt (two * zabs q) δ :: Γ) ⊢[PRAAx] _) hq.wk.wk
  have g : (le δ (zabs z) :: lt (two * zabs q) δ :: Γ) ⊢[PRAAx] lt (two * zabs q) δ := Prf.hyp0.wk
  refine not_succ_le_self δ _ (le_trans f (le_trans (le_of_eq_add (d := one) ?_) g))
  ipra_ring

end LeanProofs.IPRA.Foundations.GapDecision
