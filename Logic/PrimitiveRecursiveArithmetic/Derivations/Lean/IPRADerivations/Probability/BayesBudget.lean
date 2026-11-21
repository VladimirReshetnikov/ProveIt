import IPRADerivations.Core.IntOrder
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.OrderCertificates

/-!
# The numerical stability budget of Bayes updating

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/conditioning.tex`, "Bayes updating with a
certified evidence bound", (`eq:bayes-budget`): "Suppose `|h| ≤ M`, the numerator `a = E(hℓ)` is approximated
by `a'` to error `δ_a`, and `Z` by `Z'` to error `δ_Z ≤ z_0/2`. Since `|a| ≤ MZ` and `Z' ≥ z_0/2`,
`|a'/Z' − a/Z| ≤ 2(δ_a + Mδ_Z)/z_0`. This follows by adding and subtracting `a/Z'` and bounding the two terms."

With signed numerators `a, a'` (integer terms) and natural `Z, Z', δ_a, δ_Z, M, z_0`, under `|a' − a| ≤ δ_a`,
`|a| ≤ MZ`, `|Z − Z'| ≤ δ_Z`, `z_0 ≤ Z` and `2δ_Z ≤ z_0`, cleared of the denominators `Z Z' z_0`:

* `bayes_budget`: both signs of `z_0 (a' Z − a Z')` are at most `2(δ_a + Mδ_Z) Z Z'`.

The certificate is integral after doubling: `2 · slack = 2Z(δ_a + Mδ_Z)(2p + 2t + t') + 2z_0 Z s + z_0(uq + vp)`,
with `p, q` the two slacks of `|Z − Z'| ≤ δ_Z`, `u, v` those of `|a| ≤ MZ`, `s` that of `|a' − a| ≤ δ_a`,
`t = Z − z_0`, `t' = z_0 − 2δ_Z`; `zle_of_toZ2` cancels the factor `2`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.BayesBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The natural slack of `zle u v`. -/
abbrev zsl (u v : ZT n) : PTm n := monus (v.pos + u.neg) (u.pos + v.neg)

/-- A doubled certificate: `2u + D = 2v` gives `u ≤ v`. -/
theorem zle_of_toZ2 {u v : ZT n} (D : PTm n)
    (h : 2 * ZT.toZ Γ u + Groth.ι (Q.mk Γ D) = 2 * ZT.toZ Γ v) : Γ ⊢[PRAAx] zle u v := by
  refine mul_le_cancel (d' := one) (le_of_eq_add (d := D) ?_)
  rw [toZ_def, toZ_def] at h
  apply deriveNat; ipra_simps
  linear_combination -h

/-- `eq:bayes-budget`, cleared: `|z_0 (a' Z − a Z')| ≤ 2(δ_a + Mδ_Z) Z Z'`. -/
theorem bayes_budget {a a' : ZT n} {Z Z' da dZ M z0 : PTm n}
    (hA1 : Γ ⊢[PRAAx] zle (a' - a) (ZT.ofNat da)) (hA2 : Γ ⊢[PRAAx] zle (a - a') (ZT.ofNat da))
    (hM1 : Γ ⊢[PRAAx] zle a (ZT.ofNat (M * Z))) (hM2 : Γ ⊢[PRAAx] zle (-a) (ZT.ofNat (M * Z)))
    (hZ1 : Γ ⊢[PRAAx] le Z (Z' + dZ)) (hZ2 : Γ ⊢[PRAAx] le Z' (Z + dZ))
    (hz : Γ ⊢[PRAAx] le z0 Z) (hd : Γ ⊢[PRAAx] le (two * dZ) z0) :
    (Γ ⊢[PRAAx] zle (ZT.ofNat z0 * (a' * ZT.ofNat Z - a * ZT.ofNat Z'))
      (ZT.ofNat (two * (da + M * dZ) * Z * Z'))) ∧
    (Γ ⊢[PRAAx] zle (ZT.ofNat z0 * (a * ZT.ofNat Z' - a' * ZT.ofNat Z))
      (ZT.ofNat (two * (da + M * dZ) * Z * Z'))) := by
  have e1 := zle_toZ hA1
  have e2 := zle_toZ hA2
  have e3 := zle_toZ hM1
  have e4 := zle_toZ hM2
  have f1 := natEq (eq_add_of_le hZ1)
  have f2 := natEq (eq_add_of_le hZ2)
  have f3 := natEq (eq_add_of_le hz)
  have f4 := natEq (eq_add_of_le hd)
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, Q.mk_succ,
    Q.mk_zero, Q.mk_one, map_add, map_mul, map_one, map_zero] at e1 e2 e3 e4 f1 f2 f3 f4
  set A := ZT.toZ Γ a
  set A2 := ZT.toZ Γ a'
  set s1 := 𝔟 (zsl (a' - a) (ZT.ofNat da))
  set s2 := 𝔟 (zsl (a - a') (ZT.ofNat da))
  set u := 𝔟 (zsl a (ZT.ofNat (M * Z)))
  set v := 𝔟 (zsl (-a) (ZT.ofNat (M * Z)))
  set p := 𝔟 (monus (Z' + dZ) Z)
  set q := 𝔟 (monus (Z + dZ) Z')
  constructor
  · refine zle_of_toZ2 (two * Z * (da + M * dZ) * (two * monus (Z' + dZ) Z + two * monus Z z0 +
        monus z0 (two * dZ)) + two * z0 * Z * zsl (a' - a) (ZT.ofNat da) +
        z0 * (zsl a (ZT.ofNat (M * Z)) * monus (Z + dZ) Z' + zsl (-a) (ZT.ofNat (M * Z)) * monus (Z' + dZ) Z)) ?_
    simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, Q.mk_succ,
      Q.mk_zero, Q.mk_one, map_add, map_mul, map_one, map_zero]
    linear_combination 2 * 𝔟 Z * 𝔟 z0 * e1 + q * 𝔟 z0 * e3 + p * 𝔟 z0 * e4 +
      (-A * 𝔟 z0 - 4 * 𝔟 M * 𝔟 Z * 𝔟 dZ - 𝔟 M * 𝔟 Z * 𝔟 z0 - 4 * 𝔟 Z * 𝔟 da) * f1 +
      𝔟 z0 * (A - 𝔟 M * 𝔟 Z) * f2 - 4 * 𝔟 Z * (𝔟 M * 𝔟 dZ + 𝔟 da) * f3 -
      2 * 𝔟 Z * (𝔟 M * 𝔟 dZ + 𝔟 da) * f4
  · refine zle_of_toZ2 (two * Z * (da + M * dZ) * (two * monus (Z' + dZ) Z + two * monus Z z0 +
        monus z0 (two * dZ)) + two * z0 * Z * zsl (a - a') (ZT.ofNat da) +
        z0 * (zsl a (ZT.ofNat (M * Z)) * monus (Z' + dZ) Z + zsl (-a) (ZT.ofNat (M * Z)) * monus (Z + dZ) Z')) ?_
    simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, Q.mk_succ,
      Q.mk_zero, Q.mk_one, map_add, map_mul, map_one, map_zero]
    linear_combination 2 * 𝔟 Z * 𝔟 z0 * e2 + p * 𝔟 z0 * e3 + q * 𝔟 z0 * e4 +
      (A * 𝔟 z0 - 4 * 𝔟 M * 𝔟 Z * 𝔟 dZ - 𝔟 M * 𝔟 Z * 𝔟 z0 - 4 * 𝔟 Z * 𝔟 da) * f1 -
      𝔟 z0 * (A + 𝔟 M * 𝔟 Z) * f2 - 4 * 𝔟 Z * (𝔟 M * 𝔟 dZ + 𝔟 da) * f3 -
      2 * 𝔟 Z * (𝔟 M * 𝔟 dZ + 𝔟 da) * f4

end LeanProofs.IPRA.Probability.BayesBudget
