import IPRADerivations.Core.IntCertificates
import IPRADerivations.Core.LinearCombination

/-!
# One-line order certificates

`Core/LinearCombination` derives equations between polynomial terms as linear combinations of ring equations
(`ipra_lc e`). This module adds the same for the order of integer terms and for finite tables, on top of
`Core/IntCertificates`:

* `ipra_zle z with e` derives `Γ ⊢ zle u v` from the certificate `z`, a `Nonneg` combination of slacks and
  squares with `toZ v − toZ u = z` modulo the linear combination `e` (`ipra_zle2` for
  `2 (toZ v − toZ u) = z`); `ipra_zle z` alone is for a polynomial identity;
* `ipra_absurd z with e` derives any formula from a `Nonneg` certificate `z` that equals `−1`;
* `ipra_cast h` derives an equation between integer terms built from numerals from the fact `h : a = b` about
  natural numbers of the metatheory (a table checked by `decide`);
* `ipra_norm` is extended by the slacks `sl`, `zsl` of derived inequalities and by finite sums of integer terms.

In every form `[l₁, …]` after the tactic name adds simp lemmas to the normalization, and the certificate `z` is
checked to be `Nonneg` by `znn`.

Importing this module brings `Core/IntCertificates` and `Core/LinearAlgebra` into scope; a module that needs only
`ipra_lc` should import `Core/LinearCombination`.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- An integer equation from a fact about natural numbers: both sides evaluate to casts. -/
theorem ZT.derive_cast {u v : ZT n} {a b : ℕ} (h : a = b) (hu : ZT.toZ Γ u = (a : Groth (Q Γ)))
    (hv : ZT.toZ Γ v = (b : Groth (Q Γ))) : Γ ⊢[PRAAx] ZT.eq u v :=
  ZT.derive (by rw [hu, hv, h])

end LeanProofs.IPRA

/-- `ipra_norm` of `Core/LinearCombination`, extended by the slacks `sl`, `zsl` of derived inequalities and by
finite sums of integer terms. -/
macro_rules
  | `(tactic| ipra_norm) => `(tactic| simp only [ipra_defs,
      LeanProofs.IPRA.zsl_def, LeanProofs.IPRA.sl_def,
      LeanProofs.IPRA.Q.mk_add, LeanProofs.IPRA.Q.mk_mul, LeanProofs.IPRA.Q.mk_succ,
      LeanProofs.IPRA.Q.mk_zero, LeanProofs.IPRA.Q.mk_one, LeanProofs.IPRA.Q.mk_num,
      map_add, map_mul, map_one, map_zero, map_natCast, map_ofNat,
      LeanProofs.IPRA.ZT.toZ_add, LeanProofs.IPRA.ZT.toZ_mul, LeanProofs.IPRA.ZT.toZ_neg,
      LeanProofs.IPRA.ZT.toZ_sub, LeanProofs.IPRA.ZT.toZ_sq, LeanProofs.IPRA.ZT.toZ_ofNat,
      LeanProofs.IPRA.ZT.toZ_natLit, LeanProofs.IPRA.ZT.toZ_var2, LeanProofs.IPRA.ZT.toZ_sumFin,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])
  | `(tactic| ipra_norm [$ls,*]) => `(tactic| simp only [$ls,*, ipra_defs,
      LeanProofs.IPRA.zsl_def, LeanProofs.IPRA.sl_def,
      LeanProofs.IPRA.Q.mk_add, LeanProofs.IPRA.Q.mk_mul, LeanProofs.IPRA.Q.mk_succ,
      LeanProofs.IPRA.Q.mk_zero, LeanProofs.IPRA.Q.mk_one, LeanProofs.IPRA.Q.mk_num,
      map_add, map_mul, map_one, map_zero, map_natCast, map_ofNat,
      LeanProofs.IPRA.ZT.toZ_add, LeanProofs.IPRA.ZT.toZ_mul, LeanProofs.IPRA.ZT.toZ_neg,
      LeanProofs.IPRA.ZT.toZ_sub, LeanProofs.IPRA.ZT.toZ_sq, LeanProofs.IPRA.ZT.toZ_ofNat,
      LeanProofs.IPRA.ZT.toZ_natLit, LeanProofs.IPRA.ZT.toZ_var2, LeanProofs.IPRA.ZT.toZ_sumFin,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])

/-- `ipra_zle z with e` derives `Γ ⊢ zle u v` from the `Nonneg` certificate `z`: `toZ v − toZ u = z` is checked
as the linear combination `e` of ring equations (a polynomial identity when `with e` is absent). -/
syntax "ipra_zle" (" [" Lean.Parser.Tactic.simpLemma,* "]")? ppSpace colGt term " with " term : tactic

/-- The same from `2 (toZ v − toZ u) = z`. -/
syntax "ipra_zle2" (" [" Lean.Parser.Tactic.simpLemma,* "]")? ppSpace colGt term (" with " term)? : tactic

/-- `ipra_absurd z with e` derives the goal, any formula, from a `Nonneg` certificate `z` equal to `−1` modulo
the linear combination `e`. -/
syntax "ipra_absurd" (" [" Lean.Parser.Tactic.simpLemma,* "]")? ppSpace colGt term (" with " term)? : tactic

macro_rules
  | `(tactic| ipra_zle $z with $e) => `(tactic| (
      refine LeanProofs.IPRA.zle_of_comb $z ?_ (by znn)
      linear_combination (norm := ipra_close) $e:term))
  | `(tactic| ipra_zle [$ls,*] $z with $e) => `(tactic| (
      refine LeanProofs.IPRA.zle_of_comb $z ?_ (by znn)
      linear_combination (norm := ipra_close [$ls,*]) $e:term))

macro_rules
  | `(tactic| ipra_zle2 $z $[with $e]?) => `(tactic| (
      refine LeanProofs.IPRA.zle_of_comb_two $z ?_ (by znn)
      linear_combination (norm := ipra_close) $[$e:term]?))
  | `(tactic| ipra_zle2 [$ls,*] $z $[with $e]?) => `(tactic| (
      refine LeanProofs.IPRA.zle_of_comb_two $z ?_ (by znn)
      linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?))

macro_rules
  | `(tactic| ipra_absurd $z $[with $e]?) => `(tactic| (
      refine LeanProofs.IPRA.false_of_comb $z ?_ (by znn) _
      linear_combination (norm := ipra_close) $[$e:term]?))
  | `(tactic| ipra_absurd [$ls,*] $z $[with $e]?) => `(tactic| (
      refine LeanProofs.IPRA.false_of_comb $z ?_ (by znn) _
      linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?))

/-- `ipra_cast h` derives `Γ ⊢ ZT.eq u v` for integer terms built from numerals (finite sums and products of
`ZT.natLit`) from the fact `h : a = b` about natural numbers, the two sides being the casts of `a` and `b`. -/
macro "ipra_cast " h:term : tactic => `(tactic| (
  refine LeanProofs.IPRA.ZT.derive_cast $h ?_ ?_ <;>
    (first
      | (ipra_norm <;> first | with_reducible rfl | (push_cast <;> first | with_reducible rfl | ring1))
      | with_reducible rfl)))

/-- `ipra_zle z` of `Core/IntCertificates`, now seeing through the definitions tagged `ipra_defs`. -/
macro_rules
  | `(tactic| ipra_zle $z:term) => `(tactic| (
      refine LeanProofs.IPRA.zle_of_comb $z ?_ (by znn)
      ipra_close))
