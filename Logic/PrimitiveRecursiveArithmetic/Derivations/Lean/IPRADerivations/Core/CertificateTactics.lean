import IPRADerivations.Core.IntCertificates
import IPRADerivations.Core.CertificateAttr

/-!
# One-line certificates

Most derivations of an equation or an inequality between polynomial terms have the same shape: the derived
equations in play are read in the ring of differences `Groth (Q Γ)` (`natEq`, `ZT.toZ_eq`), everything is pushed
through the term operations, and the goal is a linear combination of the hypotheses, checked by `ring`. The
tactics below do the three steps at once, so that such a derivation is its certificate:

* `ipra_norm` pushes `Q.mk`, `Groth.ι` and `ZT.toZ` through the term operations, unfolds the slacks `sl`, `zsl`
  and the definitions tagged `ipra_defs`; `ipra_norm [l₁, …]` uses the extra simp lemmas `l₁, …`;
* `ipra_lc e` derives `Γ ⊢ s ≐ t` or `Γ ⊢ ZT.eq u v` (or proves an equation of `Groth (Q Γ)`) from the linear
  combination `e` of ring equations, for instance `ipra_lc 2 * natEq h₁ - ZT.toZ_eq h₂`; `ipra_lc` alone is
  for polynomial identities;
* `ipra_zle z with e` derives `Γ ⊢ zle u v` from the certificate `z`, a `Nonneg` combination of slacks and
  squares with `toZ v − toZ u = z` modulo the linear combination `e` (`ipra_zle2` for
  `2 (toZ v − toZ u) = z`);
* `ipra_absurd z with e` derives any formula from a `Nonneg` certificate `z` that equals `−1`;
* `ipra_cast h` derives an equation between integer terms built from numerals from the fact `h : a = b` about
  natural numbers of the metatheory (a table checked by `decide`).

In every form `[l₁, …]` after the tactic name adds simp lemmas to the normalization, and the certificate `z` is
checked to be `Nonneg` by `znn`.
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

/-- Push `Q.mk`, `Groth.ι` and `ZT.toZ` through the term operations and unfold slacks and the definitions
tagged `ipra_defs`. -/
syntax "ipra_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

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

/-- Close a ring equation after `ipra_norm`, moving casts of natural numbers inwards (`push_cast`) if needed. -/
syntax "ipra_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_close) => `(tactic| first
      | (ipra_norm <;> ring1) | ring1 | (ipra_norm <;> push_cast <;> ring1) | (push_cast <;> ring1))
  | `(tactic| ipra_close [$ls,*]) => `(tactic| first
      | (ipra_norm [$ls,*] <;> ring1) | ring1 | (ipra_norm [$ls,*] <;> push_cast <;> ring1) | (push_cast <;> ring1))

/-- `ipra_lc e` derives a natural-number equation `s ≐ t` or an integer equation `ZT.eq u v`, or proves an
equation of `Groth (Q Γ)`, as the linear combination `e` of ring equations such as `natEq h` and
`ZT.toZ_eq h`. Without `e` the goal must be a polynomial identity. -/
syntax "ipra_lc" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (ppSpace colGt term)? : tactic

macro_rules
  | `(tactic| ipra_lc $[$e:term]?) => `(tactic| first
      | (with_reducible apply LeanProofs.IPRA.ZT.derive
         linear_combination (norm := ipra_close) $[$e:term]?)
      | (with_reducible apply LeanProofs.IPRA.deriveNat
         linear_combination (norm := ipra_close) $[$e:term]?)
      | linear_combination (norm := ipra_close) $[$e:term]?
      | (apply LeanProofs.IPRA.ZT.derive
         linear_combination (norm := ipra_close) $[$e:term]?)
      | (apply LeanProofs.IPRA.deriveNat
         linear_combination (norm := ipra_close) $[$e:term]?))
  | `(tactic| ipra_lc [$ls,*] $[$e:term]?) => `(tactic| first
      | (with_reducible apply LeanProofs.IPRA.ZT.derive
         linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?)
      | (with_reducible apply LeanProofs.IPRA.deriveNat
         linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?)
      | linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?
      | (apply LeanProofs.IPRA.ZT.derive
         linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?)
      | (apply LeanProofs.IPRA.deriveNat
         linear_combination (norm := ipra_close [$ls,*]) $[$e:term]?))

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
