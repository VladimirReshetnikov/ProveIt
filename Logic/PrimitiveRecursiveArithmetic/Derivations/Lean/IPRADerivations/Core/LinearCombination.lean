import IPRADerivations.Core.Tactic
import IPRADerivations.Core.CertificateAttr

/-!
# Equations as linear combinations

`ipra_lc e` derives `Γ ⊢ s ≐ t` or `Γ ⊢ ZT.eq u v` (or proves an equation of `Groth (Q Γ)`) from the linear
combination `e` of ring equations, for instance `ipra_lc 2 * natEq h₁ - ZT.toZ_eq h₂`; `ipra_lc` alone is for
polynomial identities. The hypotheses are written inline: the three steps of the usual ending of a derivation
(read the derived equations in the ring of differences, push `Q.mk`, `Groth.ι` and `ZT.toZ` through the term
operations, check the combination by `ring`) are done at once.

* `ipra_norm` is the normalization: it pushes the evaluation maps through the term operations and unfolds the
  definitions tagged `ipra_defs`; `ipra_norm [l₁, …]` uses the extra simp lemmas `l₁, …`;
* `ipra_close` closes a ring equation after `ipra_norm`, moving casts of natural numbers inwards if needed.

This module depends only on `Core/Tactic`, so that the lower Core modules can use `ipra_lc`.
`Core/CertificateTactics` extends `ipra_norm` by the slacks of derived inequalities and finite sums of integer
terms, and adds the order certificates.
-/

/-- Push `Q.mk`, `Groth.ι` and `ZT.toZ` through the term operations and unfold slacks and the definitions
tagged `ipra_defs`. -/
syntax "ipra_norm" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_norm) => `(tactic| simp only [ipra_defs,
      LeanProofs.IPRA.Q.mk_add, LeanProofs.IPRA.Q.mk_mul, LeanProofs.IPRA.Q.mk_succ,
      LeanProofs.IPRA.Q.mk_zero, LeanProofs.IPRA.Q.mk_one, LeanProofs.IPRA.Q.mk_num,
      map_add, map_mul, map_one, map_zero, map_natCast, map_ofNat,
      LeanProofs.IPRA.ZT.toZ_add, LeanProofs.IPRA.ZT.toZ_mul, LeanProofs.IPRA.ZT.toZ_neg,
      LeanProofs.IPRA.ZT.toZ_sub, LeanProofs.IPRA.ZT.toZ_sq, LeanProofs.IPRA.ZT.toZ_ofNat,
      LeanProofs.IPRA.ZT.toZ_natLit, LeanProofs.IPRA.ZT.toZ_var2,
      Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])
  | `(tactic| ipra_norm [$ls,*]) => `(tactic| simp only [$ls,*, ipra_defs,
      LeanProofs.IPRA.Q.mk_add, LeanProofs.IPRA.Q.mk_mul, LeanProofs.IPRA.Q.mk_succ,
      LeanProofs.IPRA.Q.mk_zero, LeanProofs.IPRA.Q.mk_one, LeanProofs.IPRA.Q.mk_num,
      map_add, map_mul, map_one, map_zero, map_natCast, map_ofNat,
      LeanProofs.IPRA.ZT.toZ_add, LeanProofs.IPRA.ZT.toZ_mul, LeanProofs.IPRA.ZT.toZ_neg,
      LeanProofs.IPRA.ZT.toZ_sub, LeanProofs.IPRA.ZT.toZ_sq, LeanProofs.IPRA.ZT.toZ_ofNat,
      LeanProofs.IPRA.ZT.toZ_natLit, LeanProofs.IPRA.ZT.toZ_var2,
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
