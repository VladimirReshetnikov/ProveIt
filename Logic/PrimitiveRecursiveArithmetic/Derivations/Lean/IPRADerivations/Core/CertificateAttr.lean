import Mathlib.Tactic.Ring

/-!
# The simp set `ipra_defs`

Definitions and evaluation lemmas that the certificate tactics of `Core/CertificateTactics` should see through:
tag a definition of a term (`@[ipra_defs] def dot …`, or `attribute [local ipra_defs] dot det` in a module that
uses it) and `ipra_lc`, `ipra_zle … with`, `ipra_absurd` unfold it before the ring identity is checked. A lemma
`toZ Γ (f …) = …` may be tagged in the same way.

The attribute is declared in a module of its own because an attribute cannot be used in the module that
declares it.
-/

/-- Definitions unfolded, and evaluation lemmas used, by the certificate tactics. -/
register_simp_attr ipra_defs
