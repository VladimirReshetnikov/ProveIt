# Counterexample case with a finite universal prefix

`ParsonsGuardPrefix.Guard` describes a proposition that is Σ₁ or has a leading
universal whose fresh-variable instance again has this property. The universal
constructor also stores its Π₂ classification. This is an explicit descriptor;
the module does not yet derive such a descriptor from every syntactic strict
prenex Π₂ formula or from an arbitrary `Hierarchy Π 2` formula.

`counter_prefix` handles a marked induction counterexample case whose first
side has such a descriptor. It structurally opens every leading universal at a
fresh variable, shifting all marked entries and terms, then uses the existing
Σ₁-guard counterexample case and universally closes the resulting actual
PA-minus rule proof. The projected disjunction of **all other side entries
must already be Σ₁**. Its explicit hypothesis `Below H` supplies the desired
rule proof for **every** marked cut-free derivation of height strictly below
`H`; the original existential conclusion's height must be at most `H`.
The theorem does not prove this strong induction hypothesis.

Two fresh Lean 4.32 builds of source and checks passed without warnings under
`-M6000 -j1 -DElab.async=false`; both objects and complete logs match. Both
axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The
[16-file replay manifest](parsons-guard-prefix-replay/FILES.json) has SHA-256
`879ef9434305a264f885611e0ecf4f6fc70c85e8a3f652640adc060caa58b020`.
The direct `ParsonsFreshOpen` source hash
`3dd42344fdd5a16be931ef094b5ad9d10996688c0aa9e4dcec435b6642785ae1`
matches its frozen snapshot, and its object hash is
`e89de03bf2a3fd75c382ba46aecd5d1e26c9fdab7d89429ee2f5aaad4f8b42e5`.
Earlier provider chains, Foundation/Mathlib, and completeness objects remain
an inherited boundary, not a fresh transitive source audit.

The Σ₁-remainder condition, descriptor construction, case dispatch, and global
well-founded recursion remain open. This is not conservation and does not
establish PRA-provability of the requested equivalence. The HA theorem for
the maintained 14-variable PDF equation is already established separately.

A third independent replay at `/tmp/parsons-guard-prefix-build-66wcm1l6`
passed with matching source, object and complete log hashes; its provider
boundary is the same as in the two recorded builds.
