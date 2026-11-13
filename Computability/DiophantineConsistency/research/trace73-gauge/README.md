# Centered 73-row gauge

For ports `p` and coordinates `v`, set `h = p₀ v₀`, `q = h+1`, and
`s = (p₁+v₅)q+1`.  The proposed all-ring move changes only

```
v₁ ↦ v₁+h t,   v₂ ↦ v₂+h² t,   v₇ ↦ v₇−s t.
```

The rank is unchanged, `B` decreases by `h s t`, and the centered carrier
and literal graph value are unchanged.  The accompanying Lean file proves
these identities over every commutative ring.

These identities do not assert the existence of any zero, nor do they by
themselves preserve positive natural coordinates: the new center must be
positive.  In particular, they do not give a counterexample to an
equivalence between existence of 73-row and 75-row positive zeros.  They
suggest a route to testing whether individual 73-row zeros must have
nonnegative `B`; proving the needed center bound at an actual zero remains
open.

Author check `attempt04` exited 0 and produced
`/tmp/trace73-gauge-r0w9s5ez/Trace73Gauge.olean` with SHA-256
`397b4aec0c8ed0042867e0e24cb0cc479213769262bda2248b9fccc9d76e7ca9`.
All four theorem reports list only `propext` and `Quot.sound`.  The source
SHA-256 is `ea63e8f4c0c59b5548b972f176bbb33b320cbe71d2968f4603aad6b561ce85c4`,
the runner SHA-256 is
`388718996da8792634ac12cc5c31fe52fda36a2e3ae366170b325c7b4b7ae2e7`,
and the terminal record SHA-256 is
`8948683f35f6d24bfd6abdeadcd7a89c239b263d57a7b9d5fdfb18d27761e66d`.
The three prior failed attempts remain in `observations/`.

The runner pins the direct literal and centered graph objects and selected
shared providers; it inherits the remainder of their provider and package
ancestry and does not authenticate a complete transitive build.  This is an
author check, not an independent Lean replay.
