# Doubled clause: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This records author inspection and fresh Lean checks, not an independent peer
review. Existing frozen modules and the maintained equation are unchanged.

The 166-line `Lean/DiophantineConsistency/DoubledClause2011.lean` has SHA256
`1285bb4332ad2dfabaee2a99eb1c7624d9a4c7c10e82dc3f25a2e6af92e6733f`.
The 54-line focused `DoubledClause2011Checks.lean` has SHA256
`01fafb8761d189147485c660b1bb38fa6751d73f411113e2c16021fa7fe1ff18`.
Both entire sources were reread after their successful compilation; neither
required an implementation correction during the first compile/check cycle.

The module defines the exact natural-number raw clause

```
2*n + 2048*((2^34-u)*n + W) + k + t + b
```

and its actual digit modulo `2^47`. The input hypotheses are `n≤1`,
`W,u<2^34`, `k≤57`, and `t,b≤1`. From these ranges alone it proves that the
raw value is below the radix and its outgoing carry is zero. In particular,
the outgoing bound is not assumed and does not depend on passing the mask.

The full mask lemma, for every natural `x`, is
`x &&& (2^45-4)=0 ↔ x%2^45≤3`. Its proof uses two bitwise divisions, the
standard all-ones mask identity, and Euclidean arithmetic; it performs no
finite case enumeration. The full clause decoder then proves exactly:

* empty: `n=0`, `W=0`, and `k+t+b≤3`;
* occupied: `n=1`, `W=u`, and `k+t+b≤1`.

Both converses are proved. The occupied raw value is exactly
`2^45+2+(k+t+b)`; the empty value is `k+t+b`. The incoming carry and temporal
bit are retained throughout. The focused checks accept an occupied incoming
carry of one, separately accept a temporal bit of one, and accept an empty
low value of three. They reject a second occupied low unit and unequal
unsigned copied/selected words. An explicit expanded-form check binds the
decoder to the printed arithmetic formula, not merely its local aliases.

Reproduction from the repository root, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/DoubledClause2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/DoubledClause2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/DoubledClause2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/DoubledClause2011Checks.lean
```

Both direct sequential commands exited zero. The main diagnostics are empty
(SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
The checks log SHA256 is
`da617cb608c135e9b34ad3a5b2b6f8bb9f3d633a53167c0b4c587ea6dd5398af`.
All eight printed axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound` (the raw/carry bounds use the smaller subset
`propext`, `Quot.sound`). There are no `sorry`, additional axioms, native
evaluation axioms, or imported project calibration hypotheses.

Scope: this is the generic full-word arithmetic required after one-hot
selection and fractional-phase zero have been established. It does not yet
identify the actual copied word or chosen tile's complemented tuple inside
the current cyclic stencil, prove whole-field alignment, or close the
native-language/refutation/consistency equivalence. Those remaining bindings
must use the actual physical coefficient map and cannot be inferred from
this arithmetic result alone.
