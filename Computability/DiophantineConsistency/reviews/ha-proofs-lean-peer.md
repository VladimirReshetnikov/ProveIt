# HAProofs: independent source review and isolated replay

Date: 2026-10-26. Reviewer: `/root/controller_certificate`.
Author of the reviewed packet: `/root/circuit_reduction`.

**PASS within the stated scope.** I found no hidden classical deduction rule,
incorrect binder side condition, or strengthened arithmetic axiom. The new
relation is conventional intuitionistic first-order arithmetic proof existence
over the existing arithmetic syntax. This is not a PA-to-HA translation or a
proof that HA proves the current consistency equivalence.

## Frozen bindings

| Artifact | SHA-256 |
| --- | --- |
| `HAProofs.lean`, 147 lines | `c4af3acb35ed46bd4d1dc36eba36500ff0254e69c6e552aa3cef9b468a1cd943` |
| `HAProofsChecks.lean`, 65 lines | `0e7aa30344f16944029a4fe0933b2cf8c18e316e5579659f2048788fb4321c1a` |
| `ha-proofs-dependency-replay.json` | `f8163c4c5325f30e1e9adfa04fbe3501ef67518072c46ed411b94531ea7ee4ba` |
| Fresh main object | `66103e7b07e3992fee919880c79d04f2d11bf2a7312b02a35530f3704300ddcc` |
| Fresh checks object | `c739ed0577b6c65731daf5f380f9d0c4cf4b8a4053b36fdd3617126bab5c568e` |

Both fresh objects are byte-identical to the author's corresponding objects.
All seven source files and five cached prerequisite objects were rehashed
after replay and were unchanged.

## Complete new-source and relevant prerequisite review

I read all 147 main lines, all 65 check lines, the author receipt and the entire
dependency receipt before execution. In the 66,936-line `PAHF.PASyntax` source,
I read the complete relevant definitions and constructors rather than claiming
a full monolith review: `Term`, `Formula`, term renaming/substitution and
`upSubst`; formula renaming/substitution, bounds/free-variable conventions and
closure; `instTerm`; every `Prov` constructor; `cons_sub`, `mem_map_sub`,
`BProv`; zero/successor substitutions; all six arithmetic axioms;
`inductionForm`, `Ax`, `Ax_s`, sentence closure and named axiom memberships.
The imported `FirstOrder.Fol.up` and `scons` binder conventions were also read.

The individual checks are:

* `Derives` has precisely the 16 listed intuitionistic natural-deduction rules.
  The old `Formula.Prov.P_lem` constructor is absent. There is no constructor
  taking a semantic truth, classical proof, choice witness or double-negation
  elimination as a route to a new `Derives` proof.
* Universal introduction maps **every** old assumption through
  `Formula.rename Nat.succ`, reserving index zero for the eigenvariable.
  Existential elimination shifts both the old context and the target, and
  keeps the opened existential matrix as the new assumption. These are the
  correct de Bruijn forms of the eigenvariable restrictions.
* `instTerm t` sends index zero to `t` and successor indices to the preceding
  variable. `Term.upSubst` preserves a bound zero and shifts the substituted
  outer terms under each binder. Thus universal elimination, existential
  introduction and Leibniz equality substitution are capture-avoiding.
* `Relative` uses a finite list of permitted axioms. `Proves` fixes that set to
  `Formula.Ax_s`; it does not use an arbitrary semantic axiom oracle.
  `Ax_s` consists exactly of the universally closed six arithmetic axioms
  and universally closed first-order induction instances. The existing
  conservative upper bound used by `sealPA` can introduce vacuous universal
  binders; it does not omit free parameters or add arithmetic strength.
* In `inductionForm phi`, the base instance drops variable zero; the successor
  substitution replaces only that variable by its successor while leaving
  parameter indices unchanged; the step and conclusion bind that variable.
  Sealing then closes the remaining parameters. This is full first-order
  induction, not induction over arbitrary Lean predicates or the shallow
  `PA.Model.induction` field.
* `erase` structurally maps each new derivation to its corresponding classical
  rule and never invokes `P_lem`. `relative_to_classical` preserves the same
  finite axiom list. Neither has the reverse direction. `weaken` handles
  shifted contexts using the actual read list-inclusion helpers.

The focused examples test all six axioms, arbitrary formula induction, a
concrete eigenvariable shift, `∀x ∃y, x=y`, the exact existential-elimination
signature, equality symmetry, explosion and empty-axiom identity. These are
positive signature checks; this review does not present them as a formal
independence proof that excluded middle is unprovable.

## Authenticated private replay

I independently compared current and cached source bytes for all five custom
prerequisites: `PAHF.PASyntax`, `PAHF.AckermannHFCore`,
`FirstOrder.Completeness`, `FirstOrder.Calculus`, `FirstOrder.Fol`.
Their source hashes, direct import lists and cached object hashes matched the
receipt. The repository and cache `lean-toolchain` and `lake-manifest.json`
matched byte-for-byte. The actual compiler reported Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

Only those authenticated objects were copied into the new private directory
`/tmp/ha-proofs-peer-kpqxgt0z`; neither target object was present initially.
The main and checks were rebuilt serially with that directory first on
`LEAN_PATH`, `-M6000 -j1`, and their source-level `Elab.async false`:

```bash
lake env bash -c 'export LEAN_PATH="/tmp/ha-proofs-peer-kpqxgt0z:$LEAN_PATH"; lean -M6000 -j1 -o /tmp/ha-proofs-peer-kpqxgt0z/DiophantineConsistency/HAProofs.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/HAProofs.lean'
lake env bash -c 'export LEAN_PATH="/tmp/ha-proofs-peer-kpqxgt0z:$LEAN_PATH"; lean -M6000 -j1 -o /tmp/ha-proofs-peer-kpqxgt0z/DiophantineConsistency/HAProofsChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/HAProofsChecks.lean'
```

Both exited zero. `main.log` is empty. `checks.log` contains ten intended
reports: four have no axioms; the other six use only `propext` and, for
weakening, `Quot.sound`. None lists `Classical.choice`, `sorryAx` or a new
axiom. This is a metatheoretic audit of these declarations, not a claim that
all imported classical proof developments have acquired intuitionistic proofs.
The private `authenticated-inputs.json` records the checked input copies.

No prerequisite was freshly rebuilt, no shared object was overwritten, no
proof limit was raised, and no incoming script was run. In particular this
is **not** a fresh replay of the PASyntax monolith or its full library closure.

The reviewer did not author these HA or PAHF modules. The reviewer did author
the separate current witness adapter and several Diophantine native modules;
none is a prerequisite of this HA packet. Interoperability with the existing
Foundation intuitionistic/Gödel–Gentzen development and the internal arithmetic
equivalence remains separate work. No source correction is requested.
