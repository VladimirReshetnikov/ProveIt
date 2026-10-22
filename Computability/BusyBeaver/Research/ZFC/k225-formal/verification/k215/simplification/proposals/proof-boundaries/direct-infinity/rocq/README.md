# Direct Infinity: independent Rocq/Coq proof core

`DirectInfinity.v` ports the accompanying Lean mathematical core. It uses the
exact quantifier order of `KSeed222.SeedProp`, but has no project imports and
does not instantiate the actual `FormSeed` schema or final K215 endpoint.

The central observation is that the seed container is closed under witnesses
of any serial relation whose range remains in the desired domain. In the
closure clause, take the subset variable to be the current container member
itself. The subset obligation is then reflexivity. For the tagged successor
relation, this yields a successor-closed container. Adjoin the designated
empty representative and transport the result to the quotient.

## Results

- `seed_serial_container`: a seed instance, a serial relation on a domain,
  and its range condition produce a nonempty witness container closed under
  that relation.
- `succ_tag`: raw von Neumann successor preserves the tag.
- `seed_tagged_container`: bounded tagged adjunction adds the initial element
  and produces the tagged successor-closed container.
- `tagged_inductive`: restrict the result to tagged representatives, using
  equality of the underlying values.
- `quotient_successor`: exact raw successors become ordinary successors in
  the quotient.
- `quotient_infinity`: raw emptiness and an inductive set descend to quotient
  emptiness and an ordinary inductive set.
- `quotient_successor_rel` and `quotient_infinity_rel`: versions whose raw
  equality is an explicit reflexive relation respected by the quotient map.

All hypotheses are explicit. The core proves no unconditional Infinity
statement. The actual set-theoretic application must supply the seed
instance, tagged successors, bounded adjunction, empty representative,
surjectivity, and the displayed atomic membership presentation.

## Why the equality parameter matters in Rocq

Lean's `Subtype.ext` relies on its built-in proof irrelevance. In ordinary
Rocq, equality of the underlying elements of arbitrary `sig` values does not
by itself give Leibniz equality of their proof fields. The port avoids an
axiom by defining `tagged_eq` as equality of the underlying representatives.
`tagged_inductive` consequently concludes `InductiveRel` with that relation.
The generalized quotient theorems require its reflexivity and the explicit
adapter obligation that equal representatives have equal quotient images.
The ordinary `quotient_successor` and `quotient_infinity` are the special case
of raw Leibniz equality and have the same mathematical conclusion as Lean.
No functional extensionality, propositional extensionality, excluded middle,
choice, proof irrelevance, or project axiom is assumed by these theorems.

## Verified scope

The standalone module freshly compiled with Coq 8.18.0 / OCaml 4.14.1. All
eight `Print Assumptions` reports were closed under the global context.
Recursive `coqchk -o DirectInfinity` passed and reported that the loaded
context was closed. No precompiled project objects were reused. The source
is 169 lines / 7,881 bytes, including comments and assumption reports.

The theorem is a checked replacement *mathematical route* for the existing
singleton/index/inductive-attempt construction. It is not a checked deletion
of that chain from the complete Rocq endpoint. The production-designated
Rocq 9.1.0 acceptance lane, actual formula adapters, affected clients, and
full endpoint remain separate integration obligations.

## Reproduce

With Python 3.10+ in a POSIX/WSL environment and a complete Coq/Rocq install:

```sh
python3 check.py --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /tmp/k215-direct-infinity-check
```

The driver verifies the source hash, compiles into a new directory, checks
the eight closed reports, and invokes the recursive kernel checker. It
records compiler/checker hashes, source hashes, timings, and logs. No network
or repository checkout is needed. `evidence/` retains the executed result.

Package the `.v`, driver, provenance JSON, README and evidence. Exclude the
local `.vo`, `.vok`, `.vos`, and `.glob` compilation products.
