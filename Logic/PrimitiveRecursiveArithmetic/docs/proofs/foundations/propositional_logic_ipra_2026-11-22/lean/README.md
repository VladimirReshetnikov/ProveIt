# Lean source status

**These sources have not been compiled.** The production environment had no
`lean`, `lake`, or `elan` executable. They are proof candidates and a precise
formalization starting point, not a claim of completed Lean verification.

`Propositional.lean` imports only Lean. It contains formula syntax; Boolean and
proposition-valued evaluation; substitution, atom occurrences, and size; complete proof
candidates for identity/composition of substitution and semantic substitution;
a natural-deduction datatype with a Boolean IPC/CPC switch; constructive
soundness proofs; and direct identity/conjunction-commutativity proof objects.
It contains no proof holes, additional axioms, or classical oracle. Absence of
such tokens is not a substitute for compilation.

`ObjectExamples.lean` imports the user's existing `ConciseIPRA.PR` module and
contains eight constructor-only proof candidates whose conclusions have the
form `Prf PRAAx [] formula`. This directly targets the existing iPRA object
logic. The interface was read from ProveIt commit
`803d951d15834da5571e26d1f39988d921b29760`; the file belongs alongside that pinned
project and inherits its Lean toolchain/dependencies. It also defines closed numerical completeness sentence templates without
asserting them as theorems. It is deliberately not in the standalone default
Lake root.

## First verification step

With a supported Lean 4 toolchain installed, run:

```sh
cd lean
lake build
```

For the repository adapter, copy `ObjectExamples.lean` into the pinned
ConciseIPRA project's source tree and run `lake env lean` on the copied file.
Use the repository's own `lean-toolchain` and dependency lockfile. No exact
compiler compatibility is claimed before that check.

See `FormalizationPlan.md` for the nontrivial remaining path from the reference
algorithms and human proofs to numerical iPRA derivations. In particular,
proving an algorithm correct in Lean's metatheory does not prove its encoded
statement in iPRA.
