# Actual Foundation DeltaZero interpretation: author receipt

26 October 2026. Author: `circuit_reduction`. This is the first approved
source-bound leaf of the frozen [proposal](../research/ha-foundation-deltazero-bridge-audit.md),
whose SHA is `3aa4c4e45c911be6e1ee54512f97f751b4c30e0a2a2c2fbf62ef1334ffdc8c9e`.
No GG-comparison or checker-normalization theorem was implemented.

The 216-line `FoundationHADeltaZero.lean` defines `ordinaryAux` on Foundation's
actual eight-constructor NNF syntax, restricted to its actual ordered
arithmetic language. It reuses the existing `termAux`, `liftBound`,
`liftFree` and existential `ltFormula` without changing their bodies.
The interpretation preserves ordinary conjunction/disjunction and both
quantifiers, interprets negative atoms as primitive PAHF negations, and
interprets truth as `bot → bot`. Its bound/free environments are arbitrary
PAHF terms, so the result retains all parameters and capture-avoiding shifts.

The primary theorem is:

```text
ordinary_decidable (hp : LO.FirstOrder.Arithmetic.DeltaZero p) bv fv :
  HA.Proves (HABoundedQuantifiers.dec (ordinaryAux bv fv p)).
```

`hierarchy_zero_decidable` proves it directly by induction on the actual
`Hierarchy Γ s p`, with the explicit condition `s=0`; all positive-level
unbounded/alternating constructors are impossible. Atom decisions are the
previously checked genuine HA equality and order proofs. The finite
negation/conjunction/disjunction proofs use only the intuitionistic
`Relative` rules, with complete finite contexts.

For each bounded constructor, `Rew.positive_iff` extracts an actual outer
term `u` with `t=Rew.bShift u`. `positive_bound` records this exact identity
and the existing `termAux_bShift` equation. Here `Positive` means no bound
slot zero; it does not assert a positive numerical value. `ordinary_bex`
is literally the accepted `bex`, with the shifted environments. The
induction hypothesis is closed under the fresh quantifier to provide the
object-language uniform decision required by `bex_decidable`.

`ordinary_ball` instead retains the actual source NNF body `neg L ∨ A`.
`guard_forward` proves its implication form intuitionistically;
`guard_reverse` requires and uses an actual HA decision of `L`. For the
bounded theorem that decision is the proved order-atom decision. `all_imp`
shifts the entire antecedent context before generalization and uses the
exact instantiation/rename identity. Thus the resulting decision does not
silently replace classical implication by intuitionistic implication.
`ordinary_decidable_relative` weakens the derived proof to an arbitrary
finite open context without a model or derivability oracle.

The 69-line checks cover zero as a legal source bound, rejection of the fresh
bound variable as a positive bound, old bound slots under a fresh binder,
two nested binders, negative order atoms, actual nested bounded-all/bounded-ex
with a bound depending on the preceding witness, sparse free parameters,
nontrivial substituted term environments and shifted finite contexts.
All 12 axiom reports are restricted to `propext`, `Classical.choice`, and
`Quot.sound`. In particular the finite HA guard/quantifier proofs report only
`propext` and `Quot.sound`. The standard metatheoretic choice dependency of
`positive_iff` is retained; no choice or classical rule is added to
`HA.Derives`.

I read the entire new main/check and both replay drivers before their
execution, and the relevant full hierarchy constructors, positive-bound
proof, NNF syntax, existing syntax bridge and bounded-quantifier proofs.
The final replay authenticates 101 current-source cached modules,
76 Foundation modules, 329 cached artifacts and 34 explicit external package/
toolchain boundaries. Both the original bounded author records/objects and
the selected accepted root primary are pinned, including the full original
19-file bundle. Root record
`8a321ccb5e0f1860701fd8e1e5319027de7ccc8e15458aac09a286ead4b9808c`
is checked, and the imported primary is exactly
`/tmp/ha-bounded-quantifiers-root-peer-gtq42hal/lib/DiophantineConsistency/HABoundedQuantifiers.olean`
with SHA `5aef4873ce228ef55ac107f2fb0c251da951552feee7d0acb92f0ca3061a992f`.
All 637 distinct final pins are checked before and after compilation. The
source-derived closure contains no reused client importing a fresh leaf.
No Foundation or prerequisite source was rebuilt.

Only the two new leaves were compiled, using Lean 4.32.0 with
`-M6000 -j1 -DElab.async=false`, regular fresh private outputs and a 512MiB
reserve. Final main/check passed in 2.349s/1.843s; main log is empty. Their
objects also match the preceding successful pair byte for byte. The final
private primary is `/tmp/foundation-ha-deltazero-author-dad_e2ln/lib`.

All development evidence is retained. The first main attempt failed on a
local implicit context placeholder and redundant `generalizing bv`, both
fixed without changing theorem statements. A separate attempt stopped at
the 512MiB reserve guard before any Lean invocation. The next main passed,
but checks failed because literal source zero lacked an `OfNat` instance;
using its exact nullary function constructor fixed that notation. The next
pair passed. The final pair used a separate preserved driver version adding
explicit authentication of all original-parent evidence, and passed again.
No failure was hidden, no placeholder proof was accepted, and no limits were
raised. Frozen sources and shared dependency objects were not edited.

Exact frozen pins:

- Main: `dd20f2b1f64fec8fed2eab70bb76d457a6e8fcd6eae19aa655f18b51da4afcab`.
- Checks: `0c515dce8468dedcbc6a6c46c7629b1af599b0799bc2557294fc5f7feeb07065`.
- Main object: `8077e247871af1b704e106824370382c23f2f8d1f9a5f410758a2fe8c675a567`.
- Checks object: `72fe7417064d203aa77f173804d85c71a7492b00790f13d16a72c5615c59eab8`.
- [Replay summary](foundation-ha-deltazero-replay.json): `74fa657079742ad6c20ad5e733376ddfc8457779a2fac17f6ec3e85dfdacc9b2`.
- [44-file attempt manifest](foundation-ha-deltazero-replay/FILES.json): `cf354c525a4b6dedb9410563d09899e4ce5ed7b655c1255c8ccf1957e093ee93`.

This is actual HA decidability for an ordinary interpretation under an
actual syntactic DeltaZero proof. It does not assert that the Foundation
proof checker is literally DeltaZero, normalize any delta-one checker,
prove a GG comparison, apply unbounded-existential DNE, or discharge the
current-equation/consistency equivalence. No maintained equation, shared
document, vendor source, or Git state was changed.
