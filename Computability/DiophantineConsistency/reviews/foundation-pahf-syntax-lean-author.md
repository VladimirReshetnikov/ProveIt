# Foundation ordered arithmetic to PAHF: syntax-only author receipt

Author: `circuit_reduction`. This is the author's review and fresh leaf build,
not an independent peer review. Both complete new sources and the private
cache-selection/freeze drivers were read before execution. The final sources
were read again in full before this freeze.

## Frozen scope and files

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationPAHFSyntax.lean` | 252 | `6ef6d070feed7382fe5e90fbb1edf9dba41aae33e3ca65b049c16a1b015ede35` |
| `Lean/DiophantineConsistency/FoundationPAHFSyntaxChecks.lean` | 87 | `2845c0f816f450b00a89ecfad470d4871b076ee28c90a15974b3579c4d5d360e` |
| `reviews/foundation-pahf-syntax-dependency-replay.json` | — | `cae0069bc912513e9adfc99e9bb0db2a2a897301482badaf263d4c8636bad30a` |

The selected sources and objects were reauthenticated after repository snapshot
`891c86e0b2970feb2b7442420d61c37ee7233ff2`; no selected dependency drift was found.
The imports are exactly `Foundation.FirstOrder.Intuitionistic.Rew` and
`PAHF.PASyntax`. Their joint use succeeds without importing broad
`Mathlib.Tactic` or triggering the unrelated `Matrix.map` declaration collision.

## What the theorems establish

Foundation bound variables and free variables have explicit independent term
environments. Its actual ordered-ring symbols translate as `0`, `S 0`,
addition and multiplication. Equality preserves its two arguments. Strict order
is the PAHF formula `exists z, a + S z = b`, with both translated arguments
renamed beneath the new existential binder.

`termAux_subst`, `termAux_rename` and `termAux_rew` prove generic environment
compatibility. `formulaAux_subst`, `formulaAux_rename` and `formulaAux_rew`
prove the corresponding laws for every intuitionistic source formula, including
both quantifiers and the additional binder in translated order. The quantifier
cases use the actual Foundation `Rew.q` equations and PAHF `upSubst` laws.
No evaluation in a standard or nonstandard model substitutes for these syntax
identities.

The canonical interpretation places bound index `i` at target index `i.val`
and source free index `j` at target index `n+j` beneath `n` source binders.
`formula_all` and `formula_exs` preserve literal binders. `formula_free` applies
to one outer bound variable, as required by the source logical rules; it does
not falsely claim the same identity for arbitrary bound depth.
`formula_shift` applies to an unbound source formula and gives exactly the
PAHF eigenvariable shift. `formula_inst` translates one-variable source
instantiation into PAHF `Formula.subst (Formula.instTerm ...)`.
`formula_empty_subst` identifies insertion beneath a fresh binder with the
same target shift. These restrictions are explicit in the theorem types.

The checks cover zero/one/addition/multiplication, distinct bound/free variables,
equality orientation, literal negation, two nested source binders plus the
order witness, free-variable shift through those three binders, and
instantiation by a term containing a free variable beneath an inner quantifier
and order witness. A closed source sentence is also checked to produce the
stated closed PAHF sentence. This packet does not assert a general target
closedness theorem beyond those syntax laws and that focused example.

## Fresh execution and provenance

Both new leaves were compiled directly using Lean 4.32.0 with
`-M6000 -j1` and source-level `Elab.async false`, in the private overlay
`/tmp/foundation-pahf-syntax-78sp4zxe`. Exact commands, final logs, object hashes,
source hashes, compiler/package pins and the complete selected custom
prerequisite records are in the JSON receipt above.

The main's terminal exit code was zero and its final log is empty. The checks'
terminal exit code was zero; all 15 axiom reports contain only `propext` and/or
`Quot.sound`. There are no final warnings, `sorry`, `native_decide`, custom axioms
or classical proof-to-intuitionistic proof oracle in the new sources.

Fresh main object:
`51ecaff598ea2d006a4849ba7414ea7b683a7899e2e7eab998ecf73eda20ff3a`.
Fresh checks object:
`9be22eb9c80e9400bbb42a58506fe4a6f5e0ffa432436651f9822228aa9c73de`.

Prerequisites were reused, not freshly rebuilt: the previously authenticated
59-module Foundation GG closure (236 object companions) and five-module PAHF
closure, together with their pinned Mathlib/compiler packages. Every selected
custom source/object and Foundation trace hash was rechecked before the first
build and at final freeze. The PAHF current/cache source equality was checked
again. This is not a fresh build of Foundation, PAHF's large source closure,
or all of Mathlib. Private symlinks point to authenticated objects; no accepted
source, shared object, vendor file, umbrella or Git state was modified.

## Remaining boundary

This packet contains no proof-calculus translation, arithmetic-axiom proof,
induction transfer, or assertion of `HA.Proves` for a translated Foundation
arithmetic theory. In particular, the Foundation term `x + 1` translates to
literal PAHF addition by `S 0`; identifying it with `S x` requires an arithmetic
proof, not a syntax rewrite. The generic sentence constructor alone is not a
closedness/provability bridge. The existing Foundation GG theorem, conventional
HA arithmetic obligations, sentence-closure conventions and the exact current
215-state arithmetic calibration remain separate tasks. No internal HA
consistency equivalence is claimed here.
