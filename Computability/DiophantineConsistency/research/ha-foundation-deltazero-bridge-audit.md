# Next source-bound HA bounded-formula bridge

Read-only audit by `circuit_reduction`, 26 October 2026. No implementation or
compiler invocation is part of this audit. The proposed endpoints below are
not yet theorems. The frozen bounded-quantifier packet already supplies the
actual HA finite-bound induction that this proposal needs.

## Recommended first leaf

Use **Foundation's existing `Semiformula` and `Hierarchy Γ 0`**, not a new
inductive grammar of bounded PAHF formulas. A small ordinary interpretation
of the existing NNF syntax is needed: the inspected Foundation first-order
intuitionistic/GG sources contain the negative translation, but no ordinary
NNF-to-intuitionistic interpretation that can be reused for this purpose.
This is a syntax interpretation, not a replacement GG algorithm.

Suggested new module: `FoundationHADeltaZero`, with focused checks. Imports:

```lean
import DiophantineConsistency.HABoundedQuantifiers
import Foundation.FirstOrder.Arithmetic.Basic.Hierarchy
```

The second import is already in the first import's authenticated closure.
No new Foundation module or package boundary is needed.

Define the following eight-constructor recursion over **actual** source NNF:

```text
ordinaryAux (bv : Fin n → PA.Term) (fv : ξ → PA.Term)
    : Semiformula ℒₒᵣ ξ n → PA.Formula

rel eq/lt v  ↦ eq/ltFormula of the existing termAux values
nrel eq/lt v ↦ neg of that same atom
verum       ↦ imp bot bot
falsum      ↦ bot
and/or      ↦ the corresponding PAHF constructor
all/exs     ↦ all/ex, recursively using liftBound bv and liftFree fv.
```

Here `termAux`, `liftBound`, `liftFree` and `ltFormula` are the existing
`FoundationPAHFSyntax` definitions. Do not define a new term compiler or
equate source `x+1` with PAHF `S x`; the existing compiler retains the exact
source addition and maps the constant one to `S 0`.

The primary target is an actual HA proof:

```lean
theorem ordinary_decidable
    {ξ : Type*} {n : Nat} {φ : Semiformula ℒₒᵣ ξ n}
    (hφ : LO.FirstOrder.Arithmetic.DeltaZero φ)
    (bv : Fin n → SetTheory.PA.Term) (fv : ξ → SetTheory.PA.Term) :
  HA.Proves (HABoundedQuantifiers.dec (ordinaryAux bv fv φ))
```

For the proof, a motive allowing `Hierarchy Γ s φ` together with `s=0`
avoids inventing a new bounded induction principle. The positive-level
unbounded-quantifier and alternation constructors are eliminated by their
incompatible numerical index. At level zero the only remaining cases are
truth, falsity, positive/negative atoms, conjunction/disjunction and the
two bounded constructors. The result must be restricted to the actual
ordered-arithmetic language `ℒₒᵣ`; arbitrary source relation symbols do not
come with HA decisions.

Canonical wrappers may specialize the environments to source bound slots
`i ↦ var i.val` and free slots `j ↦ var(n+j)`, retaining all parameters.
For a source sentence, use the actual empty free environment. These wrappers
must not silently identify source and target binders by their printed names.
The generic environment theorem is the useful core; a new ad hoc bounded
PAHF syntax and a second induction over that syntax add no needed strength.

## Existing bound-removal API resolves the delicate condition

The source bounded constructors have a term **under** the new binder:

```text
t : Semiterm ℒₒᵣ ξ (n+1),   t.Positive.
```

`Semiterm.Positive` means every occurring bound-variable index is greater
than zero. It does not mean the interpreted term has positive numerical
value. In particular, a zero bound is allowed and the bound variable `#0`
itself is not allowed.

The existing exact theorem is:

```lean
LO.FirstOrder.Rew.positive_iff :
  t.Positive ↔ ∃ u : Semiterm L ξ n, t = Rew.bShift u
```

It is at `Foundation/Syntax/Predicate/Rew.lean:253`. After obtaining this
actual outer term `u`, the already checked
`FoundationPAHFSyntax.termAux_bShift` proves:

```text
termAux (liftBound bv) (liftFree fv) t
  = Term.rename Nat.succ (termAux bv fv u).
```

Thus the PAHF bound is exactly `termAux bv fv u`, independently of the
newly bound witness. No arbitrary-variable independence assumption, numerical
positivity premise, or new unshift operation is necessary. The existing
`positive_iff` proof uses metatheoretic finite choice in its function case;
reusing it may introduce the standard Lean `Classical.choice` dependency.
That is not a choice rule in `HA.Derives`.

## Literal bounded cases and HA proof route

Positive atoms use actual `HA.EqualityDecidable.eq_decidable` and
`FoundationHAOrderDecidable.lt_decidable`. Negative atoms use the finite
intuitionistic deduction `dec A → dec(neg A)`. Truth and falsity have direct
HA proofs. Conjunction/disjunction decisions use finite disjunction cases.
The previous bounded module's corresponding helpers are private; a new leaf
can contain a small local logical helper set rather than modifying the
frozen module or introducing a semantic decision oracle.

Source bounded existence is literally `∃(bound ∧ matrix)`. After the exact
bound identity above, its ordinary interpretation is definitionally the
accepted `HABoundedQuantifiers.bex` with the recursively interpreted matrix.
The induction hypothesis supplies an HA proof of the body's decision with
the lifted environments. `Relative.all_intro` with empty open context
supplies the required **object-language** uniform decision sentence, and
`bex_decidable` applies by modus ponens.

Source bounded universality is literally `∀(¬bound ∨ matrix)`, because its
classical implication is a negative-normal-form disjunction. Its ordinary
interpretation is therefore **not** definitionally `ball`, whose body is a
primitive PAHF implication. Prove the actual HA equivalence

```text
(¬L ∨ A) ↔ (L → A)
```

using the already proved decision of the actual order atom `L`. The forward
direction is intuitionistic without a decision premise. For the reverse,
split the genuine HA decision `L∨¬L`; in the positive branch apply the
implication, and in the negative branch keep that negation. Lift these actual
proofs under the universal binder with the complete shifted context. Transfer
decidability from accepted `ball` by the two HA implications. There is no
unrestricted replacement of classical disjunction by implication.

The anticipated first leaf is approximately 250–350 lines including syntax
identities, finite logical helpers, both guarded-all directions and the
actual `DeltaZero` structural proof; checks about 60–90 lines. If further
separation is useful, the ordinary interpreter/positive-bound identities can
freeze first. Neither phase needs new arithmetic axioms.

## Subsequent exact GG comparison, separately scoped

Once ordinary decidability is proved, a second useful source-bound target is:

```lean
theorem ordinary_gg_equivalence
    {ξ : Type*} {n : Nat} {φ : Semiformula ℒₒᵣ ξ n}
    (hφ : LO.FirstOrder.Arithmetic.DeltaZero φ)
    (bv : Fin n → SetTheory.PA.Term) (fv : ξ → SetTheory.PA.Term) :
  HA.Proves (.and
    (.imp (ordinaryAux bv fv φ)
      (FoundationPAHFSyntax.formulaAux bv fv φᴺ))
    (.imp (FoundationPAHFSyntax.formulaAux bv fv φᴺ)
      (ordinaryAux bv fv φ)))
```

Here `φᴺ` is **the existing Foundation definition**, not a newly copied GG
recursion. The proof is a normalization theorem for actual bounded source
formulas, not a new classical-to-intuitionistic translation algorithm.
Positive atoms use the proved equality/order stability; negative atoms have
one literal negation on both sides. Conjunction transports component proofs.
GG disjunction is `¬(¬φᴺ ∧ ¬ψᴺ)`; ordinary component decisions recover the
actual ordinary disjunction by finite cases. Universals use exact binder
congruence with shifted contexts.

For the bounded existential, GG is literally
`¬∀¬(doubleNeg L ∧ φᴺ)`. Normalize the decidable order atom and the bounded
body using proved HA implications. Pure intuitionistic quantifier reasoning
then identifies this with the double negation of the **bounded** existential.
Its previously proved HA decision permits DNE for that formula. This step
must cite bounded-existential decidability; applying DNE to an arbitrary
unbounded existential would instead require an unjustified principle.
For bounded universals retain the literal encoded disjunction and use the
guarded-all equivalence above, rather than assuming GG preserves source
implication definitionally. No general Markov principle occurs.

An immediate corollary could give actual HA decidability of `formulaAux bv fv
φᴺ` under `DeltaZero φ`. Proving only that corollary would avoid an ordinary
interpretation, but would not supply the useful plain-source/GG comparison.
The two-phase recommendation gives an explicit source-bound intermediate
checkpoint and avoids a redundant bespoke bounded grammar.

## Cache and source pins

The read-only [cache audit](ha-foundation-deltazero-bridge-cache-audit.json)
has SHA `3f82fcb5d2a0e57e056fbc22b9c10ee27018524a8cb74944c1a56efd8b34a29b`.
It rehashed all 607 existing bounded-packet pins and the selected source/
object records. The proposed first import closure is **101 cached modules,
76 Foundation modules, 329 cached artifacts and 34 explicit external
boundaries**. This is the bounded-packet's 100-module closure plus its frozen
fresh main. Its independent root acceptance was still pending when this
audit was generated; use the accepted root primary once published. No object
was copied, no Lean process ran, and no Foundation source was rebuilt.

Important primary-source pins and anchors:

| Source | Anchor | SHA-256 |
|---|---|---|
| `Foundation/.../Arithmetic/Basic/Hierarchy.lean` | `Hierarchy:10`, `DeltaZero:28`, `ballLT_iff:211` | `c9ac3be94e6691675ae3d37ed2d9e6a03abc0cd22a970db321ee447ea3eb14bf` |
| `Foundation/Syntax/Predicate/Term.lean` | `Positive:129` | `18cf80e4614ea6048e4b277fd99b1f662a5330ae6d7853f57f6f4ce4d3a0601a` |
| `Foundation/Syntax/Predicate/Rew.lean` | `positive_iff:253` | `61d0551a3e119cf48cb840516751c9da917b11a7da56c064ccfa37e772ca5edc` |
| `Foundation/.../Basic/Syntax/Formula.lean` | `imp_eq:129`, `ball_eq:133` | `5cbd864cc34c4b18824757fb2112f9b21f6281b53f6ee434ff326214b2e2b341` |
| `Foundation/.../NegationTranslation/GoedelGentzen.lean` | `doubleNegation:11`, bounded proof uses its literal constructors | `52fabd00a01e1f5671e1f078c36f9848f2e219e0a4e616deaad4e523057586ea` |
| `FoundationPAHFSyntax.lean` | `termAux:20`, `formulaAux:40`, `termAux_bShift:111` | `6ef6d070feed7382fe5e90fbb1edf9dba41aae33e3ca65b049c16a1b015ede35` |
| `HABoundedQuantifiers.lean` | exact bounded definitions and actual induction | `43b5a74f24985cf6c3232504f074eab315b39edda0aa688af9cc3a76e006fe21` |

## Boundary to the actual consistency checker

These proposed theorems require a proof of the actual syntactic predicate
`DeltaZero φ`. A `𝚫₁` representation, classical normal-form equivalence or
model `ProperOn` theorem is not that proof. The actual Foundation `proof T`
uses a delta-one pair with existential graph witnesses and the derivation
fixed point; `provable T` adds an unbounded proof-code existential. The
actual checker must first be bound to a suitable explicit bounded matrix
with genuine HA comparison proofs and the exact auxiliary witness behavior.

Nothing here proves that original proof predicate is literally delta-zero,
supplies positive Σ1 DNE, normalizes the ordinary consistency checker in HA,
or discharges the required PA/current-equation equivalence. The source
hierarchy/GG bridge is a concrete next component, not the final calibration.
