# Equality-only intuitionistic PRA reference: exploratory syntax

The proposed independently specified first-order reference theory is in
[`IPRAEqualityOnlyReference.lean`](../../Lean/DiophantineConsistency/IPRAEqualityOnlyReference.lean).
It has one equality predicate, finite primitive-recursive construction codes
as function symbols, universally closed defining equations, successor
nonzero, full intuitionistic Leibniz equality and parameterized successor-step
quantifier-free induction. It deliberately does not postulate successor
injectivity or a less-than predicate. Distinct codes remain distinct even when
their standard functions coincide.

This makes precise a choice compatible in broad outline with Joan
Moschovakis's [intuitionistic PRA₀ and its first-order quantifier extension](https://www.math.ucla.edu/~joan/techgothenburghandout.pdf),
and with the constructor-based primitive-recursive function syntax in Klaus
Aehlig's [Definitions 2.1–2.2](https://www.linta.de/~aehlig/university/pub/04-jsl.pdf).
Aehlig's surrounding theory is classical; the proposed reference instead uses
intuitionistic first-order logic. Neither citation supplies the exact Lean
axiomatization or proves that it is equivalent to the native candidate.

[`IPRAOrderErasure.lean`](../../Lean/DiophantineConsistency/IPRAOrderErasure.lean)
defines the equality-language embedding, erases native `<` atoms to the
comparison-code equation, and contains syntactic statements for preservation
of quantifier-freeness and erasure after embedding. These files have had only
preliminary syntax invocations using a **mixed historical project / fresh
Foundation provider**. That environment is not an authenticated proof
provider; the [mixed-provider counterexample](../../reviews/lean-mixed-provider-counterexample/README.md)
shows why even a successful invocation does not validate these statements.
A coherent build and independent replay remain required.

The exploratory [`IPRAOrderErasureRew.lean`](../../Lean/DiophantineConsistency/IPRAOrderErasureRew.lean)
adds statements that term erasure commutes with rewriting, that the translated
rewriting commutes with passing under a quantifier, and that formula erasure
commutes with capture-avoiding rewriting. It has likewise only been invoked
in the mixed-provider exploratory environment; these are not yet authenticated
Lean proof results.

The exploratory [`IPRAReferenceImages.lean`](../../Lean/DiophantineConsistency/IPRAReferenceImages.lean)
contains candidate syntactic image statements for all five primitive-recursive
defining-equation schemes, culminating in `defining_images`. This establishes
neither the other reference-axiom images nor derivation transport, and its
only invocation likewise used the untrusted mixed provider.

The exploratory [`IPRAReferenceRew.lean`](../../Lean/DiophantineConsistency/IPRAReferenceRew.lean)
and [`IPRAReferenceEqualityImages.lean`](../../Lean/DiophantineConsistency/IPRAReferenceEqualityImages.lean)
add candidate embedding-rewriting compatibility, open-formula preservation,
full Leibniz equality images and the successor-nonzero image. Their only
invocations also used the untrusted mixed provider; the induction image and
logical proof transport are not established by these files.

The exploratory [`IPRAReferenceInductionImage.lean`](../../Lean/DiophantineConsistency/IPRAReferenceInductionImage.lean)
contains a syntactic comparison of the reference induction formula with the
corresponding native-language successor-step formula. Its syntax has only
been checked in the mixed provider. The separate
[`IPRAReferenceInductionTransfer.lean`](draft/IPRAReferenceInductionTransfer.lean)
is an **uncompiled draft** attempting to apply the existing native successor
induction derivation; no induction-axiom image is claimed from it.

The exploratory [`IPRAReferenceHilbert.lean`](../../Lean/DiophantineConsistency/IPRAReferenceHilbert.lean)
and [`IPRAReferenceTheoryTransfer.lean`](../../Lean/DiophantineConsistency/IPRAReferenceTheoryTransfer.lean)
contain a candidate embedding of intuitionistic Hilbert proof trees and a
finite-theory derivation transport **conditional on all reference axiom images**.
They have only been invoked with the same untrusted mixed provider. They do
not discharge the axiom-image premise or establish either theory equivalence
or an equation endpoint.

The exploratory [`IPRAOrderErasureHilbert.lean`](../../Lean/DiophantineConsistency/IPRAOrderErasureHilbert.lean)
and [`IPRAOrderErasureTheoryTransfer.lean`](../../Lean/DiophantineConsistency/IPRAOrderErasureTheoryTransfer.lean)
now contain the opposite native-to-reference transport **conditional on every
native axiom erasing to a reference-theory theorem**. They, too, have only
been invoked under the untrusted mixed provider; their axiom-image premise,
coherent replay and application to the equation remain open.

The exploratory [`IPRAErasedDefiningImages.lean`](../../Lean/DiophantineConsistency/IPRAErasedDefiningImages.lean)
and [`IPRAErasedEqualityImages.lean`](../../Lean/DiophantineConsistency/IPRAErasedEqualityImages.lean)
contain candidate erasure images for all primitive-recursive defining
equations, full Leibniz equality and successor nonzero. Their only invocations
also used the untrusted mixed provider. Native successor injectivity and
native induction remain separate obligations.

The exploratory [`IPRAErasedOrderImage.lean`](../../Lean/DiophantineConsistency/IPRAErasedOrderImage.lean)
maps the native order definition to the universal closure of `p ↔ p` and
contains a candidate intuitionistic reference-theory derivation by identity
and generalization. Its only invocation likewise used the mixed provider;
the successful invocation is syntax feedback, not proof authentication.

The exploratory [`IPRAErasedInductionShape.lean`](../../Lean/DiophantineConsistency/IPRAErasedInductionShape.lean)
expresses the erased native induction schema in the equality-only language,
still using the `x+1` step. The remaining induction obligation is a
reference-theory derivation of that schema from successor-step induction;
the syntactic statement does not establish the derivation. Its invocation
also used the untrusted mixed provider.

The exploratory [`IPRAErasedSuccessorShape.lean`](../../Lean/DiophantineConsistency/IPRAErasedSuccessorShape.lean)
gives the equality-only syntax of erased successor injectivity. It does not
derive injectivity. [`IPRAErasedRemainingObligations.lean`](../../Lean/DiophantineConsistency/IPRAErasedRemainingObligations.lean)
assembles the available erasure branches and makes the transport conditional
on precisely two remaining proof obligations: the reference proof of
successor injectivity and reference proofs of all erased native `x+1`
induction instances. Both files have only been invoked with the untrusted
mixed provider and require coherent replay. Their conditional transfer is
not an established theory equivalence or an equation endpoint.

The exploratory [`IPRAReferenceCloseFamily.lean`](../../Lean/DiophantineConsistency/IPRAReferenceCloseFamily.lean),
[`IPRAReferenceEqualityTools.lean`](../../Lean/DiophantineConsistency/IPRAReferenceEqualityTools.lean), and
[`IPRAReferencePredecessor.lean`](../../Lean/DiophantineConsistency/IPRAReferencePredecessor.lean)
draft uniform closure, Leibniz instantiation, and the derivation of successor
injectivity from predecessor recursion and projection. The related
[`IPRAErasedInductionObligation.lean`](../../Lean/DiophantineConsistency/IPRAErasedInductionObligation.lean)
assembles a native-to-reference transfer conditional only on derivability of
the erased `x+1` induction instances. These are candidate source proofs,
invoked only with the untrusted mixed provider; they need a coherent replay.
In particular the induction-image premise remains open, and neither theory
equivalence nor the equation endpoint follows from this conditional result.

[`IPRAReferenceAddOne.lean`](../../Lean/DiophantineConsistency/IPRAReferenceAddOne.lean)
drafts the equality-only derivation of `x + 1 = S x` by translating an
existing finite native proof and the specific defining and equality axioms it
uses. It does not assume native induction, but is still only mixed-provider
syntax-checked. The derivation must be coherently replayed and used to convert
reference successor-step induction to the erased addition-step schema.

[`IPRAReferenceAddOneOpen.lean`](../../Lean/DiophantineConsistency/IPRAReferenceAddOneOpen.lean)
and [`IPRAReferenceInductionConversion.lean`](../../Lean/DiophantineConsistency/IPRAReferenceInductionConversion.lean)
draft that conversion and assemble `nativeToReference`, a native-to-reference
provability transfer with no remaining explicit axiom-image hypothesis. The
only Lean invocation so far used the **untrusted mixed provider**, so this is
candidate source, not an authenticated Lean result. In particular, coherent
replay is essential, and applying the transfer still requires identifying
the erased endpoint, including its consistency predicate, with the intended
reference-language formulas. This direction alone is not a two-way theory
equivalence.

The exact candidate statement is
`∀ {σ : Sentenceᵢ PRALanguage.language}, nativeTheory ⊢ σ → referenceTheory ⊢ erase σ`.
The mixed-provider diagnostic invocation of
[`IPRAReferenceConversionChecks.lean`](../../Lean/DiophantineConsistency/IPRAReferenceConversionChecks.lean)
exited 0 and reported `propext`, `Classical.choice`, and `Quot.sound` for the
conversion and transfer, with no reported `sorryAx`. Those diagnostics do
not repair the mixed-provider boundary: the known counterexample shows that
successful checks and benign axiom reports can still be unsound in this setup.

[`IPRAReferenceAQ29.lean`](draft/IPRAReferenceAQ29.lean) is an **uncompiled
draft** applying this candidate transport to the fixed AQ29 endpoint. It
states the no-zero formula and the negated mapped refutation explicitly under
erasure; identifying that erased refutation with a separately specified
reference-language consistency predicate remains open. The first exploratory
mixed-provider invocation exited 1 because the AQ29 object was absent from the
temporary overlay. After adding available historical AQ29 objects to that
overlay, a second invocation was bounded to 45 seconds and exited 124 without
an elaboration result. Neither invocation validates the draft; no further
heavy mixed-provider probe is justified while the coherent rebuild is active.

The missing comparison includes at least: coherently rebuild and independently
replay the erasure/rewriting statements and candidate derivations; discharge the
native induction image; transfer the reference axioms
to the native candidate; and prove every native formula equivalent there to
its embedded erasure. The two theories live in different languages, so the
target comparison must explicitly translate the formula. The previously
proved same-language successor-step versus `n+1` induction comparison does
not by itself discharge this language or proof-transport work. Applying the
comparison to the equation also requires checking the translated consistency
predicate and the positive-shift no-zero formula.
