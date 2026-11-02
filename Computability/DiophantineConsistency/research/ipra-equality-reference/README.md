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

More precisely, the existing source defines `ρ` as Foundation's
`provabilityPred` for `ZermeloFraenkelChoice` and falsity, and defines the
source consistency sentence as `∼ρ`. The native endpoint uses the separate
formula `∼native (lMap embedding ρ)`, and the draft reference endpoint uses
its equality-only erasure. These definitions identify the concrete coding
being transported; they do not by themselves prove that a separately chosen
reference-language ZFC proof predicate is intuitionistically equivalent to it.

[`IPRAReferenceRefutationReading.lean`](draft/IPRAReferenceRefutationReading.lean)
is an uncompiled draft of a direct equality-only reading of Foundation's
arithmetic NNF syntax: equality remains equality; `<` is the PR comparison
bit equal to one; negative atoms become intuitionistic negations; and the
positive logical constructors are preserved. Its proposed general syntactic
identity specializes to the **same** Foundation ZFC refutation predicate ρ.
This is a concrete candidate for identifying the transported formula with an
independently defined syntax reader, not a comparison with all alternative
proof codings, nor yet an elaborated or coherently checked Lean result.

For the **selected Foundation coding**, the native source already contains a
candidate internal comparison: `IPRABoundedRhoZFC.zfcEquiv` is a native-theory
proof object comparing the GG translation of mapped Foundation `Con(ZFC)` to
the negated mapped native reading of `rho`. The uncompiled
[`IPRAReferenceSourceConsistency.lean`](draft/IPRAReferenceSourceConsistency.lean)
draft proposes transporting that exact comparison to the equality-only
reference theory, and [`IPRAReferenceAQ29Source.lean`](draft/IPRAReferenceAQ29Source.lean)
proposes composing it with the AQ29 endpoint. Thus this identification does
not require a theorem comparing every possible proof coding. The source
comparison, its transfer and the endpoint all still require coherent replay;
the target is the **erased GG reading** of Foundation's classical sentence,
not a claim that an unmodified classical formula is an intuitionistic one.
The proposed reference replay wrapper and task policy now include these two
drafts. The updated source closure and policy still require independent
review and a guarded replay; neither draft has been elaborated.

The separate `ValidatorConsistency222.iSigma1_proves_con_ZFC_iff_222` is a
classical `IΣ₁` derivability statement built using the two-way comparison in
all `IΣ₁` models and completeness. The
`FoundationZFCConsistencyNat.source_nat_iff_no_refutation` comparison with
the project's `BProv` is a standard-natural semantic statement. Neither
alone should be presented as an already established ordinary
equality-reference-theory proof comparing arbitrary checker codings. An
internal comparison to a *separately specified* reference-language checker
would need its own precise formula and a proof of the appropriate translated
or native equivalence.

[`IPRAReferenceAQ29Direct.lean`](draft/IPRAReferenceAQ29Direct.lean) is an
uncompiled assembly of the three preceding drafts. Its proposed theorem has
type `referenceTheory ⊢ noZero AQ29 🡘 ∼refutation`, where `noZero` is the
explicit equality-only formula for the fixed positive-shift expression and
`refutation` is the direct reader applied to Foundation's same ρ. The files
are kept in the research draft directory, so their imports must be made
available before any future Lean replay. No elaboration, alternative-coding
equivalence, or equation proof verification is claimed.

[`IPRAReferenceNoZero.lean`](draft/IPRAReferenceNoZero.lean) is another
uncompiled source draft spelling out the equality-only no-zero formula from
the positive-shift expression's two natural-polynomial sides and proposing
its syntactic identification with erased `nativeNoZero`. It is intended to
make the equation side of the endpoint explicit; it has not been elaborated
or checked and says nothing about the independent consistency encoding.

[`IPRAReferenceRoundtrip.lean`](draft/IPRAReferenceRoundtrip.lean) is an
uncompiled outline for a metatheoretic comparison on equality-only sentences:
`nativeTheory ⊢ embed σ ↔ referenceTheory ⊢ σ`. It assembles the earlier
conditional reverse transfer and candidate induction-image wrapper with the
candidate forward transfer and syntactic erasure-after-embedding identity.
The induction wrapper itself remains uncompiled. Even if checked, that
sentence-level provability comparison would not alone identify an arbitrary
native formula with its embedded erasure, identify the consistency encoding,
or validate the equation endpoint.

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

## Coherent root-workspace build (2026-11-01)

The native-to-reference chain above, from `IPRAEqualityOnlyReference` through
`IPRAReferenceInductionConversion` and `IPRAReferenceConversionChecks`
(19 modules), built from source with Lake's ordinary trace-checked build in
the root workspace, at the Lean sources of `9cd427e8da`. This was not the
mixed-provider environment. `nativeToReference` reports only `propext`,
`Classical.choice` and `Quot.sound`. The 14-variable client
[`IPRAReferenceCurrentEndpoint`](../../Lean/DiophantineConsistency/IPRAReferenceCurrentEndpoint.lean)
built on top of it, and its two theorems report the same three axioms. This is
an author build only; an independent replay packet has not been made. The
reverse transport and the formula-wise native/erasure comparison remain open,
as listed in the preceding paragraph.
