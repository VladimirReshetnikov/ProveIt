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

The missing comparison includes at least: coherently rebuild and independently
replay the erasure/rewriting statements; transfer intuitionistic logical
derivations and all nonlogical axioms to the equality-only theory; derive
successor injectivity from the predecessor code; transfer the reference axioms
to the native candidate; and prove every native formula equivalent there to
its embedded erasure. The two theories live in different languages, so the
target comparison must explicitly translate the formula. The previously
proved same-language successor-step versus `n+1` induction comparison does
not by itself discharge this language or proof-transport work. Applying the
comparison to the equation also requires checking the translated consistency
predicate and the positive-shift no-zero formula.
