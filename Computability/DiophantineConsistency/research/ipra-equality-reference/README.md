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

The missing comparison includes at least: prove erasure commutes with
substitution and quantifier binding; transfer intuitionistic logical
derivations and all nonlogical axioms to the equality-only theory; derive
successor injectivity from the predecessor code; transfer the reference axioms
to the native candidate; and prove every native formula equivalent there to
its embedded erasure. The two theories live in different languages, so the
target comparison must explicitly translate the formula. The previously
proved same-language successor-step versus `n+1` induction comparison does
not by itself discharge this language or proof-transport work. Applying the
comparison to the equation also requires checking the translated consistency
predicate and the positive-shift no-zero formula.
