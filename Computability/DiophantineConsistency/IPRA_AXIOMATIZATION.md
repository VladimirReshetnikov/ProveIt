# The intuitionistic PRA candidate used in the proof

The final target is a derivation in the explicitly defined candidate
`IPRANativeTheory.nativeTheory`, not merely a derivation in classical PRA or
in Heyting arithmetic. Its exact definition is in
[`IPRANativeTheory.lean`](Lean/DiophantineConsistency/IPRANativeTheory.lean),
with its induction syntax in
[`IPRANativeInduction.lean`](Lean/DiophantineConsistency/IPRANativeInduction.lean).
This document describes those definitions. The exact equation endpoint and
its remaining replay qualifications are described below.

## Logic and language

The object proof system is Foundation's intuitionistic first-order Hilbert
calculus `Int¹`. Its language has equality and strict order as relation symbols.
For every finite construction code there is a function symbol. Codes are built
from zero functions of each arity, successor, projections, composition, and
primitive recursion. Two different codes give different symbols even when
they denote the same function on the natural numbers. The code construction is
defined in [`PRAFiniteFunctionCodes.lean`](Lean/DiophantineConsistency/PRAFiniteFunctionCodes.lean).
Addition, multiplication and one are designated codes, not separate primitive
axioms. Variables range over the arithmetic domain.

For an independent comparison, [Moschovakis's account of intuitionistic
PRA₀](https://www.math.ucla.edu/~joan/techgothenburghandout.pdf) describes
primitive-recursive function symbols, intuitionistic logic and quantifier-free
induction, and discusses the corresponding first-order formulation. For an
explicit intensional construction of function symbols, [Aehlig's arithmetic
language](https://www.linta.de/~aehlig/university/pub/04-jsl.pdf) uses zero,
successor, projections, composition and primitive recursion; the surrounding
system in that paper is classical, so it supplies a language presentation,
not the intuitionistic logic. These references motivate a comparison target;
they do not themselves prove that the Lean theories are equivalent.

## Nonlogical axiom schemes

All displayed free variables are universally closed; parameters in the schemes
are arbitrary finite lists.

1. Equality: `x = x`, and the full Leibniz substitution scheme
   `x = y → (φ(x, p̄) → φ(y, p̄))` for **every intuitionistic formula** `φ`,
   including formulas with quantifiers. This yields equality congruence for
   functions and relations.
2. Function definitions: every zero code returns zero; every projection code
   returns its selected argument; each composition code equals its defining
   composition. For each primitive-recursion code `h = prec(f,g)`, include
   `h(0, p̄) = f(p̄)` and
   `h(S(n), p̄) = g(n, h(n,p̄), p̄)`.
3. Successor and order: `S(x) ≠ 0`, `S(x) = S(y) → x = y`, and
   `x < y ↔ ltBit(x,y) = 1`, with `ltBit` the particular constructed PR
   code that tests whether truncated `y − x` is nonzero.
4. Induction: for each quantifier-free intuitionistic formula `φ(n,p̄)` in the
   full code language, include

   `∀ p̄ [φ(0,p̄) → (∀ n (φ(n,p̄) → φ(n + 1,p̄))) → ∀ n φ(n,p̄)]`.

   A quantifier-free formula is built from falsity and relation atoms using
   conjunction, disjunction and implication. Negation is implication to
   falsity. Bounded quantifiers written as quantifiers are not quantifier-free.
   The step `n + 1` uses the designated addition and one codes: it is not
   syntactically identical to `S(n)`. The candidate proves their equality;
   [`IPRASuccessorInduction.lean`](Lean/DiophantineConsistency/IPRASuccessorInduction.lean)
   uses it to derive the usual `S(n)` quantifier-free induction schema with
   arbitrary finite parameters. Conversely,
   [`IPRASuccessorInductionConverse.lean`](Lean/DiophantineConsistency/IPRASuccessorInductionConverse.lean)
   derives each `n + 1` instance from the corresponding `S(n)` instance in
   any intuitionistic theory proving the stated defining and equality schemes;
   it derives `n + 1 = S(n)` there without induction.
   [`IPRASuccessorTheoryEquivalence.lean`](Lean/DiophantineConsistency/IPRASuccessorTheoryEquivalence.lean)
   goes further: it defines the same theory with successor-step induction
   and proves that the two explicit theories have the same derivable
   sentences. This is not a comparison with every textbook presentation.

There is no unrestricted induction scheme, general excluded middle, or Markov
principle among these axioms. In particular, classical negation-normal
`¬A ∨ B` cannot simply be substituted for the intuitionistic implication
`A → B` in the induction scheme.

## What has and has not been established

The classical intermediate `PRATheory.PRA` is described in
[`PRA_AXIOMATIZATION.md`](PRA_AXIOMATIZATION.md). A Lean theorem
[`IPRAFullGGTransfer.from_classical`](Lean/DiophantineConsistency/IPRAFullGGTransfer.lean)
transfers each derivation in that particular classical presentation to a
native-candidate derivation of its Gödel–Gentzen translation. It does not by
itself identify the translated consistency sentence with the intended native
consistency sentence. The later theorem
[`IPRACurrentNativeZFC.equivalence14`](Lean/DiophantineConsistency/IPRACurrentNativeZFC.lean)
states the literal 14-variable equivalence in this native theory. A
[73-module project-origin repair](reviews/ipra-frozen-repair-v2-verification/README.md)
rebuilt the two previously mismatched dependency users and passed matching
fixed-snapshot replays. The 14-variable endpoint was then rebuilt on that
repaired parent; its [independent comparison](reviews/ipra-current-native14-repaired-verification-peer/README.md)
matched all six rows and both complete log sets. The endpoint runs each recorded
ten workspace-source drifts, so this is not a source-current result. The
848-module ancestor remains author-only, and package-transitive and dynamically
loaded ancestry remain inherited. Newer source surveys and partial successor
replays are documented in the [proof plan](IPRA_PROVABILITY_PLAN.md); a fully
authenticated current-source closure remains open. The endpoint uses the native negation of
Foundation's particular arithmetized ZFC refutation predicate, not an
unverified identification with every possible proof coding. A Lean-checked
comparison with any broader independently specified standard presentation of
intuitionistic PRA also remains open; see
[`IPRA_PROVABILITY_PLAN.md`](IPRA_PROVABILITY_PLAN.md).

The newly added [`IPRAStandardTheory.lean`](Lean/DiophantineConsistency/IPRAStandardTheory.lean)
states a same-language provability equivalence between the native candidate
and a presentation with atomic equality replacement and successor-step open
induction. The two presentations share the primitive-recursive defining and
basic axiom schemes, including the defined order relation. A direct AQ29 client
and its selected-consistency composition have completed one [author-only
extension and independent artifact audit](research/ipra-standard-aq29/README.md).
The parent pair and a second Lean replay remain open, with historical-source
and provider qualifications. For the 14-variable equation,
[`IPRAStandardCurrentEndpoint.ipra_current_iff_consistency`](Lean/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean)
states the equivalence in `standardTheory` itself; its author build from the
Lean sources of `66da84a9e7` reports only Lean's standard axioms (see the
[checks](Lean/DiophantineConsistency/IPRAStandardCurrentEndpointChecks.lean)).
A separate [16-module author-only extension](reviews/ipra-standard-current14-author-trial/README.md)
over the fresh AQ29 author provider completed with exit 0 and passed an
[independent artifact audit](reviews/ipra-standard-current14-author-independent-audit/README.md).
It uses a historical hybrid of source versions; neither a paired Lean replay
nor identification of that hybrid literal with the current PDF is established
by this audit. The parent/provider limitations above remain.
The distinct equality-only comparison described below remains open.

For this selected coding, `rho` is Foundation's arithmetized provability
predicate for falsity from ZFC and its retained classical source consistency
sentence is definitionally `¬rho` in
[`FoundationHAConsistencyNormalization.lean`](Lean/DiophantineConsistency/FoundationHAConsistencyNormalization.lean).
The candidate [`IPRABoundedRhoZFC.zfcEquiv`](Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean)
states an internal native-theory derivation comparing the Gödel–Gentzen
translation of the mapped Foundation consistency sentence with the native
negation of the native NNF reading of the mapped refutation predicate. It is a
comparison for this specific source sentence, not a general theorem identifying
every alternative proof coding. It shares the coherent-replay qualifications above.

The historical package provider has since become partly unavailable, and one
freshly rebuilt Foundation object differs from its recorded historical hash.
The [mixed-provider experiment](reviews/lean-mixed-provider-counterexample/README.md)
demonstrates why successful Lean compilation, direct-import guards and clean
axiom reports do not establish compatibility with older transitive objects.
A coherent rebuild or verification of historical compile-time inputs is
needed; the experiment does not show an inconsistency in this project.

A Lean theorem asserting `nativeTheory ⊢ ψ` is a metatheoretic assertion that
an object-theory derivation exists. Principles used by Lean in that
metatheoretic proof do not become additional object-theory axioms.

One concrete remaining comparison is an independently specified first-order
intuitionistic theory in the constructor-code language with equality alone and
successor-step open induction. A translation can erase each `<` atom into the
candidate's comparison-code equation. Proving that translation preserves
quantifier-freeness, transfers every axiom and derivation in both directions,
and maps the particular consistency sentence is still required. Distinct
construction codes must not silently be identified just because they compute
the same standard function.
