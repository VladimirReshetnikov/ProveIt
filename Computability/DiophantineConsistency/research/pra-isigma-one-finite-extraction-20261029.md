# Finite induction instances in Foundation IΣ₁ proofs

The maintained 14-variable equation already has a separate HA proof-existence result. This note concerns the additional candidate-PRA comparison and its possible use for a smaller equation; it is not needed to qualify that HA result.

`PRAISigmaOneFiniteTranslation.finite_translation` is a Lean theorem, rebuilt on the post-merge provider. Given an actual `p : Theory.Proof 𝗜𝚺₁ σ`, it produces a finite list `Φ` of Foundation arithmetic formulas satisfying `Hierarchy 𝚺 1` and an actual proof of the mapped conclusion in candidate PRA extended by precisely the mapped closed successor-induction instances in `Φ`. It uses the finite axiom list carried by `p`, `ParsonsTheoryNormalize.partition`, the proved PA-minus interpretation, and equality-model completeness. It does not replace a Σ₁ formula by a prenex equivalent. The 49-module post-merge dependency build and two independent replays have passed; see the [replay packet](../reviews/pra-after-prenex-merge-refresh-author-replay/README.md).

The independently replayed `PRAPairedFiniteInduction.PRA_proves_goal_of_finite_boundedSuccInd` eliminates an arbitrary finite list of closed successor-induction instances whose predicates have the form `∃y ψ(x,y,c)` with `ψ` bounded and no additional free predicate parameters, when the conclusion is a universally closed open existential. It uses a recursively nested bounded pair graph, not an assumed primitive-recursive pairing function code. Its post-merge graph is included in that independently replayed 49-module chain.

At that checkpoint, the gap between these two theorems was substantial. Foundation's `Hierarchy 𝚺 1` allows bounded universal quantification over Σ₁ formulas, so its formulas need not have a literal single-existential bounded matrix. For instance, rearranging `∀t<b ∃y D(t,y)` into one bounded-matrix existential needs a finite collection/coding argument under a theory strong enough to prove the equivalence. `ParsonsGuardedCollection.guarded_bounded` is an extended Parsons-rule proof transformer, not an established candidate-PRA collection principle or object-theory normalization equivalence. The later strict-prefix route described below addresses this gap without assuming collection in candidate PRA.

The former parameter gap is now handled by the checked finite multi-parameter induction elimination used in the later comparison. Its goal is still a universally closed open existential; applying it to the actual consistency/equation equivalence requires a checked reduction of that precise goal to the supported form.

An alternative route worth retaining is the cut-free proof of Parsons' theorem
in [Joosten, *Two Proofs of Parsons' Theorem*, §2](https://www.phil.uu.nl/ozsl/articles/joosten01.pdf).
It first moves from induction axioms to an induction-rule calculus and then
uses Herbrand witnessing and primitive recursion to interpret the rule. The
repository's strict-fragment Parsons and witnessing developments cover only
parts of that route; neither the unrestricted cut-free reduction nor its full
translation to candidate PRA is established here. The paper is external
mathematical guidance, not a Lean certificate or a substitute for the missing
normalization.

A warning against assuming full Σ₁ collection in a PRA-like base appears in
[Khaniki, *Not all Kripke models of HA are locally PA*, Theorem 3.11](https://iuuk.mff.cuni.cz/~koucky/EPAC/papers/HA_Final.pdf):
the paper cites a model of true Π₂ arithmetic that fails its BΣ₁ scheme in a
primitive-recursive-function language. Adapting that model to this exact
candidate presentation is not formalized here. Moreover, the cited failed
scheme has Σ₁ matrices; it does not by itself prove failure of the narrower
bounded-matrix collection instance needed for a proposed normalizer.

A potentially relevant contraction appears in [Patey, *Lowness avoidance*, §7.2](https://www.ludovicpatey.com/lowness-avoidance/lowness-avoidance.pdf). Definition 7.2.6 defines `BΓ` by bounding existential witnesses for each matrix in `Γ`; Exercise 7.2.7 states over `Q + IΔ⁰₀` the equivalence `BΣ⁰_{n+1} ↔ BΠ⁰_n` without a displayed `n ≥ 1` restriction. The following Proposition 7.2.8 explicitly fixes `n ≥ 1`. At `n = 0`, the exercise therefore appears to connect standard `BΣ₁` to bounded-matrix collection. Before combining it with the cited Khaniki countermodel for this candidate, one must match the notions of formula class and collection, verify the pairing/coding and language expansion or reduct, and check the model transfer. Those bridges and an independence theorem have not been formalized in Lean.

A later route uses the upstream `StrictSigmaOneInduction.isigma1_provable` proof, which derives arbitrary Foundation IΣ₁ theorems in a theory with strict existential-prefix induction. `PRAPositiveStrictCertificate.positive_certificate` supplies a candidate-side bounded-induction certificate for every positive predicate, including every strict prefix and the case of zero free parameters. `PRAISigmaOneOpenComparison.comparison` combines the two with finite-instance extraction and elimination, conditional on an actual candidate-PRA implication from the mapped source theorem to the chosen universally closed open-existential goal. Its [60-module dependency graph](../reviews/pra-isigma-final-merge-refresh-author-replay/README.md) passed the author build and two independent replays; Foundation and Mathlib are inherited. The separate `PRAISigmaOnePiOneComparison.comparison` provisionally specializes this to an equivalence of two unary open-matrix Π₁ sentences, again requiring that mapped-source implication. The exact equation/consistency implication remains open, and comparison with a standard PRA presentation is also required.

For the literal maintained equation, the no-zero side is an actual finite universal closure of an arithmetic disequality; the provisional `PRANoZeroUnary.noZero_unary_open` handles that general shape, and `PRACurrentNoZeroUnary` instantiates it using a historical HA-current provider whose full source closure still needs authentication. The consistency side needs separate work: Foundation's exact `sourceSentence` is `∼provabilityPred T ⊥`, and its `proof T` predicate is a Δ₁-defined proof relation rather than a syntactically open matrix. The existing C222 checker equivalence is established in IΣ₁ models, while the history/value semantics in that route are also stated under IΣ₁. Neither a Π₁ hierarchy certificate nor that IΣ₁-model equivalence alone provides an equivalence in every candidate-PRA model with a unary open PR-code predicate.
