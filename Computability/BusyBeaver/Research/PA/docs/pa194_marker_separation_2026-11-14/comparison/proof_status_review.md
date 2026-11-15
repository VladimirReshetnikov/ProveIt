# Proof-status review

## Three different claims must be kept apart

1. **Literal construction and finite/symbolic certificate.** A 388-row table, startup trace, and universal source-instruction contracts establish the displayed low-level simulation only to the extent that the checker rules are justified. A concrete blank run never establishes nonhalting or a consistency equivalence.
2. **Written weak-arithmetic mathematical theorem.** A paper may give primitive-recursive witness constructions with quantifier-free induction, or an IΣ1 argument followed by the repository's conservation/negative-translation transfer. This is a mathematical claim independent of whether Lean has formalized it.
3. **Completed proof-assistant endpoint.** The repository README explicitly states that neither physical-machine-specific iPRA direction has yet been established in the Lean development. It documents extensive intermediate results. This is not by itself a refutation of a later complete paper proof.

The primary PA194 packet gives an ordinary PA-formalizable calibration, not automatically an iPRA calibration. The later revised `pa194_ax11h_research_2026-11-14_2` packet explicitly claims a complete **written** iPRA theorem for PA194AX11H and PA194QAX11H. It supplies detailed additional manuscripts: `physical_ipra_audit.tex`, `source_command_completion.tex`, `consistency_implies_nonhalting.tex`, `term_leaf_completion.tex`, `forward_calibration_completion.tex`, `foundation_paeq_completion.tex`, and `consistency_equivalence.tex`. Current incoming packets explicitly cite this revised calibration, often retaining the exact ZIP with SHA-256 `93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.

## Substantive content of the revised mathematical calibration

The physical note encodes finite-support tapes by two binary integers and interprets every symbolic run/list rule in iPRA. Arbitrary spare lists are represented by a length, base, and digit word; slot 12 of the affine clock must be the width of that very same list. It supplies primitive-recursive clocks and a frame invariant, not merely an argument that each individual standard macro terminates. Its reverse halt implication uses the decidable source halt flag and the conditional bound `source still live at k -> τ(k) >= 3k`; it therefore handles zero durations after halt without assuming an invalid unconditional cofinality assertion.

The forward-calibration manuscript replaces full-PA inductions over all environments by finite demand trees of explicit requests, evaluated backwards. Same-stratum recursive requests strictly decrease a source rank, while other requests enter an already completed stratum. Proof-producing operations are direct finite lists; the paper does not simply cite an upstream full-PA theorem as if it were a weak-base theorem. It also replaces the equality-vacuity interface at its actual consumers, retains the guarded gate, provides arithmetic term/formula leaves, and builds the induction-matrix and ordinary-PAeq proof compilers. A separate adapter connects the exact Foundation `nativePARefutation` endpoint to ordinary PAeq.

The final witness composition is explicit. A PA proof is compiled to a numerical derivation, then an all-store halting word, a cofinally coded candidate, a scheduler bound, a source clock, and a physical clock. The opposite implication maps a halting computation to an internal PA proof. The negative consistency equivalence is transferred intuitionistically; the papers correctly avoid deriving a positive existential equivalence from a double negation or invoking Markov's principle.

## Scope of this review

The architecture and the displayed recursion/clock arguments were inspected. No concrete mathematical error was found in the inspected components. This review did **not** independently reconstruct every cited finite proof recipe, all transitive Lean dependencies, or the entire inherited syntactic PA compiler. Consequently the new research should identify this paper-level calibration as an inherited mathematical dependency, and should not describe an executable table check as a kernel proof of that calibration.

A new literal machine with a fully justified iPRA halting equivalence to the exact calibrated AX11H machine inherits the written absolute conclusion by intuitionistic propositional reasoning. This is an honest mathematical composition. It should be stated with its exact source and dependency rather than automatically downgraded to a conditional theorem solely because Lean is unfinished.

## Direct transformation criterion

For a transformation between parent and child machines, the clearest new theorem consists of primitive-recursive witness bounds `H_parent(t) -> H_child(B(t))` and `H_child(t) -> H_parent(C(t))`, where `H` means halted by time. The proof must cover all recurrent paths and intermediate times, retain the initial all-zero tape, and prove any context invariant used by a shortcut. A state renaming, reflected copy, alternate start, unused-row change, or graph-distinct diagnostic with broken startup does not supply the requested materially different blank-start design.

The rooted graph inventory preserves the designated start, the zero blank, the read/write labels, and the halt target. A supplementary root-free action-graph comparison is useful for rejecting cosmetic novelty when a native table has no recorded start. Such a comparison is deliberately stronger as a structural test; it must not be called an equivalence of blank-start computations.
