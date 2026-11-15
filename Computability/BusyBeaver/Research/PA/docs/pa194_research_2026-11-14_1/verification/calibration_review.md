# Focused review of the revised AX11H written calibration

Pinned repository: e6a84f8dd2702f5f8c7db3ca53a8cbacb1d89f4f.
Relevant packet: Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/.

This is a focused mathematical dependency review, not an independent reconstruction of the whole numerical PA compiler and not a kernel check.

1. The top PA README preserves the open Lean status. The revised packet nevertheless makes an explicit **written mathematical iPRA theorem**. These two facts must not be conflated.
2. The physical proof uses codes of full finite-support tapes, not equality on a bounded observed prefix. It interprets all finite symbolic instructions by arithmetic equations. Variable spare-list width is tied to the very same list denoted in each tape atom.
3. It handles arbitrary register values and all spare-list lengths via quantifier-free induction over explicit coded lists. The four generic list traversal arguments are supplied before the machine-specific contract composition.
4. Nonhalting endpoint closure is equality after padding each address to the header width, with overflow checked to be zero. Both zero and positive decrement cases are included. The changing gap and spare list are part of the extended source state.
5. Segment duration is zero after canonical source halt. The proof does not incorrectly assume global cofinality then: it proves z_k != Halt implies tau(k) >= 3k. A physical halt by time t forces source halt by t+1 using absorption and decidability of the source halt flag. This is a legitimate intuitionistic argument.
6. The generic positive-segment transport theorem is sound under its explicit hypotheses. In particular, it requires exact endpoint equality and either positive duration or a separately proved cofinality certificate. Merely running source instructions for standard finite times is not substituted for the uniform hypotheses.
7. The forward PA-to-calculus proof replaces strong induction over all environments by a finite demand tree, whose children are determined before outputs are returned and whose same-stratum rank decreases. It uses bounded Boolean invariants over explicit tables. A fixed finite stratification of primitive-recursive transformations avoids an unbounded recursion on returned proof values.
8. An exponential upper bound on query slots is primitive recursive and is therefore compatible with the stated weak base. No small complexity claim follows, but no such claim is needed for finite syntactic proof translation.
9. The current Foundation PA predicate is connected to historical PAeq by an explicit adapter; the report distinguishes Foundation falsity code13 from target contradiction code1. The final iPRA theorem uses the repository's existing two one-way I-Sigma-1-to-iPRA transfer results, not positive double-negation elimination or Markov's principle.
10. The reviewed files contain no obvious omitted cofinality, reset-store, or all-standard-inputs-only step of the kinds found in earlier drafts. The exact axiom-supplier strata, every source recipe identity, and all current Foundation encoding cases have not been independently rebuilt here. A derivative result should therefore identify this written calibration as an imported theorem and leave the incomplete end-to-end Lean status explicit.

Files closely read: proof/consistency_equivalence.tex, proof/forward_calibration_completion.tex, proof/ipra_simulation_theorem.tex, and the state/tape/clock/closure portions of proof/physical_ipra_audit.tex. The remaining adapter and term strata are dependencies cited by those files, not newly verified by this note.
