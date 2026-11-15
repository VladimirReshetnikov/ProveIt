# Audit of the revised AX11H written consistency calibration

## Finding and scope

The revised AX11H packet supplies a substantial ordinary mathematical argument for the absolute statement

\[
\mathrm{iPRA}\vdash\operatorname{Con}(\mathrm{PA})\leftrightarrow\neg\operatorname{Halt}_{\mathrm{blank}}(M_{\mathrm{AX11H}}).
\]

It does not merely assume the desired calibration, and it does not infer it from finite machine tests. Its main constructions are explicit primitive recursive proof transformations, finite-demand recursion with a stated decreasing rank and acyclic strata, exact execution clocks, and bounded or existential induction invariants appropriate to the stated weak theories. Reading all ten mathematical components did not reveal a concrete fatal gap or a circular calibration assumption. It is reasonable to use it as an **inherited written theorem**, stating that dependency openly.

This audit is not a new proof-assistant verification of that theorem. The complete proof compiler is specified mathematically rather than implemented and run. Some fixed, very large numerical proof lists are supplied through concrete finite Lean proof recipes; neither the packet nor this audit evaluates all those lists. The audit checked the dependency structure and inspected representative exact source definitions, but did not re-prove every transitive imported finite relational recipe. These are limitations of independent verification, not an additional assumption of PA consistency or an identified mathematical disproof.

The defensible formulation for a new machine with a fresh exact weak-arithmetic relative simulation is therefore: **a written iPRA consistency equivalence, obtained by composing the new simulation with the supplied revised AX11H written calibration; end-to-end Lean certification remains incomplete.** It would be inaccurate either to call this a newly kernel-checked theorem or to replace all its mathematical content by an unexplained conditional calibration premise solely because Lean is unfinished.

## Exact primary sources

The audit uses ProveIt commit `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`. The authoritative component directory is:

`Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/proof/`.

The ten files total 218,296 bytes. They were all read in full. Their SHA-256 values and the equality checks are recorded in `calibration_identity_audit.json`. Every one matches both the pinned filed v2 packet and the copy inside `docs/incoming/PA194ORH_research_2026-11-15.zip`, member `PA194ORH_research/reference/calibration_AX11H.zip`. The nested ZIP has SHA-256 `93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`.

The existing one-way transfer code was additionally inspected in `ConPAISigma1Directions.lean`. Its exact Git blob `fa03b3720d1e56c316c75f8c196b4f3f7f889cc1` matches the current top-level `PA/isigma1-machine/ConPAISigma1Directions.lean`, not merely an unrelated historical copy. Representative fixed-proof and target-soundness source identities are recorded in `calibration_source_checks/identity.json`.

## What the ten components actually establish

| Component | Concrete contribution | Point requiring care |
|---|---|---|
| `ax11h_preservation.tex` | Exact four-operand AX effect, eleven emitted entries, no-push MP, cache-only Shift, all-store proof-word compiler, cofinal candidate encoding, scheduler completeness and soundness. | It handles `[0;0]=0`, arbitrary carried stacks, early halts, the real fourth AX operand, and the failure of plain Shift to detect a visible contradiction when the cache is zero. |
| `ipra_simulation_theorem.tex` | General exact primitive recursive simulation theorem with explicit forward/reverse halting witnesses. | Positivity or an explicit cofinality certificate is essential; finite tests or eventual termination do not supply it. |
| `physical_ipra_audit.tex` | Interprets the literal symbolic tape rules, proves the four list traversals and full frame closure, proves exact blank initialization and physical/source simulation. | Every register value and the arbitrary spare list are quantified. The clock handles zero-duration absorption at source halt through a live-state cofinality argument. |
| `source_command_completion.tex` | Binds all 3,671 source instructions and their outgoing edges to arithmetic templates, supplies exact primitive recursive macro clocks, and proves source/scheduler simulation. | Scratch preconditions, total four-field parsing, fresh-counter update, and the actual retained halted register file are kept explicit. |
| `consistency_implies_nonhalting.tex` | Numerical derivation soundness in arbitrary candidate-PRA models with an IΣ₁ reduct, then halt-to-PA-refutation and the negative consistency implication. | Its cumulative PA-proof-witness invariant is Σ₁ and is honestly justified in IΣ₁, rather than mislabeled quantifier-free. |
| `q_exchange_ipra.tex` | Uniform finite proof-list translations between C4 and C4Q using restricted-rho implication templates and premise exchange. | This is independent of the PA forward compiler, avoiding a circular use of the desired calibration. |
| `foundation_paeq_completion.tex` | Adapts the exact current Foundation PA proof predicate to the historical ordinary-PAeq intermediate presentation. | The two formula codings and the two falsity codes are not conflated. The one changed finite axiom, induction recognition and the model-theory compatibility are addressed. |
| `term_leaf_completion.tex` | Explicit finite-demand algorithms for term syntax, substitution, guard projections, totality, coherence, uniqueness, and vector realization. | Growth under substitution is handled by lower-stratum calls, rather than an incorrect assumption that every resulting code decreases. |
| `forward_calibration_completion.tex` | Supplies the lower relational interfaces and constructs arbitrary formula, induction-axiom, and PA-proof compilation in IΣ₁ by finite request trees. | It replaces uses of full PA induction by bounded finite-table invariants and gives an acyclic dependency order. Fixed native proof recipes remain inherited finite data. |
| `consistency_equivalence.tex` | Composes the exact witness transformations with the two existing one-way negative-translation endpoints for the atomic halting matrix. | It claims an ordinary written theorem and explicitly disclaims a new end-to-end Lean/Rocq build. |

## Why the weak arithmetic claim is substantive

### A real refutation-to-halting witness

The final component, subsection “A uniform refutation-to-halting witness” and equation `(Final-time)`, defines the witness rather than saying that a successful search eventually occurs. Let `A(d)` transform a current Foundation refutation into an ordinary-PAeq proof; let `F` compile that proof into a numerical derivation. The proof-word compiler gives the all-store halting word `V_e = A0 ; W_e ; Pop`. Its extra AX prefix gives a raw enumerated candidate

\[
N_e=p(2,p(0,p(0,p(0,e_{\rm word}(V_e))))),\qquad K(e)=(N_e+2)^2.
\]

The argument proves that candidates below this one either halt or drain within their seed plus one commands. It needs no reset of the store carried between candidates and no least-successful-candidate search. Exact source and physical cumulative clocks then give

\[
T_M(e)=57922+\tau(B(K(e))).
\]

All the iterates and bounds are specified primitive recursions. In particular this is not an appeal to termination of an unspecified unbounded search. The variable gap, spare list and register file are included in the state used to compute the physical clock.

### The bounded all-store command induction

An unrestricted universal assertion over all stores cannot simply be used as an induction formula of iPRA. The subsection “A quantifier-free proof of the compiler invariant” in `ax11h_preservation.tex` explicitly introduces a monotone primitive recursive envelope for one command and bounds all stores visited during every compiled word. It inducts on a Boolean finite check of earlier proof lines and stores below their assigned bounds. The final line's bound is the arbitrary initial-store code, so the bounded invariant supplies the wanted uniform conclusion. This directly addresses the weak-theory issue.

### Finite-demand proof compilation

The finite-demand construction in `forward_calibration_completion.tex`, around equations `(F4)`–`(F7)`, allocates a finite request tree from an input rank. Child requests are computed from syntax and parameters before their proof outputs are needed. Same-stratum children have smaller rank; a binary tree bounded by `2^(r+2)-1` suffices. A forward traversal assigns requests and a reverse traversal combines proof lists. Its correctness is a bounded Boolean assertion about the already processed request/output table (or an equivalent Σ₁ witness assertion in the stated model setting).

The final seven-stratum order in that file identifies every higher-level dependency. In particular:

- Generic relational compilation precedes arithmetic term suppliers.
- Term totality/coherence precede uniqueness and vector realization.
- Replacing a source term by a larger term calls an already completed lower stratum; it is not a same-stratum descent on an increasing code.
- Arbitrary-property separation uses the guarded gate and lower vacuity/binder operations. It does not call the arithmetic formula compiler whose induction it will help discharge.
- Formula realization precedes arbitrary PA induction matrices, and the complete induction witness is retained while the outer closure depth decreases.
- The outer PA-proof compiler calls the previously completed axiom supplier; it does not presume the source proof's semantic truth.

These constructions contain the substance needed to address the repository's warning that the old proof used full PA induction over all environments. Merely citing the old theorem would not have been enough; the revised manuscript instead describes new recursors and their invariants.

### Exact physical simulation, including the halted case

`physical_ipra_audit.tex` starts from a complete finite-support tape code and supplies explicit interpretations of the symbolic rules. The four list-traversal recipes are verified from the literal transition rows, then lifted to arbitrary coded lists by primitive recursion. The frame equality covers both sides of the head and the entire spare file, not merely a projection of the live registers.

The actual physical clock assigns zero duration to the canonical absorbed source halt. Thus the stronger global inequality `tau(k) >= k` would be false after halting. The manuscript does not rely on that inequality: it proves that if the source at stage `k` is still live, then `tau(k) >= 3k`. Given a physical halt at `t`, choosing source stage `t+1` and using absorption rules out its being live. Equality with the halt code is decidable. This gives a reverse witness without a least-boundary search or Markov's principle. The separate generic positive-duration theorem is explanatory; the actual instance uses this correct live-state argument.

### Exact PA predicate and the final intuitionistic step

`foundation_paeq_completion.tex` identifies the Foundation dependency `32e1a0956a8622fad067328ca1959729a7634428`. Its adapter distinguishes current-source formula pairing from machine Cantor pairing and source falsity code `13` from numerical contradiction code `1`. It accounts for all proof rules, bounded induction-axiom witness extraction, explicit opening/closing operations, and the changed `addEqOfLt` finite axiom.

The final argument does not assert that an arbitrary IΣ₁ theorem automatically belongs to iPRA. It applies the specific existing endpoints `ConPA.Directions.ipra_nonhalt_implies_consistency` and `ipra_consistency_implies_nonhalt`. Inspection of their exact current Lean source confirms that they take the corresponding implications in every candidate-PRA model with an IΣ₁ reduct, then use the established conservation/negative-translation and PA-witness machinery. The proposed halting matrix `chi_M(t)=1` is atomic, hence satisfies the open/bounded requirements. Neither endpoint needs an intuitionistic inference from a double-negated existential to the positive existential itself.

## Residual dependencies and verification limits

The fixed relational leaves in the forward compiler are concrete `*NativeProof` definitions, listed in its “Closed relational leaves” paragraph. Representative inspected examples actually construct typed derivations with explicit reserve functions: `zeroNativeProof`, `successorNativeProof`, `additionNativeProof`, `multiplicationNativeProof`, and `fixedImageNativeProof`. They are not axioms declaring PA consistency. The fixed-axiom supplier has twelve standard cases; arbitrary internal induction axioms are handled separately by the new uniform construction.

The manuscript explains how the fixed finite recipes are reinterpreted through its retained logical interface after removal of obsolete primitive equality-vacuity. It explicitly identifies the old equality-vacuity consumers and supplies replacement reverse-rewrite and neighborhood constructions. This is a mathematical proof-transport obligation. This audit checked that it is addressed and did not find a dependency returning to the PA calibration. It did not independently normalize every enormous recipe or run the transitive Lean development. Any later discovered defect there would affect the inherited written theorem and all descendants that use it; a source-equivalent machine transformation cannot repair a logical calibration defect.

Two local wording cautions should not be mistaken for hidden final assumptions. The generic `ipra_simulation_theorem.tex` introduction retains the phrase “still-unproved consistency calibration” from its standalone role. `term_leaf_completion.tex` ends by saying its term stratum alone does not complete lower relational interfaces or the higher proof transport. The full packet supplies those layers in the other components and explicitly states the composed final theorem. Read as a collection, these cautions identify modular scope rather than establish a circular final premise.

## Relation to the repository's open Lean status

The pinned top-level `PA/README.md` reports that the machine-specific iPRA directions for the primary PA194, original PA195 and PA196 have not yet been established in the repository's formal development. It also records which modeled scheduler, gate and transfer components have been formalized and which physical/model compiler connections remain open. The primary PA194 table has hash `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`; it is not the revised AX11H table with hash `c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a`.

The revised AX11H manuscript expressly states that its new ordinary argument does not change that proof-assistant status. Both statements can hold: there is an inherited written mathematical proof for the exact revised AX11H table, and there is no completed end-to-end Lean verification of it or of the new descendants. The final deliverable should state both, without calling the Python receipts an iPRA proof and without downgrading every written mathematical argument merely because its formalization is unfinished.
