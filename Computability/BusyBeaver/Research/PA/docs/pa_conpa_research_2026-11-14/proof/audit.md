# Audit of the inherited iPRA calibration and the new transfer

## Result and scope

The latest incoming `pa194_ax11h_research_2026-11-14.zip` contains a substantially stronger written argument than the older placed packet with the same basename. Its conclusion is a written iPRA equivalence for the literal AX11H and QAX11H binary transition tables. Its `claims.json` expressly declines to claim a new end-to-end Lean or Rocq build. The incomplete proof-assistant status of the repository therefore does not contradict the written theorem.

The review found no concrete mathematical gap in the weak-base constructions inspected below. In particular, the latest packet addresses the two most serious potential shortcuts: induction on an unbounded family of input environments, and the use of PA-model soundness where model-uniform IΣ1 correctness is required. It gives explicit bounded or finite-demand replacements for both. The new AX11GH/GHS proof can consequently use its QAX11H theorem as an identified mathematical dependency. It does not obtain a new PA calibration merely from sample simulation or from the repository's conditional Lean endpoint.

This audit is not an independent kernel verification of every inherited source recipe. The finite implementation checks and selected proof constructors were replayed or read; the complete numerical PA-proof compiler was not evaluated or implemented anew. Its correctness remains a mathematical proof dependency, with its exact source recipes and fixed derivations preserved in the inherited archive.

## Exact dependency identity

The retained baseline is the incoming archive at the audited corpus revision, with SHA-256:

`93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`

The corpus ProveIt commit is `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`. The baseline's own reference snapshot is `1c9524d8bf2e0a27b9a16ff622359927f536e663`, with Foundation submodule `32e1a0956a8622fad067328ca1959729a7634428`.

The endpoint version comparison was made explicitly rather than assuming the words “current PA” fix a stable code:

| Item | Identity checked at the corpus revision |
|---|---|
| Foundation submodule `lib/FormalizedFormalLogic-Foundation` | Gitlink remains `32e1a0956a8622fad067328ca1959729a7634428`. |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAPA196Consistency.lean` | Blob remains `ff5926a5cf1cd350403c84329e42775b13a1eb19`, matching the baseline endpoint manifest. |
| `Computability/BusyBeaver/Research/PA/pa195/ipra/PA195RefutationBridge.lean` | SHA-256 remains `fd043d3493d4386a70e38f39f4b172b357d714ddb7da07ba276a5892b1c5d655`, matching the baseline endpoint manifest. |

The structured receipt is `endpoint_identity.json`. The consistency sentence in the theorem is the inherited `nativePAConsistency`, defined as the negation of the native reading of the mapped Foundation PA-refutation predicate. This is not an unqualified identification of Cantor-coded numerical proof lists with Foundation proof codes.

## Proof-chain review

Paths in this section are relative to the root of the retained baseline archive.

| Connection | Principal source | Review finding |
|---|---|---|
| Literal binary table ↔ exact primitive-register source | `proof/physical_ipra_audit.tex` | Explicit literal-step semantics, symbolic-run induction, four list-scan lemmas, frame closure, whole initialization and positive PR clocks. The proof includes arbitrary gap and spare-list parameters, rather than fixing them to startup values. |
| Primitive source ↔ abstract scheduler | `proof/source_command_completion.tex` | Every source instruction and edge is matched to arithmetic templates; exact clocks are proved by counter induction. Full AX fallthrough consumes the fourth field, including nonzero values. |
| Abstract scheduler ↔ numerical refutation | `proof/ax11h_preservation.tex` | Exact cached-guard Push/Pop contracts, reserved-zero MP, all-store refutation word, four-field encoding, cofinal scheduling and bounded-input compiler induction. |
| Ordinary sixth head ↔ exchanged sixth head | `proof/q_exchange_ipra.tex` | A fixed acyclic restricted-implication derivation gives premise exchange. Proof-list translation uses index relocation with bounded Boolean invariants. No forward PA-calibration assumption occurs. |
| Numerical refutation → current PA refutation | `proof/consistency_implies_nonhalting.tex` and `references/reverse_soundness/` | Uses the model-uniform seed-soundness route and the stated one-way transfer; it does not appeal to truth in only the standard natural numbers. |
| Current Foundation PA → historical ordinary PAeq | `proof/foundation_paeq_completion.tex` | Source syntax, proof tags, canonical closure count and induction recognizer are fixed explicitly. The changed finite arithmetic axiom is translated by a supplied proof, and the metatheory-base difference is also addressed. |
| Terms, substitutions and finite logical leaves | `proof/term_leaf_completion.tex` | Query trees use decreasing source rank; child parameters are determined without reading returned certificate values. Finite tables avoid universal-environment induction. |
| Ordinary PAeq → numerical C4 | `proof/forward_calibration_completion.tex` | Gives the construction order, finite-demand algorithm, fixed-template suppliers, ordinary proof compiler and contradiction readback. The old stronger PA soundness theorem is not simply re-labeled as IΣ1 soundness. |
| Full iPRA consistency equivalence | `proof/consistency_equivalence.tex` | Composes exact clocks and the two all-model implications through the established one-way endpoints. No Markov principle or double-negation elimination for a positive existential is used. |

### Why the physical bridge is stronger than bounded simulation

The finite files contain symbolic outcomes for every source instruction branch. Each outcome ranges over arbitrary primary register values, an arbitrary nonempty spare-register list and an arbitrary nonnegative gap. The symbolic interpreter's rewrite rules are justified by literal binary steps and unary/list induction. The four list rules are derived from the literal table; they are not unproved simulator oracles.

The physical frame stores the actual evolving source register file, gap and spare list. The cumulative physical clock is primitive recursive on those extended configurations. A quantifier-free induction proves equality of the physical run with the encoded source state at each clock boundary. Positive duration supplies the reverse direction: if a physical run has already halted at time t, a certified later live frame after more than t source steps would contradict absorption. This argument covers nonstandard internal input codes once the equations are interpreted in the weak arithmetic model.

The new physical certificates were independently replayed from the actual GH/GHS literal tables, not inherited by filename. New GH uses 3,671 source sites and 4,778 outcomes; new GHS uses 3,668 sites and 4,774 outcomes. Their startups are respectively 57,922 and 57,768 steps. Older `PA194GH` / `PA194GHS` results in exploratory working directories refer to different machines and must not be substituted for the `PA194AX11GH` / `PA194AX11GHS` receipts.

### Why the abstract compiler proof uses permitted induction

An informal induction asserting correctness “for every base stack” would not itself justify an iPRA proof. The baseline instead computes the largest compiled-word length L and command code K from the finite proof, then uses the monotone primitive recursive envelope

`Phi_K(s) = 1 + max(s, max_{c <= K, u <= s} next(c,u))`.

For a proof of N lines and a fixed initial store code s0, line j is proved correct for every normalized input no larger than `Phi_K^(L(N-1-j))(s0)`. The induction invariant is a bounded conjunction retaining every earlier line's correctness. A premise invocation reached by a prefix of the current word is inside the earlier line's larger bound. The final line covers the original arbitrary store, after which ordinary universal generalization is available. All maximization is bounded, and all word execution is primitive recursive with an absorbing halt flag.

The same argument applies after replacing the old generalization word by the shorter explicit-binder word. A bound linear in the number of nodes applies to an expanded derivation tree, not automatically to a DAG's line count; the new report states this distinction.

### Why finite-demand compilation addresses the IΣ1 issue

The forward logical compiler previously needed some theorems proved under a full-PA model assumption. The latest document does not import their stronger conclusion. It extracts their finite parent proof recipes and constructs the required instances by a finite query tree.

Within each stratum, the input includes a natural rank. Each same-stratum child has smaller rank, and its parameter tuple is a primitive recursive function of the parent tuple independent of child proof values. Maximum branching is fixed. A complete tree can therefore be generated with an explicit primitive recursive node bound, then evaluated bottom-up. The values can be enormous without ceasing to be primitive recursive: one iterates a fixed PR operation a PR-bounded number of times.

The main document lists the order of strata and the particular child calls. Source-term structural rank, not the numerical size of a substituted term or returned certificate, governs the term recursion. This matters because substitution may enlarge the code. Lower-stratum results supply the calls that are not structurally decreasing. The associated correctness invariant checks a finite table of queries, values and local validity conditions; it is a bounded Boolean statement, or equivalently a finite witness-table Σ1 invariant in the IΣ1 formulation.

The reviewed fixed certificates are actual Type-valued derivation recipes, including the `RelationalClosedCertificate*Seeds.lean` and `PAInterpretedFixedCertificateSeeds.lean` families. Their selected reserve values are explicit standard naturals. The report reinterprets these finite recipes through the completed logical interface. It does not assume soundness of PA to conclude the finite leaf exists. This review read the named seed interfaces and a representative portion of those recipes; it did not expand every enormous numerical proof code.

### Current Foundation coding is a separate obligation

The incoming argument distinguishes three objects: current Foundation proof coding, the historical ordinary-PAeq presentation used by the forward compiler, and the Cantor-coded numerical calculus. It explicitly compares source constructor equations and proof tags, handles canonical parameter closure, and supplies an adapter for the finite arithmetic leaf that changed between Foundation versions.

The changed leaf must also be addressed in the weak arithmetic metatheory, not only in the object PA proof. The document provides the corresponding derivations between the current and historical finite arithmetic bases before transferring the IΣ1 reasoning. This closes a potential version-confusion gap that would remain if only object-level axiom translations were given.

The finite closure-constructor checker was rerun successfully in this review: 308 closure chains, 140 canonical induction readbacks, 36 existential projections, four changed-leaf adapters and 8,828 distinct primitive proof nodes. These finite tests supplement the displayed uniform constructions; they do not alone prove all-model correctness.

## Exact additional obligation for AX11GH/GHS

The new proof in `relative_ipra.tex` changes the saved AX generalization slot from `U(d,h)` to `U(c,h)`. Every other numerical axiom, every side condition, and every proof rule remains in the common C4Q calculus. Soundness appends the same Gen rule using binder c. Completeness uses

`Gen_i = Push ; S ; AX(i,0,0,0) ; S^11`.

Push has 12 commands; Gen therefore has 25. The middle Shift safely moves the incoming theorem into the cache, and the following AX consumes it before any further cached guard. This works even when that theorem is code one. All head selectors, the restricted-rho selector, the reserved-zero MP compiler and the final Pop are unchanged in their contracts. Pop halts exactly when its incoming visible top is one; a final plain Shift would be incorrect.

For GH, the primitive source differs from QAX11H at just the decrement and restoration increment used by the saved generalizer: register D becomes A at source addresses 95 and 100. For GHS, the Shift preparation additionally duplicates H to T and X, then compares `(1,h)` instead of `(h,1)`. Its exact clock changes, but the live and halted register files agree. This is a source implementation change, not a change to the abstract proof rules.

Two independently adapted source-command checkers produced identical operational code; their differences are comments and receipt metadata. Both new machines passed whole-emitter free-algebra checks, all instruction/edge bindings, 882 local duration instances and 324 composed S/MP instances. Symbolic command checks also passed for Push, Pop, all nine head selectors, restricted rho, explicit-binder Gen, MP including zero aliases and early halts, and the four-field encoder. The physical replay then certified the actual tables and startups.

These facts establish in iPRA that each new table halts iff C4Q has a refutation. The calibrated QAX11H table has the same characterization. Positive halting equivalence follows in iPRA, equivalence is preserved by intuitionistic negation, and the inherited QAX11H consistency theorem yields the desired Con(PA) equivalence. No new model-theoretic calibration is required for the explicit-binder change.

## Files to retain with the deliverable

Retaining the entire identified baseline archive is the simplest complete dependency record and avoids accidentally omitting a finite source recipe. It is approximately 4.9 MiB. In addition to the new machine artifacts and checkers, the reader-facing extracted proof subset should contain:

1. `proof/physical_ipra_audit.tex` and `proof/source_command_completion.tex` for the generic arithmetic simulation lemmas.
2. `proof/ax11h_preservation.tex` for the original compiler and bounded-input argument.
3. `proof/q_exchange_ipra.tex` for the C4/C4Q proof-list translations.
4. `proof/consistency_implies_nonhalting.tex` and `proof/consistency_equivalence.tex` for the endpoint assembly.
5. `proof/foundation_paeq_completion.tex`, `proof/term_leaf_completion.tex` and `proof/forward_calibration_completion.tex` for the hard PA-calibration obligations.
6. The baseline `claims.json`, provenance/manifest files and all referenced source recipes inside `references/`, `research/calibration_forward/`, `research/calibration_terms/` and `research/foundation_calibration/` (these remain in the intact archive).

The report should describe the result as a written mathematical iPRA proof with finite implementation certificates and a preserved baseline proof dependency. It should not describe the result as a completed Lean proof, an independently reimplemented PA compiler, or a sub-194 machine.
