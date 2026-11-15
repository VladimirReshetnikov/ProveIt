# Scope audit: inherited PA calibration and the AX11GH/GHS interface

Date: 2026-11-14. Repository revision: `8d31445d858761a8f6150c2e5012adae8895e932`.

## Finding and its scope

The later AX11H written calibration and the AX11GH/GHS command protocol are compatible. No concrete defect was found in the weak-induction arguments and protocol interfaces examined here. In particular, the change to an explicit generalization binder and the change to testing only the cached formula do not invalidate the refutation compiler: the current GH/GHS paper changes its command words and its induction invariant accordingly.

This supports using the **identified inherited written theorem** as a dependency of a new relative machine construction. It is not a new end-to-end proof-assistant verification, nor an independent reconstruction of every arithmetic compiler in the inherited development. The repository's incomplete Lean status and the later packet's written mathematical theorem describe different verification levels and should both be stated accurately.

A precise way to state a composed result is: “The new machines are proved equivalent in iPRA to the specified AX11GH/GHS tables by the new relative construction. Composing this with the included, explicitly identified written PA calibration gives the written Con(PA) equivalence. The end-to-end Lean formalization remains incomplete.”

## Exact dependency identity

The GH/GHS packet examined is the `_1` incoming extraction, whose internal directory is `pa194_ax11gh_research_2026-11-14`. Its `references/ax11h_written_ipra/proof/` contains ten proof sources. All ten are byte-for-byte equal to the corresponding files in the current repository's `PA/docs/pa194_ax11h_research_2026-11-14_2/proof/`. The equality check and SHA-256 values are in `inherited_proof_identity.json`.

The retained AX11H archive is identified by SHA-256 `93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075`. The relevant baseline QAX11H dense-table hash is `19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50`. These identifiers distinguish the later written completion from earlier conditional packets.

Both compiler source manifests were checked against the current pinned Git tree and against the actual bytes of a cached checkout. All **490 manifest entries, covering 441 distinct paths**, matched their declared Git blob hashes; there were no mismatches. Of these entries, 423 are in `research/calibration_forward/source_manifest.json` and 67 in `research/calibration_terms/source_manifest.json`. `source_manifest_audit.json` records every comparison. Hash agreement verifies source identity; it does not verify all mathematical claims made about those sources.

## The finite-request repair

The substantial forward-calibration issue is whether recursive proof translation can be justified with the permitted weak induction when environments, fresh labels, and proof sizes grow. The later packet does not simply reuse an induction hypothesis quantified over all environments.

In `forward_calibration_completion.tex`, each request carries a rank and finite parameters. Same-stratum child requests have smaller rank, and their complete parameters are computed before any child proof is returned. A complete binary demand tree of depth at most the initial rank plus one gives a primitive-recursive finite slot bound. A forward pass computes the requests; a reverse pass supplies proof outputs. The two correctness invariants are bounded Boolean conjunctions over the finite slot array. Lower strata are already completed primitive-recursive functions; their input ranks may grow without creating a recursive cycle. There are finitely many fixed strata, not an interpreter for arbitrary total functions.

This addresses the relevant quantifier issue. The proof still needs the local constructors and their child-parameter formulas, so the audit also read the allocator, connective, canonical-matrix, and term-supplier portions. Representative comparisons with the pinned Lean sources agreed: the two quantifier-child allocator requests in `FoundationRelationalSequentAllocator.lean`, the connective parameter maps in `NumericPAeqFormulaRealizationConnectives.lean`, and the concrete proof-producing seeds in `RelationalClosedCertificateSeeds.lean` match the written interfaces.

`term_leaf_completion.tex` makes the term-syntax functions explicit and separates syntax, uniqueness, substitution, totality/coherence, vector realization, and guard routines into lower strata. One delicate case calls uniqueness on a substituted term that may be larger than its caller's term. This is a call to an already completed lower stratum, not a violation of same-stratum rank descent. The fixed seeds are explicit finite derivation objects, not a truth oracle or a use of PA reflection. This audit did not evaluate the enormous final compiler outputs or independently instantiate every fixed proof seed.

## The exact PA predicate

`foundation_paeq_completion.tex` explicitly bridges the historical ordinary-PA-with-equality presentation and the current Foundation predicate. It accounts for the false-formula code 13 in the Foundation presentation versus code 1 in the numerical calculus; it does not identify them silently.

It also treats the finite-axiom difference involving the strengthened existential witness in the older `addEqOfLt` axiom, and it supplies the required opening, closing, substitution, and equality-replacement transformations. For induction, the canonical matrix witness is retained through the recursion, rather than replacing the base case with an arbitrary closed formula. The candidate matrix search is bounded using `Open(m,b)`, which need not be bounded by the original formula code. Formula replacement uses constructor-count rank where an opened formula code can increase. These are the cases in which a superficially similar historical presentation would otherwise be insufficient.

The detailed audit read the forward-completion, term-completion, Foundation-adapter, final-equivalence, and consistency-implies-nonhalting arguments, as well as the command-preservation induction and the physical-clock composition. It sampled the cited Lean recipes; it did not rebuild the Foundation dependency or every quoted theorem.

## Why the changed GH/GHS commands still compile refutations

Write a command store as `(t,w,d,h)`. Let `I(a,b)=4p(a,b)` and `U(i,a)=4p(a,i)+2`, where `p` is Cantor pairing. The GH/GHS interface is:

* `AX(c,x,y,z)` pushes eleven entries, clears visible top and cache, and leaves offset `z`. The generalization entry is exactly `U(c,h)`, using the **incoming** cache. It is not `U(c,h+y)`.
* `MP(x)` compares the cache with `I(t,d+x)` and returns the consequent on equality, or zero on inequality. It does not push the result.
* `Shift` halts precisely when `h=1`. Otherwise it shifts the cache into the visible top and pops the stack into the cache.

The literal AX exit falls through the full MP operand reader. Consequently its encoding genuinely has a fourth operand. The current paper encodes that operand and gives the residual continuation correctly; using the old three-operand encoding would be wrong.

Let `A=AX(0,0,0,0)` and `S=Shift`. The exact stack algebra establishes

* `Push = A; S^10; MP(0)`, returning `(0,[t;w],0,0)`;
* `Pop = A; S^12`, returning `(t,w,0,a)` from `(t,[a;w],d,h)` when `t != 1`, and halting when `t=1`;
* `Gen_i = Push; S; AX(i,0,0,0); S^11`, returning `(U(i,a),w,0,0)` from `(a,w,0,0)`.

The `Gen_i` identity includes `a=1`: after `Push`, the first Shift places `a` in the cache while testing zero; AX consumes that cache before another Shift can test it. Thus the proof does not need to assume the premise is noncontradictory. The axiom selectors are safe because their first nine head entries have residue zero modulo four and their generalization entry has residue two. The twelve-Shift Pop checks the original top exactly at the final exceptional branch.

The MP compiler reserves a zero below its two premises. From `(0,[a,I(a,b),0;w],0,0)`, the suffix `S; S; MP(b); Pop` either halts on a contradiction premise/conclusion, or returns `(b,w,0,0)`. The reserved zero is essential because successful MP does not push.

The derivation compiler's all-store claim is proved using a finite conjunction over all relevant derivation nodes and bounded stacks, with a height-dependent primitive-recursive bound. The scheduler then uses a cofinal AX prefix and the explicit bound `(N_e+2)^2`; it does not reset the carried store or select the least successful candidate. The reverse proof annotation treats the offset as unrestricted and annotates the top, cache, and canonical stack with genuine numerical derivations. These changes match the new interface.

## Independently replayed finite source checks

The supplied checkers were read and rerun on both exact incoming source artifacts. Output was written to this audit's own directory. All checks passed.

| Check | AX11GH | AX11GHS |
|---|---:|---:|
| Complete primitive instruction rows and outgoing edges | 3,671 | 3,668 |
| Expanded AX macro tokens | 190 | 190 |
| Matched arithmetic-template blocks | 947 | 945 |
| Local exact-duration examples | 882 | 882 |
| Composed Shift/MP clock examples | 324 | 324 |

`commands_PA194AX11GH.json` and `commands_PA194AX11GHS.json` record the free-term command identities, all head expressions, both guard branches, raw-cache generalization, fourth-operand residual, contradiction cases, and zero aliases. The `source_commands/` receipts record the complete instruction-array/template match, an independent expansion and control-flow resolution of the binary source tree, scratch-register preconditions, and a whole-emitter free-algebra check.

The instruction and free-algebra checks are finite symbolic bindings. The small numerical duration examples are regression checks; the uniform clock argument is the written counter-induction proof. This audit did not independently rerun every physical tape contract or the blank startup. Such checks belong to the machine construction and its physical verification receipts.

## Composition inside iPRA

The new protocol proves a relative equivalence with numerical refutations in the exchanged distribution calculus `C4^Q`. It is therefore aligned with QAX11H, not merely with an informally similar Hilbert system. The retained `q_exchange_ipra.tex` supplies the fixed finite exchange translation between the two distribution orientations.

The inherited absolute argument uses explicit primitive-recursive refutation-to-run witnesses and a reverse proof annotation in the specified model class. The one-way conservation and negative-translation endpoints conclude the negative implications required for `Con(PA) <-> not Halt`. It does not extract a positive intuitionistic existential from a double negation and does not require Markov's principle. The physical/source composition uses positive clocks before halt and canonical absorbed halted codes; its reverse implication is a decidable finite case split, not an informal claim that a future boundary must eventually be reached.

For any new machine with an iPRA-proved halting equivalence to one of these exact GH/GHS tables, intuitionistic propositional composition transfers the negative consistency equivalence. This audit finds the inherited interfaces adequate for that composition. The complete arithmetic derivation remains an inherited written dependency until the separate formalization is completed.

## Reproducibility artifacts

* `inherited_proof_identity.json`: all ten byte-identity checks and SHA-256 values.
* `source_manifest_audit.json`: 490 exact manifest-entry comparisons against current Git and cached file bytes.
* `commands_PA194AX11GH.json`, `commands_PA194AX11GHS.json`: replayed command algebra.
* `source_commands/PA194AX11GH/` and `source_commands/PA194AX11GHS/`: replayed source binding, template ports, and clock examples.

No unsuccessful source-level reduction studied during this audit is claimed as a machine with the required equivalence. In particular, replacing the symmetry/vacuity head by a shorter reflexivity-like head, weakening the equality witness, or strengthening the gate's freshness condition would require new completeness proofs; similarity of intended semantics is insufficient.
