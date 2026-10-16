# Batch 148, source 17: independent mathematical and clausal-reference intake

Review completed 2026-10-16. Arrival `5e5603303d`; untouched extraction `/tmp/zfc-intake-148-51452zxy/original/zfc_machine_research`. All execution was on the separate copy `/tmp/zfc-batch148-theory-review-mjaanodf/bundle`. The report audits ProveIt at `47f3a3602946dfe48803a91a910c646e74637ac8`. No extracted source was edited, no checksum manifests or line endings were checked, no Lean/Coq build was attempted, and no repository file was edited by this review.

## Verdict and placement

Continuation of the existing closure-kernel research collection, not a standalone new theory. Recommend source-17 `clause` placement with the full paper and its reference code/proof notes retained. I found no concrete mathematical or implementation error in the reviewed claims. The principal new contributions are an ordinary PA arithmetization of the known finite-sort obstruction, its general fresh-hull extension, an actual complete ground-clause certificate architecture/reference implementation, and a corrected tagged Capture-to-Collection extraction. None is an end-to-end binary-machine theorem or a new state record.

Read-complete scope: the whole main `report.tex` (including its mathematical sections, engineering summary and references), README/Makefile, both detailed clausal/Capture proof notes, both attribution notes, all of `clausal_trace.py`, `check_clausal_trace.py`, `capture_tagged_check.py` and `qpsc_syntax.py`. The inherited finite-sort code and full grammar experiment are assigned separately to root/backend intake; I did not repeat their executions. The machine-engine results in `experiment_results.tex` are not independently certified by this mathematical review.

## Mathematical claims and audit

### Ordinary PSC and existing work

Report lines 338–511 reconstruct the inherited equality-free subset-seeded PSC calibration. Full incoming/outgoing profile twins, the decoder, transitive covers, raw Separation/Union, hereditary incoming-profile saturation, purity cuts and transfer to a pure extensional quotient match the previous source-08/13/16 route. They are credited as inherited; this is not a newly discovered axiomatization. In particular a raw incoming-profile singleton is not silently substituted for a Full-profile twin decoder. The H-domain construction is mathematical, not a claim that our Lean library already proves the complete raw-PSC consistency equivalence. Passing to the well-founded/constructible interpretation is the existing consistency bridge, not same-model equivalence with Foundation/Choice.

### PA strengthening of the sorted obstruction

Report lines 661–828 give an ordinary proof that PA proves consistency of the reduced raw calculus and nonhalting of its specified abstract enumerator. This strengthens the host's existing ZFC-level explanation. The finite-domain sizes obey d_0=2 and d_(i+1)=d_i+2^(d_i). A(n)=product(i<n)d_i indexes assignments by mixed-radix digits; the update changes a single digit and stays in range. Each table T[n,k], k≤n, has A(n) bits, so the concatenation is bounded by 2^((n+1)A(n)). Recursive accesses decrease the formula code. The stated bound (n+1)A(n)(d_n+1) concerns Boolean writes/reads, not bit-complexity or physical runtime. The iterated exponential grows with input height but is still primitive recursive and PA-provably total. Strong induction on code proves ambient-dimension coherence; code freshness ensures no atom or binder exceeds the available coordinates. Coherence is needed for MP across different formula table dimensions and is supplied.

The explicit axiom parameters/back-references make the proof predicate primitive recursive. Finite-range G witnesses, vacuity, MP and GEN preserve all-assignment truth; the target is uniformly false. The abstract enumerator's failed operations/zero-stack tail and stack decrease are treated separately. This is an acceptable ordinary PA-provability argument, **not** a supplied machine-checked PA derivation, extraction program, or literal-table simulation. No unconditional literal 248/250/251/252 nonhalting result follows without the missing simulation theorem. The report correctly preserves this boundary.

### General fresh-hull theorem

Report lines 830–888: with output sort j below fresh hull sort k, all variables mentioned by the matrix outside k, and arbitrary guard G (which may itself mention k), choose in sort k the exact finite set of all matrix outputs in sort j. This global range makes both forward closure and unrestricted output support hold. The guard can only restrict forward obligations; it does not affect the range. Parameters and auxiliary prefix quantifiers are harmless. The binary sum constructing the range is bounded and formalizable in PA. The result rules out repairing the old program merely by changing the closure guard, same-variable specialization, IR, a primitive Bottom code or an unrelated quantifier row while leaving this variable-domain defect intact. It does not refute ordinary one-sorted PSC or the complete alternative checker.

### Complete ground-clause architecture

Report lines 890–1066 and `data/clausal_trace_proof.md` give a sound ordinary ZFC argument, with the correct front-end assumptions explicit. A certificate supplies finitely many matrix ASTs; the checker reconstructs the actual closed PSC wrappers, then signed clausification creates global fresh Skolem symbols with every active lexical universal as an argument. Existential symbols are not shared between axioms or unrelated occurrences. All universal occurrences are standardized apart; same-name shadowing is handled by scoped environment updates. Remaining universal variables are instantiated in a single common ground term algebra, including identification of different variables. This directly supplies the missing cross-variable/diagonal specialization that the sorted semantics defeated.

The propositional kernel's extension creates **all** children of a clause; a closed branch must have exact complementary signed atoms. Empty clauses close immediately. Fixed-order expansion of a finite unsatisfiable ground set is complete: an open terminal branch would select a consistent literal from every clause and thereby define a satisfying assignment. Closing only against the newest literal is sufficient because the construction closes at the first complement, when the newest literal belongs to a complementary pair. Herbrand compactness provides finitely many ground instances for an inconsistent finite axiom fragment; the natural certificate enumeration ranges over matrix lists, arbitrary terms and arbitrary finite traces together. Thus the specified ideal search halts iff PSC is inconsistent. The source-08 ordinary PSC calibration composes this with ZFC consistency inside ZFC.

The report does not claim a Lean proof, a compiled RM/TM or a new state count. Clausification, source decoding, Skolem dependencies, ground terms, branch restoration, enumeration and boot must all still be charged. Existing complete environment-tableau and source-16 Hilbert checkers remain independent controls.

### Finite class-theory competitor

Report lines 1068–1135 propose finite predicative GB plus **set** Choice, without Global Choice, as an alternative fixed finite source. Its external proof-transport argument credits Shoenfield/Hajek. It explicitly separates an externally primitive-recursive eliminator from a correctness proof in PA. No serialized finite GB axiom package, proof eliminator or competing binary machine is supplied here. I found no new contrary claim concerning the existing PSC branch.

### Capture extraction: independently checked against primary text

Report lines 1137–1199 and `data/capture_tagged_proof.md` identify a real error in the untagged extraction step printed on page 19 of Harvey M. Friedman's [Simplified axioms for class theory (15 September 2020)](https://bpb-us-w2.wpmucdn.com/u.osu.edu/dist/1/1952/files/2020/09/NBGAxioms091520.pdf). I opened the primary PDF and checked the local argument. This review rejects that particular inference, **not** the theorem about the full class theory.

Take von Neumann 0,1,2,3; A={0,2}; witnesses (0,1),(2,3); and untagged codes {x,{x,y}}. The first code equals A, so C={A} is a subset of the code class and its union covers A. Nevertheless it omits the second input's code and its double union omits witness 3. This verifies the stated finite counterexample.

The tagged repair uses a_x=<0,x> and b_y=<1,y>, then outer codes {a_x,b_y}. Injectivity and disjoint tags force a covered input code to be the input half of a code with the same x. The selected y lies in the **triple** union of C. The set of input codes is available by Separation from P(P(A∪{0,1})), without Replacement. The conditional lemma requires Extensionality, two distinct set tags, Pairing/Union/Power, limited class comprehension, subclass-of-a-set and Capture. It does not require Choice, Foundation, Infinity or Replacement once those resources/tags are supplied; it is not an independent audit of all preceding lemmas in Friedman's finite presentation. No existing hosted Capture theorem was found to be contradicted.

## Executable-reference audit

`code/clausal_trace.py`:

- Lines 27–51 reject Boolean/negative labels, enforce declared symbols and exact ground-term arity, and substitute one common term at every repeated variable occurrence.
- Lines 61–100 require closed source sentences, carry fresh variable and Skolem counters across all axioms, preserve lexical scope/shadowing, handle signed implication correctly, and give Truth the empty CNF and Bottom a singleton empty clause with polarity reversed under negation. Distributing disjunction over CNF is correct for both empty cases.
- Lines 102–122 accept exactly one ground argument per used clause variable. Variables inside Skolem terms are included; standardization counters remain stable as source axioms are appended.
- Lines 128–183 use a frame containing parent trail depth, clause and next sibling. Each closure truncates to the correct ancestor before entering the next child; all siblings must close. The last literal must complement a strictly earlier one. Trailing instructions and unfinished traces are rejected. Nested/last-sibling restoration is correct.
- Lines 186–192 admit only fields `matrices` and `trace`. Every PSC axiom is regenerated; the supplied synthetic generic-theory tests cannot be smuggled into the PSC entry point.
- Lines 195–277 give total mathematical Cantor/list/matrix/term/instruction/certificate codecs. Ground-term child codes strictly decrease (including the n=0 constant case); certificate enumeration is not stuck enumerating a fixed finite axiom fragment or a bounded term depth. The manual AST parser's Truth token need not occur primitively in exhaustive matrices because Bottom→Bottom defines it.
- Lines 279 onward reject malformed candidates; errors are never reported as proofs. The actual Python interpreter has ordinary memory/recursion limits, which the README/proof notes explicitly exclude from the ideal unbounded finite-storage specification. Prefix completion is a diagnostic event, not a consistency-search halt.

The generic `Clauses`/`check_trace` test API assumes its programmer-supplied clauses are well formed. The strict PSC-facing entry point is separately constrained. This is documented, not a theorem-mode bypass.

All of `check_clausal_trace.py` was read: its truth tables and Skolem expansion checks are independent finite semantic oracles, while its proof generator is deliberately untrusted and checked by the actual trace checker. `capture_tagged_check.py` exhaustively examines all covering subfamilies for the displayed finite tagged example only, not a model of the full class theory. The qpsc wrapper uses fresh binders above **all** matrix labels, scoped capture-avoiding simultaneous replacement of free slots 0/1, and universal closure of the remaining free parameters. That API is the correct ordinary common-domain PSC theory, rather than the retired fixed-slot numerical row.

## Executed suites

Standard-library children were invoked by a `uv run --no-project python` driver, cwd the separate review copy. The driver result log is `checks.log`; individual stdout/stderr and `checks/verification.json` preserve the results. The exact suite commands are listed below. All exited 0:

1. `python code/check_clausal_trace.py --output-dir /tmp/zfc-batch148-theory-review-mjaanodf/checks/clausal` — 1.265119 s. 159 closed generic formulas, 2,862 finite structure/Skolem comparisons; 20,854 CNFs of at most four nontautological clauses over three atoms; 4,613 accepted actual refutations; 15 malformed/unsound traces rejected; 200 PSC matrices producing 2,167 clauses and 1,326 Skolem functions (max arity 5); 5,000 natural round trips each for matrix, term and certificate codecs. Stable source-prefix, empty-clause, exact source-boundary, witness freshness and dependence controls pass. Cross-variable and diagonal specialization each have an explicit checked trace with two extensions and one closure. The varying-witness diagonal relation has a unary Skolem expansion and no constant expansion, as required.
2. `python code/clausal_trace.py --prefix 1000` — 0.298337 s. All first 1,000 candidates rejected. No inference about Con(PSC) or Con(ZFC).
3. `python code/capture_tagged_check.py` — 0.027694 s. Untagged inference fails; the displayed tagged family has exactly one covering subfamily and its triple-union bound succeeds.

The principal suite itself emits source hashes as provenance; I did not run any separate integrity/manifest checker. No advertised machine regeneration/grammar search or PDF build was repeated here; root's assigned reviewers cover those. No machine-checked theorem is inferred from any finite test.

## Current-repository overlap and remaining gaps

Repository paths below are relative to `/home/codex/.codex/worktrees/ec20/Proofs`; lines checked on the current tree during review:

- `Computability/BusyBeaver/Research/ZFC/typed_countermodel.md:1`: “The incoming finite-sort obstruction retires the reduced raw C/G calculus”. Lines 2–4 and 27–29 explicitly call the prior result ordinary mathematics/ZFC-definable. Source 17 adds the PA-strengthening argument; there is still no Lean countermodel certificate.
- The same file, line 38: “The literal tables have no proved simulation to this abstract enumerator.” Source 17 accurately retains this gap; no 248/250/251/252 literal nonhalting theorem is obtained.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RawPSCProfile.lean:22` defines `Full`; lines 78,96,126,156,164 already prove the decoder, cover, Separation and Union under the named resources. Source 17's reconstruction is overlap, not a missing implementation claim.
- `.../RawPSCModel.lean:22` defines `ModelsRawPSC`; line 44 is `instance_of_definable`; lines 136,141,147,153,175,188 connect actual equality-free Form-indexed PSC to twins/empty/power/cover/Separation/Union. Lines 257,265,271 implement purity cut/saturation/upward purity. Line 292, `pure_hull_of_model`, explicitly retains `hDef`, `PureLocalBound`, `PureRelationInvariant` (lines 294–295). Complete quotient/H-domain all-formula calibration and its arithmetic proof-code translation are still distinct tasks.
- `.../PSCSaturation.lean:192` is `saturated_hull_transfer` and line 217 `pure_hull_of_instance`, both under explicit resource hypotheses. They are not global semantic-relation closure axioms.
- `.../PSCCalibration.lean:166`, `same_models`, and lines 171/175, `psc_iff_zf0`/`psc_consistency_iff_zf0`, are the **Extensionality plus PSC** control. They are not the full equality-free raw-PSC calibration theorem.
- `.../Bottom3Syntax.lean:252` already checks the new source-16 primitive-Bottom decoder's label bound; lines 306/314 prove semantic normalization/roundtrip. It does not provide a complete calculus/refutation/machine bridge. Root's concurrent recent work should be credited independently of source 17's earlier pin.
- `Computability/BusyBeaver/Research/ZFC/README.md:124–127`: “It is not a computable proof-code translator verified in arithmetic. No theorem here supplies a proof-producing theory translator, a complete refutation checker, an enumerator compiler, a verified executing decoder, or the final ZFC machine endpoint.” Source 17 supplies a new Python **reference** complete checker and ordinary correctness argument, not those absent Lean/runtime endpoints. The fresh ground-term interface is a useful architecture candidate for closing that gap.

No existing Lean theorem is refuted. Existing ordinary source-13 complete environment tableau and source-16 complete Hilbert checker overlap at the correct target theory; the new clausal reference offers a different representation with explicit front-end costs. Its state advantage is presently unmeasured. The 270-state full-grammar experiment is a compiler control and openly exceeds the earlier 269 benchmark; its decisions/framework/boot costs must remain charged, with no unsupported subtraction to 243.

## Actionable next work

First preserve the working complete 253-state frontend and the complete reference checkers as controls. The next useful independent formal component is a checked signed-clausifier with a dependency/satisfaction theorem, followed by a small verified ground trace checker. Compile the whole finite-source or PSC front end against one common backend, including matrix reconstruction, terms, search and boot. The PA table construction can make the old reduced-calculus rejection durable, but cannot itself shrink a correctly calibrated machine. The tagged Capture repair is useful only if the finite class-theory branch is actually selected and all its input axioms/elimination costs are measured. No change to the current correctness boundaries is warranted by the finite runs.
