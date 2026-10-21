# Independent review of the next simplification proposals

Status: ordinary mathematical audit, source inspection, and independent finite corroboration. **No new Lean file was compiled or kernel checked.** `lean` and `lake` were not found on the review environment's PATH. The review executed only newly owned review code and read incoming Lean/JSON as data. Older sealed packets and production files were not changed.

## Conclusions

1. **Terminal drain:** the weakened theorem is mathematically sound under its stated deterministic partial-transition semantics and positive successful blocks. The derivative changes exactly the advertised premise and preservation base case, plus attribution/namespace documentation.
2. **Home return:** the fixed-table word contract, output orientation, arbitrary right-frame preservation, all-natural gap guard, and physical clock are sound. A real accelerated symbolic run now confirms the proposed 62.08% reduction in abstract interpreter iterations, not merely an estimated cut ledger. This is not a smaller machine, shorter concrete computation, or measured kernel speedup.
3. **Fresh named padding / sparse lower theory:** the fresh universal is valid with the displayed valuation and existing freshness theorem. The narrower lower theory supplies exactly the equality-free seed instances needed by the existing quotient/completeness argument. The fully decoder-free named-bundle theorem remains an identified formalization obligation, not an implemented theorem.
4. **Canonical WF summaries:** the recurrences and completion-rank witness preserve the exact existing all-node WF proposition. Their generic evaluator and soundness proof remain to be implemented; a completeness proof is optional for initial adoption. Python reproduction of all three arrays is corroboration only.

No mathematical counterexample was found to a correctly scoped proposed theorem. Concrete counterexamples below show why omitted conditions and broader descriptions would be unsound.

## 1. Terminal-drain interface

Inputs: `terminal_contract/README.md`, the pinned `input/PositiveStutter.lean`, `TerminalDrain.uncompiled.lean`, and the finite checker/result.

Let `stepA : A → Option A`, `stepB : B → Option B`, and `R : A → B → Prop`. A successful run of length zero returns its start, and a successful positive run cannot step past a `none` successor. Assume:

- For every related pair and every source successor, there exists a **strictly positive successful** target block to a related source-successor/target-endpoint pair.
- At a related pair, source terminality implies **eventual** target halting.

Then related pairs are equihalting. Preservation is induction over a finite source run, using terminal drain only at its last configuration. Reflection is strong induction over the length of a target run ending at an actual terminal configuration. A source successor supplies a positive target prefix. Determinism and terminality imply this prefix cannot extend beyond the terminating run; its remainder is strictly shorter. The reflection proof therefore uses only `advance`, as claimed.

No uniform bound on block lengths, reverse simulation, fairness condition, functionality of R, or relation preservation throughout intermediate target states is needed. A source terminal may relate to a target with a finite cleanup suffix. Immediate terminal equivalence implies the drain condition but is strictly stronger.

### Boundaries

- Zero target blocks fail: a self-looping source can relate to a terminal target and repeatedly use zero steps.
- Omitting drain fails for preservation: a terminal source can relate to a looping target, with `advance` vacuous.
- Absorbing total-step semantics are different. A looping source can take positive steps against the target's absorbing halt self-loop forever. The partial-successful-run argument cannot be silently reused there.
- Determinism of the target matters: in a nondeterministic target a branch may halt while another branch supplies arbitrary matching progress.

The source SHA-256 and Git blob ID match the pin. Apart from the attribution header, the derivative is exactly the original with the terminal field weakened, the preservation base case changed, and namespace/doc wording updated. In particular, reflection is unchanged. The embedded `#print axioms` commands have not been run for the derivative and are not an axiom report.

Independent enumeration used bounded finite orbits rather than the proposal's reachability implementation. It reproduced all counts: 36,864 system/relation triples; 15,910 satisfying advance; 7,273 satisfying advance and drain; 1,506 satisfying the relaxed contract but not immediate terminal agreement.

## 2. Whole-tape home-return macro

Inputs: `runtime_contexts/profile_home.py`, `symbolic_owned.py`, `verify_home.py`, their JSON results, the fixed table, and `HomeReturn.uncompiled.lean`.

### Exact concrete statement

The left list is ordered from the head toward the left exterior. Enter at state 2 with the head on its first cell. Let its nonblank portion be `W = U ++ [true]`, followed only by blanks, and let the entire right list R be arbitrary. Starting with zero streak 0, W must contain no eight consecutive false cells.

The required table rows are the eight left-moving scanner states `[2,3,5,9,15,23,34,50]`: a true cell is preserved and resets to state 2; a false cell is preserved and advances through the chain, with the eighth entering state 75. State 75 preserves false while moving right and preserves true while moving right to 84.

The endpoint is state 84, head on the right list, left list `[true]`, right list `reverse(U) ++ R`, modulo the usual trailing blank representation. The entire tape contents are unchanged, not merely a selected suffix or current symbol.

For the fixed rows, the physical clock is `|W|+18 = |U|+19`: scan W leftward, take eight leftward blank steps, nine rightward blank steps, then one rightward marker step. The macro never reads R. For `|W|=1`, it stops just before the first cell of R; for longer W it stops earlier, in the preserved reversed U.

The exterior on the left must be blank, not arbitrary. The generic `LeftWord.sound` theorem has arbitrary left/right frames, but the home-return theorem intentionally specializes the left exterior to blanks.

### Symbolic guard

Segments denote natural lengths `a*n+c`. Trimming trailing false runs only removes exterior blanks, including unbounded blank padding. Inside W, positive-coefficient false runs are rejected. True runs may have positive coefficients; setting n=0 removes the largest possible number of true cells. Increasing n inserts only true cells and cannot create a new eight-zero block. A zero-constant true run must not reset the zero counter at n=0. The implementation gets this case right. Literal final true guarantees the marker exists even at n=0.

The hypothesis that coefficients/constants are naturals is inherited from the Lean segment type and owned constructors. A future untrusted serialized checker should validate this rather than accepting arbitrary Python integers.

### Replay and measures

The initial profiler resumed the old, normalized-equivalent symbolic endpoint after each verified cut. By itself its counts were a cut-ledger result, not execution of the accelerated state representation. This review raised that distinction. `verify_home.py` now actually resumes the macro-produced state, and independently reaches all 6,176 expected branch endpoints with exactly 15,673 macros plus 910,678 ordinary abstract steps, totaling 926,351. The old count is 2,442,801, so 1,516,450 abstract iterations are removed (62.0783%).

These are abstract interpreter iterations; some represent no concrete transition and some summarize many. They are neither concrete machine-time savings nor Lean kernel timing measurements. Other ordinary-step assumptions, including register-box validity and the existing box lemmas, are unchanged. The home macro itself is independent of the box oracle.

The two rejected actual candidates have empty left lists and a true first right cell (paths `11011` and `1111110`, the latter's zero branch). They are conservative fallbacks, not failing accepted cases. An optional separate 18-physical-step boundary macro could cover them; it is not needed for the present result.

Independent review tests used absolute tape coordinates and the literal table, not the symbolic interpreter: 16,252 full-tape word/right-suffix tests and 3,280 affine-word instantiations, including true runs that disappear at n=0. They also demonstrate an unsafe omitted-guard case: `W = false^8 ++ [true,true]` can return to the wrong marker. The guard is sufficient, not necessary for every isolated word.

### Formal caveat

`HomeReturn.uncompiled.lean` exposes the actual remaining obligations as hypotheses: a positive concrete boundary theorem and an all-n shortcut theorem. Its generic boundary premise asserts only positive reachability, not an exact duration. Accordingly the fixed-table clock must not be attributed to that abstract theorem without a separate clock premise/proof. The author corrected this documentation distinction in the final draft. The generic hook is not a completed verified accelerated interpreter.

## 3. Fresh padding and the named lower kernel

Inputs: `calibration/FreshPadding.uncompiled.lean`, `NAMED_KERNEL.md`, and pinned source definitions/theorems.

The construction `pad ψ = ∀(enc ψ) ψ` is valid because the existing `Code254GIC.occurs_lt_enc` theorem bounds **every named label**, including bound labels, below its encoding. Reusing this theorem and `not_free_enc` avoids a redundant structural induction. Satisfaction depends only on free variables; changing `enc ψ` therefore cannot change ψ's truth value. The reverse direction instantiates the universal with `e(enc ψ)`. The explicit valuation is essential context: there is no valuation `Nat → empty`, so no empty-domain consistency inference is hidden.

Padding adds one formula constructor rather than the four added by literal double negation. It preserves equality-freeness definitionally, and its code is greater than 1, hence distinct from both fixed role labels 0 and 1. This is a local syntactic/proof simplification, not a claim that the full lower endpoint becomes constructive.

The sparse theory contains the named bundle for each equality-free padded matrix at roles 0 and 1. Its derivability follows using `th_eqFree`, `enc_bundleNF`, and the unchanged C222 bundle constructor with its gates. Models of this sparse theory provide exactly the seed instances demanded by `fullSeed_quotient`. `c222_complete` already allows an arbitrary theory T with these derivability/no-model obligations, so the old theory of *all* interpreted derivable formulas is unnecessary for this lower argument.

The first-stage draft deliberately retains two `sat_encode_decode` invocations and the old decoded `seed_of_bundle`. Its source does not yet implement the decoder-free theorem.

### Exact decoder-free obligation

For named `bundleNF a b k m`, the proposed equivalence with the corresponding SeedProp is correct with:

- distinct roles `a ≠ b`;
- container label `k ≠ a` and `k ≠ b`;
- freshness `¬ Free k m`;
- an explicit valuation e.

No irreflexivity or equality-free assumption is needed for this **named semantic equivalence**, because genuine named Bottom is interpreted as False. Existential extraction from the negative universal form remains classical. Equality-freeness remains needed in the separate derivability adapter, and irreflexivity remains needed in the lower completeness/quotient chain and any raw encode/decode adapter.

The matrix-transport, request, and closure normalizations stated in `NAMED_KERNEL.md` reproduce the existing environmental identities without decoding. Their combination yields the exact ordinary-role seed property. This is a sound design, not a completed Lean proof.

Independent checks covered 114 sampled named formulas, 14,820 padding/model/valuation combinations, and 8,320 fresh bundle/Seed equivalences, including 6,208 with reflexive membership. Two concrete negative controls establish genuine hypothesis boundaries:

- Without freshness: domain `{0,1}`, empty membership, valuation constantly 0, roles `a=0,b=1,k=2`, matrix `x0=x2`. The bundle is true but SeedProp is false.
- Without distinct roles: domain `{0,1}`, membership `{(0,0),(1,0)}`, valuation constantly 0, `a=b=0,k=2`, matrix `x0∈x0`. Again the named bundle is true but SeedProp is false. The separate worker also records an irreflexive four-element example.

Raw upper soundness must remain over **all** natural codes and its original roles, including code zero and `a=b`. Genuine Bottom is not syntactically the decoded code 1; its semantic alias needs irreflexivity. Nothing here licenses deleting the raw decoder globally, removing junk-code cases, or claiming import/build dependency removal before module extraction.

## 4. Canonical all-node well-formedness

Inputs: `wellformedness/PROOF.md`, `RankScopeContract.uncompiled.lean`, the finite prototype, and the exact `RMEquiv.WF` definition.

For a node with CAR a and CDR d, the canonical natural demands are:

- `B(n)=max(b(a)-1,b(d))`.
- `C(n)=max(c(a),c(d)-1)`.
- Optional comparison height `H(n)=1+max(h(a),h(d))`.

Subtraction is truncated. CAR consumes one break but no continue; CDR consumes one continue but no break. A decrement leaf has break demand 1. The formulas are the least local solutions to the original inequalities, not claims about exactly attainable runtime exits.

A child-before-parent completion number supplies a simpler height witness: positive rank for each node, with every child rank smaller and every leaf height zero. At most nn nodes complete, so root height is at most nn, stronger than nn+1. The final zero-based Lean interface adds 1 and constructs the original WF record from decreasing ranks, recurrence equalities, legality, and the single checked scalar condition `rank(root) ≤ nn`; its mathematical argument is sound. A global cardinality proof is not needed in this interface.

The derived traversal must validate every ID below nn, not only reachable nodes; preserve edge bounds and positive break/continue levels; reject active-stack cycles; memoize shared completed subgraphs; and require zero root demand. The prototype does these. Its worklist has nn initial visits, at most 2nn child visits, and nn completions, at most 4nn pops. This is not a kernel-time bound.

For the first implementation, arbitrary-fuel soundness plus a final root-rank check is enough: acceptance supplies the complete-table invariant, and every incomplete or out-of-fuel run fails closed. Neither a generic acyclic-graph termination theorem nor a proof of the 4nn sufficient bound is a prerequisite for this soundness implication.

Optional completeness relative to WF follows because an existing decreasing-height witness excludes all bounded node cycles. Induction in completion order makes canonical B/C no larger than any WF witness, so their root values vanish. Soundness reconstructs the original WF witnesses. Thus the intended checker preserves the exact acceptance criterion once its generic invariant proof is implemented.

An independent Kahn readiness queue reconstructed all 487 source nodes through the four override layers and reproduced every supplied H/B/C entry, including root `(178,0,0)`. It did not execute the fetched generators. All-node coverage retains 226 unreachable nodes, as required. An unreachable self-cycle would leave root behavior unchanged but invalidate current WF, so deleting those checks would silently weaken the theorem.

The root-support alternative is correctly separated: it needs a new supported theorem or proved transport through a graph with trivial unreachable nodes. It is not a free optimization of the present WF checker. Likewise, supplying a topological order remains a certificate and cannot be counted as the certificate-free derived traversal.

## Reproduction and scope

Run only the owned review scripts:

- `python -I -B review/check_independent.py`
- `python -I -B review/check_named_kernel.py`

Outputs: `independent_result.json` and `named_kernel_result.json` in this directory. They are finite corroboration, not a proof of any universal theorem, elaboration success, axiom audit, production integration, or compiler performance.
