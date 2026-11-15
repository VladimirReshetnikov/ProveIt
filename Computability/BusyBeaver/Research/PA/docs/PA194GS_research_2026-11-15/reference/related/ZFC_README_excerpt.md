# Smaller machines for Con(ZFC)

The literal [K215 machine](candidate-k215/README.md) now has **compiled Lean and Rocq
correctness proofs**: blank-tape halting iff ZFC has a finite refutation, and
nonhalting iff syntactic consistency of ZFC. Lean's original fresh build checked
204 project modules; the [current simplification checkpoint](k225-formal/verification/k215/simplification/phase8/README.md)
checks a 188-module closure and two explicit clients with standard axioms only.
Unchanged modules retain exact predecessor source, dependency, object and log bindings.
Rocq's 237 selected sources,
four closed endpoint reports and recursive `coqchk` pass. See the
[formal verification record](k225-formal/verification/k215/README.md).
The earlier target
of214 or fewer states remains a research direction, rather than the present
completion criterion. The original target was fewer than254 states and equivalence
provable in PA. An earlier search phase also permitted consistency of a
well-understood stronger theory, as clarified on 17 October 2026. Each candidate
must state the assumptions used for its two unprovability directions;
consistency alone must not be confused with arithmetic soundness. The
external Lean equivalence with Con(ZFC) is now proved for the exact
[240-state machine](rotation240_binary.md), improving the earlier checked
[244-state](compensated244_binary.md), 245-, 246- and 252-state endpoints.
**PA now proves the equivalence for that exact 240-state machine:**
[`BinaryConsistencyRotation240`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/BinaryConsistencyRotation240.lean) checks
`𝗣𝗔 ⊢ Con(𝗭𝗙𝗖) ↔ ¬Halts(M₂₄₀, blank)` (already in IΣ₂, and likewise for ZF), with
the standard axioms only.
The current simplification work is Lean-only; the checked Rocq endpoint is preserved.
An intended set-theoretic meaning is optional: any effectively presented
theory or proof calculus is eligible once its consistency calibration is proved.
The complete compiled search, including its data and initialization, is the
cost measure that decides whether a candidate improves the baseline.

Stronger targets must stay within well-understood assumptions widely believed
to be consistent (user clarification, 17 October 2026). Preferred benchmarks
are finite consistency iterations over ZF/ZFC and standard inaccessible-cardinal
assumptions. A shorter encoding alone does not justify an unfamiliar increase
in consistency strength. For an artificial calculus T, identify an accepted
benchmark S and prove both Con(S) → Con(T) and Con(T) → Con(ZF), with the
formalization base stated. This supplies a consistency upper bound as well as
the lower bound needed for the independence argument; no absolute consistency
proof is claimed. Require a concrete encoding benefit before increasing the
benchmark strength.

The [**240-state candidate**](candidate-rotation240/README.md) from `e5c2b3337e`
combines another source-loop rotation with a 72/90 state fold. Fresh replay
passes all 8,386 runtime cases, 2,322,575 symbolic rules and all 480 transition
rows, with exact 409,691-step blank initialization. Its ordinary consistency
argument is independently reviewed. The [exact-table external Lean endpoint](rotation240_binary.md)
now proves blank-tape halting equivalent to ZF/ZFC refutation and nonhalting
equivalent to the corresponding consistency statements. Its nine probes and
nine typed callers pass with zero warnings. The internal PA equivalence for
this exact 240-state machine is now checked too
([`BinaryConsistencyRotation240`](../../../../Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/BinaryConsistencyRotation240.lean), 19 October 2026). See the [intake reconciliation](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-170.md).

The primary contender is the [**215-state machine**](candidate-k215/README.md).
It combines the command-local field reader and command ordering of
`d59b441882` with the partial selector from `6ec69081ca`. Both earlier
marker folds remain valid. The source has 202 distinct subtrees; reallocation
deletes one state and changes 35 retained rows, giving 430 binary rows
including initialization. All 6,176 arbitrary-natural runtime cases pass,
with 1,698,790 symbolic rules, every row covered and minimum positive
duration 6. Independent replay checks every one of the 95,714 blank steps
in both native and dense formats and the entire final tape.

The complete ordinary proof gives
`ZFC ⊢ (¬Halt(K215, blank) ↔ Con(ZFC))` and reaches the requested 215-state
target at the ordinary mathematical level. The exact-K215 external Lean and Rocq
endpoints are now compiled and audited. The internal PA endpoint remains open; the
formal 240-state result above retains its separate status. See the
[proof and reproducible evidence](candidate-k215/proof.md).

The [partial-selector K216](candidate-k216/README.md) remains the immediate
physical parent. [Batch 197](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-197.md)
imports the two distinct [command-permuted K216 alternatives](candidate-k216/alternatives/permuted/README.md)
from `d59b441882`; all ten selected fresh checks pass. The 215 composition
has separate exact-table checks, and neither submitted 216 table is
relabelled as the smaller result. [Batch 196](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-196.md)
preserves scanner/encoding/clean-seed research from `d3d6b8c14e`, with nine
fresh selected leaves and explicit failed-search boundaries. All three ZIPs
are imported and retired.

The [previous K217](candidate-k217/README.md) supplied the 69/400 fold;
K216 adds the compatible 164/183 fold. Both persist in K215, with the same
accepted dominated-rho8 calculus calibration.

The later [exposed-marker presentation](candidate-k217/presentations/exposed-marker/README.md)
from `673c87a878` is exactly the same machine under `188→213→210→188`, with
the identical source. All 434 rows and source-prefix roles compare, and its
native bytes exactly match the independent candidate025 already preserved
with K217. The six-versus-nine parent-row edit count reflects label choices;
the savings cannot stack. Its separate fixed1,3-core appendix costs 211 source
subtrees and is not part of the machine. See
[batch 194](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-194.md).

The former [primary K218](candidate-k218/README.md) from `c4568161bf` remains
published with its 205-node source, state 85/212 fold, complete runtime/startup
and same-size row157 variant. Its source roles differ from the new dominated
layout, so the two savings cannot simply be counted twice.

The [contextual 218 alternative](candidate-k218/alternatives/contextual/README.md)
from `3c7c3aa5a3` also passes six fresh checks: 6,167 cases, 1,514,325 rules,
all 436 rows and a complete 312,701-step startup. Its graph is distinct, but
its final fold shares the same two source roles as the former primary K218; the savings
do not stack. Its own row157 variant also remains at 218. See
[batch 190](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-190.md).

[Batch 191](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-191.md)
adds a [dominated-rho8 218 alternative](candidate-k218/alternatives/dominated/README.md):
restricting U≤A preserves every native theorem while shrinking the source to
203 distinct subtrees. All eight fresh checks pass, including 6,176 runtime
cases, 1,616,989 rules and exact 312,605-step startup. Existing final contextual
folds do not directly stack. Two further complete 218 variants
[omit a redundant MP push](candidate-k218/alternatives/omit-zero/README.md) or
[permute command tags](candidate-k218/alternatives/dmn/README.md).
The reports also add calibrated H/PW and self-vacuity bases, codec transport
and concrete startup obstructions. Their four archives are imported and retired.
The later Source 152 construction builds on the dominated layout and is now
accepted as the primary 217 above.

[Batch 193](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-193.md)
imports the two additional reports at `1e87618cf2`: residual-counter and
negative-equality calibrations, full Peirce/T/B countermodels, inverse
detachment, shifted codecs and shorter MP returns. Eleven selected fresh
leaves pass. The [cache-return composition](candidate-k217/research/cache-return/README.md)
has 4,728 leaves with exact source/startup checks, but remains at 217 states;
its bounded 645,408-specification fold search finds no survivor. Its modified
universal runtime remains unexecuted. Both source ZIPs are imported and retired.

The two [batch-189 research reports](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-189.md)
retain useful arbitrary-clean-seed and fixed-power-of-two scheduler theorems,
two freshly verified 219 layouts, and explicit failed startup repairs.
The [all-start obstruction](k218-continuation-search/all-starts/README.md)
shows that choosing another existing start cannot repair the exact delete301
217 table. All three new archives have been imported and retired. A [reachable repair
counterexample](k218-continuation-search/row36-repairs/README.md) rejects the
proposed row36 repairs for the accepted source. A [source-reassociation
search](k218-continuation-search/rotation-folds/README.md) tests 282,416 fold
specifications after 25 closed rotations without a survivor; its bounds do
not imply minimality.

A [217-state marker relay](k218-continuation-search/marker-relay/README.md)
repairs one bootstrap route and has proved local return lemmas, but its full
runtime attempt fails at source ordinal 4569. A literal counterexample
confirms that failure; this table is not an accepted contender. The
[retagging obstruction](k218-continuation-search/marker-relay/retag-obstruction/proof.md)
explains why changing that short backward jump from `CC2` to `CC3` cannot
preserve the same instruction order and control-flow edges.
A separately reviewed [protected-tail seed theorem](k217-protected-tail-seed/README.md)
shows that the enumerator, starting at candidate zero or one with an empty
proof-list pointer, never reads its initial stack. This permits arbitrary
initial stack contents when the current formula and cache are theorems.
It supplies an ordinary startup route after the relay's complete AX suffix,
conditional on the still-missing correct binary runtime.

On the formalism side, [K/S with mixed commutation](k218-ks-mixed-commutation/README.md)
has a reviewed ordinary equiconsistency proof: co-translating formula codes
and numeric labels preserves the literal gated bundle and gives finite
refutation translations in both directions. It needs no separate quantified
stability axiom. [K/S plus quantified stability](k218-quantifier-stability/README.md)
has a separate ordinary calibration, with an independently checked finite
proof DAG. The respective [mixed-row](k218-ks-mixed-commutation/source-pricing/README.md)
and [K/S+QS](k218-quantifier-stability/source-span-dp/README.md) source searches
reach 209 and 208 distinct subtrees. [Context-aware allocation diagnostics](k218-context-allocation/README.md)
explain why these source counts do not directly translate to machine savings.
Neither theory has yet produced a smaller verified machine.
The [K/S-only gap](k218-ks-mixed-commutation/ks-only-gap/README.md)
isolates the remaining quantified commutation problem. The separate
[restricted rho8 with explosion](k218-hf-efq/README.md) investigation derives
closed-theorem double-negation elimination, but has no full consistency
calibration or machine saving yet.
The [five-value model](k219-fourth-parameter/finite-matrix/README.md)
now excludes every membership-fourth restriction of rho8, even their union,
while retaining the other native rows; adding K or explosion is outside
that model's scope. A separate [three-value code-dependent model](k218-k-membership-obstruction/README.md)
now also rules out K plus `R(A,B)`-fourth rho8, even with quantified stability.
Its [all-natural Lean proof](k218-k-membership-obstruction/lean-model/README.md)
now passes with 21 standard-axiom reports and zero warnings. A separate
[syntactic invariant](k218-k-membership-obstruction/identities/README.md) also
rules out K plus that restricted row even with every identity, including
`F → F` (code 16). The latter proof excludes quantified stability; combining
both additions remains outside these results. No machine-state saving follows.
