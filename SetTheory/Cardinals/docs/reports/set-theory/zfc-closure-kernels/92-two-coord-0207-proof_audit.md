# Independent proof and runtime audit

This review concerns the current ProveIt `candidate-routing245` source and the reconstructed source 68 package. It also independently reviews the FC13S/FC14S mathematical contribution produced in this session. It is an ordinary mathematical/source review. No Lean or Coq compiler was run by this reviewer.

## Current baseline and exact theorem boundary

The current canonical table has 245 working states, 490 rows, blank start state 0, head 0, and a separate halt 245. Its SHA256 is `17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`. In historical labels start 95, dispatcher 96, and halt 254 are used. The standard blank tape is zero everywhere, two-way infinite, and all transitions move L or R.

Current primary repository documentation records an ordinary ZFC-provable nonhalting/consistency equivalence, complete executable universal evidence, and substantial external Lean proofs. The exact 245-state closed Lean endpoint remains open at complete instruction-site coverage and final composition. Its current pieces include exact table/fast lookup, all 6,460 decoder leaves, source bisimulation, register operations, runtime under explicit coverage/initial-frame premises, and the exact407915-step blank frame. The 246-state machine already has a closed external Lean binary/ZFC consistency theorem. Neither that external theorem nor a Python replay is an object-language PA proof. PA internalization remains a separate obligation; the current repository has meanwhile completed its internal ZF/Choice comparison, so describing Choice transport itself as entirely open would also be stale.

Primary paths:

- `Computability/BusyBeaver/Research/ZFC/candidate-routing245/README.md`
- `Computability/BusyBeaver/Research/ZFC/routing245_execution.md`
- `Computability/BusyBeaver/Research/ZFC/routing245_bootstrap.md`
- `Computability/BusyBeaver/Research/ZFC/prefix246_binary.md`
- `Computability/BusyBeaver/Research/ZFC/pa_internalization.md`
- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-164.md`
- `.../intake-164-checker-review.md`
- `.../intake-164-reproduction.md`

Upstream primary audit: `https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/README.md`, together with `design/tm.md`, `design/logic.md`, and `design/settheory.md`. Upstream's three end-to-end Coq statements concern the literal254 table, its calculus, ZF, and ZFC; they do not automatically bind a smaller literal table.

## Sound composition obligations

A changed table must satisfy all of the following, with the same exact inputs throughout:

1. Its complete source tree implements the original program. Ordered leaf-operation equality is insufficient after reassociation: break/continue targets and consumed pointers need the finite source bisimulation. The routed245 certificate has3013 pairs and6024 edges.
2. Register macro contracts must be derived on the proposed literal table. The builder alone admits macro summaries before their separate actual-table derivation. `audit_existing_machine.py` explicitly rederives unary/list/mark/macro contracts before running the affine cases.
3. Instruction correctness quantifies over independent arbitrary primary naturals, arbitrary gap slack, and an arbitrary nonempty finite spare suffix. Both decrement guards are covered unless a separately proved reachable-state invariant justifies an exclusion. A bounded fixture is never a universal guard.
4. Residual pointer normalization must preserve the whole frame, including implicit trailing zero bits. All8390 nonhalting successors have a checked normalization obligation. The frame margin grows by positive decrement and marker overflow; increment appends a spare of value1. These physical conventions differ from the original254 encoding.
5. Positive binary progress is necessary for reverse halting equivalence. Deterministic positive segments from each active frame give unbounded execution times along an infinite register run. Exact final halt writes/moves and whole-tape frame preservation prevent a hidden premature halt.
6. Initialization must reach a complete admissible frame from a genuine blank start. The initial frame is not a free preloaded tape.

For routed245 the endpoint is head−5, marker−6, header176, gap181, physical primaries `[0,0,0,3,0,0,3,0,0]`, logical primaries `[3,0,0,0,3,0,0,0,0]`, and167 spare blocks of value1. Exactly351 cells contain one and all other cells are zero.

The universal8391 cases and2312645 whole-frame symbolic rules are distinct from the8385 finite C++ fixtures. All490 transition rows being exercised by finite fixtures does not prove arbitrary future execution correctness.

## Logical calibration and avoided shortcuts

The compact source theory is the attributed nonextensional CP/GIC/irreflexivity theory. The code1 alias is both `Rel(0,0)` and the falsity sentinel; irreflexivity is essential for its soundness. The bundle's gates excluding its fresh code from the two bound names are likewise essential. Consequently a minimalist equality-free theory omitting IR may be equiconsistent with ZFC, but that alone does not license deletion of IR from this existing alias-based checker.

The ordinary consistency comparison is a two-direction interpretation/model construction, not a claim that the compact theory and ZFC have the same models. Upstream constructs quotient membership from set-coded bisimulations in one direction and uses constructibility plus the separate Foundation consistency comparison in the other. ProveIt's current ZFC adapter uses its checked constructible carrier and Choice comparison. It does not assume Choice in an arbitrary ambient reduct.

No unconditional nonhalting or consistency claim follows. Consistency alone is insufficient for both halves of logical independence; any two-sided independence statement needs the stated additional arithmetic soundness hypothesis.

## New reproducible runtime discovery checks

The following searches were performed on the actual245 table and its current8385 finite fixtures, in a separate scratch directory. Every conclusion below is explicitly bounded; none is a state lower bound.

- Ordinary two-state quotient search:119560 inherited-row recipes,54 passed quick probes, zero passed all affected fixtures. The prior delivered120540-recipe sweeps used246-state tables with492 rows, so this is a fresh check of the current245 baseline.
- Arbitrary-action contextual merge synthesis:29567580 candidate single-row actions. Each bit of the proposed merged state could have any retained target, write bit, and move direction; local joins were checked against200800 observed19-cell windows with at most18 steps. No pair satisfied that bounded local criterion. This local condition is a sufficient discovery filter, not a completeness theorem for all valid merges.
- Context-split target deletion:111996 possible hosts,1882676 observed63-cell windows,52757 sampled contexts, at most96 local steps. Four scanner-state deletions met the local criterion; their first chosen route combinations failed full fixtures. These four had a single nonself incoming edge, so the preceding complete ordinary quotient sweep already rules out their unmodified-host recipes under its fixture bounds.
- Context-split incoming-action synthesis:447984 arbitrary action choices,1880694 observed63-cell windows,52731 sampled contexts, at most96 local steps. Three scanner-state deletions admitted7 local recipes in total, all of which failed full fixtures. No combination cap was hit.

Files `local_merge.cpp`, `context_bypass.cpp`, `action_bypass.cpp` and their JSON summaries retain exact scopes. The input fixture is already present in source 68 as `inputs/state_reduction/candidate245-literal-cases.txt.gz`; the uncompressed25MB scratch copy need not be redistributed. `resource_merge_search.cpp` from source 68 supplies the ordinary quotient sweep.

## All-start safe-frame helper

`search_safe_starts.py` accepts any old-label table, with configurable dispatcher/halt/physical map. It reuses an unchanged copy of the existing `safe_seed254.py`; the Safe certificate family is inherited, not new.

```
python3 -B search_safe_starts.py candidate_old.tm \
  --output candidate-safe-starts.json --limit 2000000
```

Use `--stop-after-first` for discovery of one positive initializer. Defaults are dispatcher 96, halt 254, current physical-of-logical map `(6,2,0,4,3,7,8,5,1)`, minimum gap64, and at least one spare block.

Every all-zero prefix is grouped exactly by the state and relative one position immediately after its first one-write. Pure zero-write cycles are proved to stay blank forever, including nonzero head drift. This collapses the245 baseline starts to 8 finite normalized runs and 11 exact blank-cycle starts. At 500,000 steps per normalized run, the helper recovers the known start 95 frame at 407,915 actual blank steps; the other 7 classes reach the finite bound. The successful result is independently replayed from the actual original blank start using a dense interpreter, checking state, head, every one-cell, and zero exterior.

The root theorem permits `C254(T) ∧ C254(H) ∧ Good(W)`, not only `T=W=H=0`. The supplied inherited recognizer handles truth, generalization, implication identity, weakening, ex-falso, equality reflexivity, and unshifted Cantor stacks of theorem codes. It returns explicit finite certificates. A rejected scalar or stack is not proved unsafe; it merely falls outside this sufficient grammar. An arbitrary scalar theorem code placed in a stack field is not necessarily a good stack. For example, the repository's existing notes distinguish formula60 (a theorem) from stack60 (contains buried falsity).

A positive initializer from this helper still needs the proposed machine's runtime simulation and the existing logical program comparison. A negative bounded search does not show absence of eventual admissible frames or different frame invariants.

## Independent FC13S/FC14S review

Reviewed `formalisms_work/frozen_kernel_note.tex`, `frozen_kernel.py`, and the emitted final S clause JSONs. No substantive mathematical blocker was found in the following new steps:

- Clauses 1–2 give coordinate write and retention. Clauses 3–6 give exact implication/falsity, hence `d != I(d,d)`.
- `P(a,b)=C(C(d,d,a),q,b)` has projections `a,b`, so it is injective. The proposed chain using an injective self-map and a point outside its image gives arbitrarily many distinct selector values. The note correctly avoids claiming that a fixed syntactic chain element always differs from both designated selectors.
- Clauses 9–10 give an exact universal-quantifier biconditional for the chosen witness function, not merely its sound direction.
- Freezing evaluates the original matrix at a fixed base with only the input/output coordinates overwritten. This makes the class extension independent of all auxiliary outer selector assignments, even if the original matrix uses their labels as parameters or bound names.
- The reused inner input selector is confined to the subset test, and the reused inner output selector to the emptiness test. Neither local scope includes the matrix occurrence. The expanded formulas agree with the stated EPSC closure and unrestricted support condition.
- Rich class coding is valid in a countably infinite set-coded ZFC model. Before choosing the incidence coding, definable normalized partial-function-graph assignment operations make each `V(-,q)=w` fiber infinite via `P(v,w)`. Excluding the at most two reserved objects leaves enough codes to realize every externally pure-membership-definable class in every coordinate fiber.
- The shared key for the freeze code is exactly `(b,t)`. If `b=P(s,j)`, pair injectivity makes `(s,j)` unique. Therefore the same code needs to satisfy at most one counterexample-witness request, independently of its prescribed incidence class. There is no function-key collision or witness circularity.
- Individual coded classes are definable by ordinary finite pure-membership formulas with finitely many model parameters. Global coding/constructor functions need not be definable in the model. No truth predicate or expanded-language comprehension is used in the EPSC verification.
- Extensionality's XOR clause is correctly expanded and guarded. It has no capture of its two compared coordinates.
- Equality completion by reflexivity, left-Euclidean equality, retained-function congruence, and predicate transport gives a genuine equivalence congruence. An unused template opcode needs no congruence in the retained reduct.

Independent counting of the emitted JSONs, without calling the generator's metric routine, gives:

| Theory | Clauses | Literals | Term nodes | Depth | Max variables | Bits |
|---|---:|---:|---:|---:|---:|---:|
| FC13S native |13|26|230|15|4|1040|
| FC13S completed |23|57|318|15|6|1515|
| FC14S native |14|30|274|15|4|1231|
| FC14S completed |24|61|362|15|6|1706|

All four emitted theories use exactly `V,C,I,A,U,F`; no `W` occurrence remains. Bits were independently recomputed as `3*clauses + 3*literals + 4*term_nodes + 3`.

The lower calibration remains explicitly dependent on source 44's accepted ordinary raw-EPSC hereditary-saturation interpretation, or the direct extensional EPSC calibration in the control. It is not a new complete formalization of those inherited results. The six-function signature permits a padded radix8 ground-term codec, but neither the1515-bit completed template nor this codec is a complete RM/TM compiler. Equality-quotient frontends must compare the1040-bit native template, which is larger than source 44's881-bit native one. The note correctly exposes that tradeoff and makes no sub245-state claim.

## Exact scanner obstruction

`scanner_witness.md` gives the local scanner lemma and a precise eight-step failure for deleting old state 58 and patching old row `41/0` to target 84. During the shared CI/CD mark-and-return phase, the phase zero immediately following the PC joins its trailing zero run. A PC ending in an internal one followed by six zeros therefore presents seven consecutive zeros to the shortened scanner. It reaches state 84 on the internal one and restarts the dispatcher at the first of those six PC zeros. This occurs before the CI/CD effect or the decrement guard can matter.

The portable `scanner_witness.py` independently verifies three full-frame literal examples: zero and positive CD at site 41, and CI at site 649. It also checks the complete prefix-tree site census. Exactly 50 leaf PCs have a six-zero suffix, giving 99 guarded cases, exactly matching the 99 universal affine failures of this contraction. The other 8,292 guarded cases pass the separate audit. These finite witnesses reject the proposed instruction-frame simulation; they do not settle the changed machine's eventual blank-tape behavior.

Although the local condition distinguishes internal runs from the phase-extended trailing run, it does not enlarge this grammar search family. In any finite complete binary tree, the maximum zero-run length equals the maximum trailing-zero length among leaves, by extending the end of a zero run along zero edges to a leaf. All non-CI/CD leaves in this program end in one. Thus a five-zero suffix restriction on CI/CD leaves already implies a global five-zero-run bound. The detailed obstruction is useful evidence, not a newly demonstrated state saving.
