# Independent review of PA194N6

**Result:** no defect found in the new composition of radix-six formula constructors with the no-push MP controller. This is an independent review of the changes and their supplied ordinary mathematical proof, not a new proof-assistant theorem or a reconstruction of every inherited logical proof from first principles.

The reviewed dense machine has SHA-256 `36da42a81d605ccb8b5edae197c7cde311447bd95b9bf1ab771a3e726a41c6f4` and 194 working states. Its native table hash is `63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a`.

## Source and table binding

Independent parsing, without importing the construction compiler, confirms:

- Compared with the supplied M6 table, the only native-row change is `(164,1): (1,R,98) -> (1,R,114)`. The state domain is unchanged.
- The source node map differs only at `node163`: `(node6,node55)` becomes `(node6,node54)`; `node55=(node49,node54)`. The deleted `node49` occurrence is precisely the successful-MP dummy-zero push.
- The old source has 3,795 instructions; the new source has 3,776. The removed interval is exactly `[3756,3775)`, with the only exterior entry `3750 -> 3756`. Every retained instruction and all its successor addresses agree under the stated index relocation. Only the seven retained copy-loop paths change; the entire radix-six axiom emitter is unchanged.
- The surviving seven-instruction copy loop sends `(T,D,X)=(0,b,0)` to `(b,b,0)` in `7b+2` steps. Its two loop invariants in the manuscript are correct.
- The supplied dense label map is a bijection including halt, and every dense row is conjugate to the corresponding native row.

## Interaction with folds and initialization

I independently replayed all **32 local fold cases** directly from the new literal table, checked each endpoint against the corresponding unfolded-parent action, and rechecked all **28 fold-ingress rows** supplying the required left-cell history bit. Native control 164 and its old/new targets 98 and 114 are not fold endpoints. No local fold trace reads control 164. Thus the new redirect does not invalidate the local fold certificates.

A separate finite-support simulator replayed all **58,320 blank-start transitions**. The changed row `(164,1)` is never read before the clean seed. Therefore old M6 and new N6 have exactly the same startup trace. The final control 84, head −2, and every one-cell equal the delivered clean-frame certificate. This directly excludes the bootstrap defect seen in several other source-equivalent zero-return mutations.

The separate literal symbolic receipt reports **4,877 source outcomes**, **1,115,525 symbolic operations**, maximum 397 operations per outcome, four list lemmas derived from literal rows, and minimum physical-duration constant 3. The construction engine reports the same outcome count with 1,531,094 operations and maximum 499. These are symbolic-verifier operation counts, not TM runtimes. The full literal pass was executed by the construction task; this review separately rechecked the table/source/fold/startup bindings rather than rerunning that entire engine.

## Generalized command compiler

The reviewed proof is `mathematics/n6_command_proof.tex`, with `I(a,b)=6p(a,b)` and `U(i,a)=6p(a,i)+2`.

- Generated implication heads and the guarded gate are divisible by 6; the generated universal head is 2 modulo 6 and at least 2. This establishes every claimed safe AX shift without a consistency assumption.
- AX followed by nine shifts returns `(q8,[t;w],0,U(d,h))`; ten shifts return `(U(d,h),w,0,t)`. The counts are correct.
- Push has the exact effect `(0,[t;w],0,0)`. Its final MP necessarily fails by the distinct residues 0 and 2. Pop preserves the old top and pops exactly one stack entry; its last shift is safe even when that top is 1 because `U(d,h)+t>=2`.
- Discard uses MP0 with `d=0`; its two branches both return `(0,w,0,0)` for arbitrary old cache h. Offset i is correct both for i=0 and i>0.
- The ordinary-head selector consumes exactly `9-j` residual entries after `j+1` shifts. The gate selector consumes 10. The dominated-head selector uses `u<=a` to obtain `a=u+(a-u)`; its arguments are all natural numbers.
- Generalization reaches `(0,w,i,a)` before AX and returns `(U(i,a),w,0,0)`.
- The MP proof compiler explicitly reserves its zero below both premises. Its two shifts either halt early when a=1 or prepare `(a,[0;w],0,I(a,b))`. Successful MP followed by Pop returns `(b,w,0,0)`. The argument remains valid when `[0;0]=0`; it does not assume a free list representation.
- Prefix AX0 clears the offset and cache on arbitrary incoming stores. Hence the final refutation word is universal over carried stores, as the non-resetting scheduler requires. The prefixed AXk family gives strictly increasing unbounded fresh candidate codes, addressing the scheduler's start at counter 2.

The soundness annotation must cover all numerical codes, including residues 4 and 5, not merely the hereditary image of radix 4. The retained radix calibration does this with its total arithmetic translation. Its hereditary recoding also changes variable labels and does **not** assume monotonicity: unrestricted rho is derived from the restricted basis before recoding proof leaves. These are the necessary side conditions for the composition.

For maximum clarity, the forward construction should be displayed as `PA-refutation -> C4-refutation -> L6(C4-refutation) -> C6-refutation -> N6 halting word`. The theory author was notified to make this link explicit. No change to the actual mathematical construction was requested.

## Exact formal-status references

All paths below are relative to the pinned ProveIt root:

- `Computability/BusyBeaver/Research/PA/pa194/ipra/README.md`: both machine-specific iPRA reductions remain explicit hypotheses.
- `Computability/BusyBeaver/Research/PA/pa194-dense/README.md`: exact dense/native and parent-quotient standard finite-run halting equivalence is proved; this is not an internal PA/PRA/iPRA theorem.
- `Computability/BusyBeaver/Research/PA/pa194-coverage/README.md`: all 3,673 original source-site checks passed; the theorem concerns standard finite executions and retains an explicit Python source-generation boundary.
- `Computability/BusyBeaver/Research/PA/pa194-clock-source-complete/README.md`: unconditional standard-natural clock/source equivalence is proved, but neither the internal arithmetic reductions nor Con(PA) calibration follows from that theorem alone.

The new paper should retain this separation: the supplied syntactic PA calibration plus the new mathematical composition prove the stated PA-provability claim in ordinary mathematics; executable certificates support its finite implementation obligations; no new end-to-end Lean or Rocq endpoint is asserted.

## Reproducible evidence

`review_structure.py` and `independent_structure_evidence.json` contain the independent table, source, fold, startup and conjugacy checks. `pa194N6_current_novelty.json` independently confirms absence from all 30 current 194 graph classes under state renaming, root changes, reflection and global symbol exchange.
