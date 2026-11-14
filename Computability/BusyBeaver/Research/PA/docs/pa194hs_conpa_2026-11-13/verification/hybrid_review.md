# Independent review of the PA194H / PA194HS argument

## Verdict and scope

I independently checked the new command algebra and proof compiler in `research/theory/hybrid/proof_hybrid.tex`. I found no mathematical defect in the final hybrid command argument. The conclusion is an ordinary mathematical PA-provability statement using the explicitly retained numerical-calculus/PA calibration and the stated source/physical contracts. This review is not a new Lean or Rocq kernel verification and does not complete the repository's separate iPRA endpoint.

The exact graph novelty checks passed for both literal tables against every one of the 51 recognized current 194-state byte forms, representing 28 graph classes at ProveIt commit `1e407ae841e4666f932777fad977ba784ebbcfd5`. The comparison uses full canonical tuples under arbitrary state renaming, root changes, reflection and global read/write-bit complementation. The receipts are `novelty_PA194H.json` and `novelty_PA194HS.json`. In particular, the speculative `MPH` research input is not one of these graphs.

The independent physical replay belongs to the construction workstream; this review examines its mathematical role and the new command/source argument, rather than relabeling the other checker's output as an independent rerun by this reviewer.

## Exact identities checked

Let `p(a,b)=((a+b)(a+b+1))/2+b`, `[a;w]=p(a,w)`, `I(a,b)=4p(a,b)` and `U(i,a)=4p(a,i)+2`. A store is `(t,w,d,h)`. Shift halts exactly when `h=1`; otherwise it returns `(h,tl(w),d,hd(w))`. Successful `MP_x`, with `b=d+x`, returns `(b,w,b,0)`, and failure returns `(0,w,b,0)`.

### AX indexing

The unchanged AX command produces top `K` and stack `[q1,...,q9,t;w]`, with `d=h=0`. The first eight generated heads have residue zero modulo four, and `q9=U(old_d,old_h)` has residue two. None can equal one. Direct indexing gives:

* AX followed by nine Shifts returns `(q8,[t;w],0,q9)`.
* AX followed by ten Shifts returns `(q9,w,0,t)`.

These Shifts test the initial zero and the generated heads, never the arbitrary saved top. This establishes totality of those words even on dirty incoming stores with `t=1` or `h=1`.

### Push, Pop, and Discard

For `Push = AX_0,0,0 ; S^9 ; MP_0`, the final implication has residue zero and is compared with the universal head of residue two. It therefore fails and returns exactly `(0,[t;w],0,0)` for every incoming store.

For `Pop = AX_0,0,0 ; S^11`, the first ten Shifts are safe, and the eleventh tests the saved top. Thus `Pop(t,[a;w],d,h)` halts exactly when `t=1`, and otherwise returns `(t,w,0,a)`.

For `Discard = MP_0` with `d=0`, the candidate conclusion is zero. Both branches return `(0,w,0,0)`, even when the implication comparison succeeds through `I(0,0)=0`. No failure assumption is needed.

### Cantor zero collapse

The argument never relies on an injective representation of list length. Although `[0;0]=0`, the identities `hd([a;w])=a` and `tl([a;w])=w` remain exact at `(a,w)=(0,0)`. The reserved-zero invariant is an explicit symbolic wrapper over an arbitrary tail, not a claim that a new zero cell is distinguishable from the infinite decoded zero suffix.

For the soundness annotation, `tl(w)<w` when `w>0`; hence the canonical finite stack can be annotated until it first reaches zero. Popping zero supplies the fixed derivation of numerical truth code zero. The inherited calibration gives this construction in explicit bounded arithmetic.

### Generalization and selectors

`Offset_i=MP_i` takes `(0,w,0,0)` to `(0,w,i,0)`, including `i=0`. Therefore

`Push ; Offset_i ; S ; AX_i,0,0 ; S^10`

sends `(a,w,0,0)` to `(U(i,a),w,0,0)`. The intermediate Shift tests a zero cache, then loads `a`; AX consumes it as the generalization input before the cache is tested again. This calculation remains valid at `a=1`.

For ordinary head index `1<=j<=7`, the selector

`Discard ; AX_A,D,H ; S^(j+1) ; Pop^(9-j)`

returns `q_j` and restores the old stack and zero offset/cache. After the Shifts the remaining explicit tail has `9-j` entries, the last being the saved zero. Each Pop preserves the selected head and consumes one of these entries. The selected head has residue zero, so no unintended halt is possible. The diagonal, gate and dominated-rho selectors all have the stated exact parameter assignments. In particular the rho selector sets the old offset to `u` and chooses AX offset `a-u`, using the required hypothesis `u<=a`.

### MP suffix

From `(0,[a,I(a,b),0;w],0,0)`, the first Shift gives `(0,[I(a,b),0;w],0,a)`. The second halts if `a=1`; otherwise it gives `(a,[0;w],0,I(a,b))`. `MP_b` then succeeds and gives `(b,[0;w],b,0)`. Pop halts if `b=1`; otherwise it returns `(b,w,0,0)`.

The explicit zero under the two premises is essential. Without it, Pop would consume an arbitrary old stack entry. The new compiler reserves it before compiling the major and minor premises. All-zero aliases cause no exception to the calculation.

## Proof-tree induction and dirty stores

The stated invariant is appropriately strong: from every `(t,w,0,0)`, the compiled proof word either halts early or returns its conclusion with unchanged `w` and cleared `d,h`. Axiom selectors satisfy it, generalization preserves it, and the reserved-zero major-first MP block satisfies it by the suffix identity above. Early halts are propagated rather than incorrectly discarded in the induction.

For a proof of numerical code one, the word

`AX_0,0,0 ; W_p ; Pop`

halts from every store, including arbitrary old `d,h,t,w`. The first AX resets `d,h`, and the proof invariant accepts its resulting arbitrary top and stack. If the proof word does not halt earlier, Pop detects the concluded top one before relying on the underlying tail. This is the correct interface for a scheduler that carries state between trials.

## Scheduler and cofinality

The original draft referred to the inherited exhaustive scheduler. On review, an explicit cofinal packing argument was added. The literal positive continuation encoding is

`B_S(z)=p(0,z)`,
`B_MP_x(z)=p(1,p(x,z))`,
`B_AX_c,x,y(z)=p(c+2,p(y,p(x,z)))`,

with the AX field order **y then x**, as in the inherited literal decoder. The positive continuation encoding is `E([])=0`, `E(c::w)=1+B_c(E(w))`.

For a universal halting word encoded by continuation `z`, prefixing `AX_k,0,0` gives fresh-candidate code `n_k=p(k+2,p(0,p(0,z)))`. These codes are unbounded in `k`. The prefix may change the carried store, but the following word works for every store. Thus omitting initial candidates zero and one does not matter.

For a positive continuation `l`, the decoder uses `l-1`; its residual continuation is at most `l-1`, by the bounds on Cantor projections. Every prior trial therefore finishes or halts. The fresh candidate counter then advances by one. A bounded induction over candidate numbers reaches a chosen `n_k` unless an earlier halt occurs. Arithmetic source loops have the inherited terminating finite bounds. All objects and constructions are finite and their correctness can be proved in PA, without a reflection principle or a nonstandard-model appeal.

## Soundness and literal halting

At clean startup, visible top, cached head and every canonical stack entry have numerical-calculus proof annotations; the initial values are zero. No theorem annotation is required for the arithmetic offset. AX adds unchanged axioms and the generalization of an annotated cache. Successful MP applies the numerical MP rule, failed MP supplies truth, and Shift moves annotations. A Shift halt exposes an annotated proof of one.

The inherited numerical-calculus calibration converts that finite derivation to a PA refutation. Conversely, a PA refutation yields a numerical refutation, then the universal halting word above. This gives the two source-level implications without assuming PA is sound or consistent.

Positive source-to-physical segment durations and exact startup supply the literal machine connection. A hypothetical first literal halt at time T is incompatible with T+1 completed nonhalting source steps, because their concatenated positive segments extend beyond T and determinism forbids passing through a terminal halt. This is a bounded finite comparison formalizable in PA, not an inference from long empirical nonhalting.

The physical evidence must refer to the final folded table, include all source outcomes and the complete tape frame, and check the exact blank initialization separately. The supplied corpus's 1,361-step startup counterexample demonstrates why the last requirement cannot be inferred from source contracts alone.

## Issues found and corrected during review

1. The scheduler link was expanded from a reference to an explicit positive-tail encoding, residual-decrease argument and unbounded candidate family. The verified literal AX field order is y then x; the proof uses that order.
2. The original semantic-distinction examples used a contradiction-bearing input and described the resulting difference as actual reachable behavior. That wording was narrowed to specified command behavior. The MP example was improved to `MP_2` on `(0,w,0,20)`, using `I(0,2)=20` and the theorem `2=U(0,0)`. PA194C returns `(0,w,0,2)`, while the hybrid returns `(2,w,2,0)`. The Shift example with top one is retained only as an algebraic distinction between functions.
3. The document correctly credits no-push MP, cache-only Shift and symmetric equality as supplied components. Current-corpus novelty is the certified combination, its new compiler and its new literal graph; global historical novelty is not claimed.

## Remaining dependency boundary

No new defect remains in the command argument after these changes. Acceptance of the complete PA theorem still relies on the retained ordinary numerical-calculus/PA refutation translations, the inherited source scheduler and arithmetic routines, the new exact source splice, the final universal physical contracts and the independent exact startup checks. The report should continue to name those dependencies and avoid representing the result as an end-to-end kernel theorem or an iPRA proof.
