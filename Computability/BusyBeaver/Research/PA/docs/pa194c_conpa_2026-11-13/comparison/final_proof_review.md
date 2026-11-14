# Final adversarial proof review

## Scope and result

Reviewed `report/pa194c_conpa.tex` against the retained original PA calibration,
the cached-controller command proof, the source-macro proof and the completed
comparison evidence. The source tables and the two physical verification runs
were not rerun for this review.

No mathematical contradiction was found in the composition or in its stated
ordinary PA-provability claim. The report correctly distinguishes that written
proof from a newly compiled end-to-end Lean or Rocq endpoint. Its dependence
on the inherited numerical-calculus proof translations and scheduler remains
substantive; source-graph equality alone would not prove those interfaces.

## Substantive requirements raised and resolved

1. **Zero-scratch boundary.** The initial draft stated the cached tail's
   arbitrary-value loop effect without its command-boundary condition. The
   revised report now explicitly assumes `R_3=X=Y=0`, gives the MP-success
   entry values `T=H=X=Y=0,D=y`, and states `X=0` at Shift entry. These are
   exactly the conditions required by the retained source-macro proof.
   The formula `2t+7h+3` applies to arbitrary `t,h` under that invariant,
   not to arbitrary initial scratch values.

2. **PA-provable correctness, not only finite bounds.** The revised
   finite-trace proof now states that PA proves each symbolic frame contract:
   literal transitions are finite equations, and sweep/list operations have
   fixed induction proofs instantiated by the finite certificates. It also
   explicitly requires nonhalting instruction segments to avoid the terminal
   control and the source halt case to reach it. Primitive-recursive duration
   bounds alone would not have established the PA-internal simulation.

3. **Scheduler coverage.** The revised command proof explicitly inherits
   PA-verifiable exhaustive command-word coverage and a primitive-recursive
   bound for reaching a trial or halting earlier. The constructed refutation
   word halts from every incoming store, so earlier trials need not restore
   the clean store. This is the right completeness invariant.

With these conditions stated, the bounded reverse transport is valid: if
the tape halts at time T but T+1 source instructions all remain nonhalting,
concatenating their positive, terminal-avoiding simulations after startup
produces a nonhalting tape prefix longer than T, contradicting determinism.
The proof requires no assumption of actual nonhalting or of PA consistency.

## Register notation

In the report's logical order `(N,T,W,A,D,H,X,Y,L)`, source registers are

    R0=N, R1=T, R2=W, R3=A, R4=D, R5=H, R6=X, R7=Y, R8=L.

Therefore the inherited boundary condition is equivalently **A=X=Y=0**.
This assertion is about logical registers. Under the physical map
`(6,2,0,4,3,7,8,5,1)`, logical A occupies physical position 4; logical
R3 must not be confused with physical register position 3 (which stores D).
The source macro reference explicitly states the R3/X/Y condition.

Two small readability cautions remain harmless but are worth making explicit:

- AX clears the **offset and cached formula**, `d,h`; calling these “both
  caches” is imprecise because d is the offset.
- “Every word is executed from the clean seed” should mean that the scheduler
  **started at the clean seed reaches each word's trial** (or halts earlier).
  It should not suggest that each trial starts with the same clean store.

## Authoritative M195S8 startup count

The correct number is **59,164**, not 59,194. All these supplied JSON entries
agree, in `pa195_followup_research.zip`:

- `pa195_followup/machine_195s8/startup_certificate.json`: `literal_steps=59164`.
- `pa195_followup/machine_195s8/validation.json`: `startup.literal_steps=59164`.
- `pa195_followup/evidence/scanner8_independent_audit/pa195_scanner8.independent_audit.json`:
  `blank_startup.raw203.literal_steps=59164`,
  `blank_startup.folded195.literal_steps=59164`, and
  `blank_startup.dense_bytearray.literal_steps=59164`.

The reviewed main report's source table also contains 59,164.

## Calibration points checked

- The separate head is unconditional even when the guarded gate returns
  zero; the ten-entry stack compiler accounts for that extra head.
- Pop's early halt at preserved top one is explicit. It is not falsely
  claimed to be total on all tops.
- The MP suffix retains its dummy zero and preserves the arbitrary
  underlying stack. The Cantor zero alias is handled numerically.
- The soundness invariant annotates the visible top, cached formula and
  canonical stack entries; it places no derivability restriction on d.
- The finite-comprehension argument is a syntactic PA proof supplier for
  each formula, rather than a uniform arithmetic truth predicate.
- The formula-code zero exception and the separator-label collision case
  are referred to the retained detailed proofs, not silently discarded.
- PA194C has a different command function and a source 24 instructions
  shorter than PA194/PA194_AD. Independent graph comparison also excludes
  equality under control renaming, root redesignation and tape reflection.

The proof's correct conclusion is the ordinary mathematical statement
`PA |- Nonhalt(PA194C,blank) <-> Con(PA)` for the literal supplied table.
It does not assert a new full proof-assistant endpoint, an iPRA derivation,
a construction below 194 states, or a global state-count lower bound.

## Final editorial resolution

The main report now names logical A as the third scratch register, says AX clears the offset and cached formula, and states scheduler coverage without implying that trial stores are reset. All requested proof and wording clarifications have been incorporated.
