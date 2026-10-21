# Independent review of the guarded arithmetic proof core

## Conclusion

The proposed **1,426 → 367 → 189 checkpoint/proof-graph contraction is sound at the mathematical graph level**, provided the finite checks and the generic semantic lemmas described below are formalized. The concrete finite obligations pass a separately written verifier. The two local loop contracts are valid for **every natural-valued register file**, without clean-scratch assumptions. The zero-input guards are essential.

This is **not** a 189-state Turing machine, a runtime improvement, a proof-kernel certificate, or an endpoint theorem. No Lean/Rocq compiler was located or invoked. No received Python or Lean program was executed. `independent_verify.py` parses literal data and implements an independently authored interpreter and checker; it does not import the first reviewer's checker.

The checked source packet is the archive at commit `aa66d0a33f1f8237a348899eb8095b045a502832`, Git blob `17321c28fc63f3dcdc895fa468eb3cad85d6cabe`, SHA-256 `4b9bf197546985b2c298b15d33bcf256e892a76a749ed1b367fe96aa4c536d46`. The actual guarded JSON reviewed has SHA-256 `15a315b4e87f966bd8d7bde577fa18d06e4d750720bd3e9d4404d9547605bd86`.

## What was independently checked

- All 104 incoming manifest payload hashes, four inherited Git blob pins, five current library/code Git blob pins, and the archive Git blob.
- Separate parsing of the literal `t215` and `tD` trees from pinned `KSource215Data.lean`, without Lean evaluation. Both have 4,751 leaves.
- Separate reconstruction of every canonical leaf checkpoint and each positive/zero successor, including exact consumed-path normalization, increments, break/continue operations and finite intervening path. The two rebuilt graphs are identical, and equal both stored graph inputs: 1,426 vertices, 2,850 labelled edges. Each tree has maximum intervening segment length 5 and segment-length sum 3,420.
- Both empty-pointer entries decode directly to checkpoint 0, canonical path `000`, with no intervening action or register update. The mandatory bundled phase-five production file's two Tree literals are unchanged. Its source copy and explicit byte-count, Git-blob and SHA-256 pin must all be present and valid; there is no optional external-directory fallback.
- All 1,426 entries of the balanced canonical relation certificate: subtree left counts, both exact canonical leaf pointers, zero offsets, total/unique checkpoint coverage, entry index and every successor lookup. This validates the proposed normalization-aware table, not acceptance by the old literal-pointer checker.
- Exactly 1,059 first-level drain shapes are independently identified; every local coefficient and zero-exit addition is checked. All 732 affine edges have exactly the certified finite drain path and the right-ordered matrix product. All 33 compact matrices round-trip to the full graph. The affine initial binding is node 0 and the identity matrix.
- Exactly 174 triangular and four conditional-clear loops are identified by the **entire ten-by-ten homogeneous map including the node's decrement**, not by selected matrix rows or names. All nine output registers and the constant row are compared.
- Every self-contained loop definition in the updated guarded core has the exact zero-exit target and matrix from the checked affine graph. Both source digests agree. Every one of 376 retained outgoing edges has the exact leading affine matrix, consecutive loop binding, and retained endpoint. There are 189 vertices, including 188 tests and one halt.
- The only halt is literal leaf ordinal **4736**, canonical path `111101` in both trees, retained at both contraction layers, with no successors. Every retained nonhalt is a valid `decnz` with exactly two successor certificates. Failed lookup, decoding failure, or exhausted verification fuel is never classified as halt.
- Every source register read/write index is below 9. Registers 9 and above therefore remain framed unchanged in the actual `Nat → Nat` semantics; the claim does not assume they start at zero.
- An additional 13,350 occurrence-level regressions use R1,R6 ∈ {0,1,2,5,8}, R7 ∈ {0,1,9}, and deterministic randomized positive values in the other six registers. They replay 2,157,631 original checkpoint transitions and 89,478 affine transitions. Exact targets, all nine outputs, and the claimed affine step counts agree. These bounded regressions corroborate, but do not prove, the all-natural theorems.

The independent verifier **does not use the rank witnesses for semantic acceptance**. It also independently expands the 60,401-byte compact guarded representation through its 33 shared matrices and checks equality of every non-rank field with the full core. Its SHA-256 is `be4c2309ad188fa314213b5cd0cb066aeade11c19c50f5ef14b96a57b1957cc7`.

## 1. Exact local semantics

Let a register file be `R : Nat → Nat`. For affine calculations take the column `(R0,…,R8,1)`. A positive branch of a `decnz r` checkpoint first subtracts one from `Rr` under the premise `Rr > 0`, then applies its stored edge matrix. A zero branch applies its matrix without subtraction. The ninth homogeneous row is `(0,…,0,1)`.

An affine map updates registers below 9 to the indicated matrix product and preserves each `R i` for `i ≥ 9`. Source instructions all access indices below 9, so source execution has the same frame property. Induction on steps gives it for finite paths and macros. Projection onto the first nine registers commutes with each source step; combining that projection with the higher-register frame gives equality of the **whole** `Nat → Nat` output file.

A statement about the state “before the zero exit” must not be confused with the final output. The literal zero edge may alter scratch registers, accumulate their contents, and even give R6 a positive value again. The full macro is always the boundary summary **followed by that exact zero-edge matrix and target**.

## 2. All-natural triangular theorem

For any of the 174 occurrences, write `a = R1`, `n = R6`, `z = R7`, and define triangular numbers recursively by

`T(0)=0`, `T(k+1)=T(k)+(k+1)`.

This recursive definition is enough; a closed-form division theorem is not needed by the loop induction. If desired, separately prove `2*T(k)=k*(k+1)` and its natural-division consequence.

The verified positive-body transformation `B` is, under `n>0`:

- `(B R)1 = 0`;
- `(B R)6 = a+n−1`;
- `(B R)7 = z+a+n`;
- `(B R)i = R i` for every other index, including all `i≥9`.

All updates are simultaneous and refer to the old values. In particular, the map preserves R5; a blanket reset of scratch registers is false.

### Tail lemma

For every natural `k,z` and every framed register file with R1=0, R6=k, R7=z, exactly k positive self-bodies lead to R1=R6=0, R7=z+T(k), preserving every other register, with no earlier zero test when k>0.

Proof by induction on k. For k=0, the empty path suffices and is already at the zero boundary. For k+1, the current guard is positive. One body gives R1=0, R6=k, R7=z+k+1. The induction hypothesis gives another k positive bodies and final R7=(z+k+1)+T(k)=z+T(k+1). The first counter is positive and each of the following k guarded counters is positive by the induction hypothesis. This also proves the exact count and absence of an early exit.

### Arbitrary-input theorem

Define the boundary register map `S` and positive-body count `b` by:

- If `n=0`: `S(R)=R` and `b(R)=0`.
- If `n>0`: `S(R)` simultaneously sets R1=R6=0, sets R7=z+T(a+n), and preserves every other register; `b(R)=a+n`.

For `n=0`, no body may execute: notably R1 and R7 remain unchanged. For `n=k+1`, the first positive body gives R1=0, R6=a+k and R7=z+(a+k+1). Apply the tail lemma with k'=a+k. The count is 1+(a+k)=a+n, and the final accumulator is z+(a+k+1)+T(a+k)=z+T(a+n). All unchanged coordinates follow from the per-body frame. This proves the theorem for all naturals without bounded testing or any global program invariant.

Equivalently, the sum R1+R6 decreases by one at every positive body. **R6 itself need not decrease**: from (R1,R6)=(2,1), the next value is (0,2). A plain `while_loop` theorem requiring its body to preserve the counter cannot be instantiated directly; use the one-shot initialization/tail proof above or an explicit sum measure.

If the literal zero edge at v is `(w,Z)`, the complete local macro is

`(v,R) →* (w, Z(S(R)))`

in exactly `b(R)+1` **affine graph steps**, strictly positive even when `n=0`. This count includes the last zero test/exit. Each affine step already expands into a positive finite original checkpoint run, so this establishes positive primitive progress after composing the existing segment expansion. It is not a primitive-instruction or Turing-step formula.

### Necessary-guard counterexample

At node 36, let R1=2 and every other low register be zero. The correct zero exit reaches node 62 with R6=2 and R7=0. Applying the positive triangular formula despite R6=0 instead reaches node 62 with R6=R7=3. This is a post-exit counterexample, not merely a scratch-boundary discrepancy.

## 3. All-natural conditional-clear theorem

At nodes 4567, 4585, 4668 and 4733, the verified positive body sets R5=0, decrements positive R6 by one, and preserves every other register.

Let n=R6. Induction on n proves that exactly n positive bodies reach the zero boundary. If n=0, the empty body trace preserves **all** registers, including R5. If n>0, the first body sets R5=0 and every later body preserves that zero value; the final state has R5=R6=0 and all other registers unchanged. Applying the exact zero edge once gives n+1 affine steps, always positive.

The guard on clearing R5 is observable in this actual graph at **all four** occurrences: every corresponding zero-exit matrix preserves the R5 column. Thus an initial R6=0,R5=13 must leave R5=13 after exit, whereas an unconditional-clear variant yields R5=0. This is not an optimization that can be justified by a later erasure at these boundaries.

## 4. First-level drain theorem

This also admits an elementary Nat proof, avoiding a matrix-power library. At a drain node testing register r, let the nonzero edge loop back and add counts c_i, with c_r=0. Let the zero edge target w and add counts e_i. Starting from Rr=d, after j≤d positive iterations:

- the counter is d−j;
- every other register i is R_i+j*c_i.

Induct on j, using j<d when another positive body is required. After d bodies, take the zero edge once. The output is R'_r=e_r and R'_i=R_i+d*c_i+e_i for i≠r. This is exactly the verified homogeneous matrix. Every input has a total, **positive** d+1 checkpoint-step realization, including d=0.

## 5. Finite paths suffice; ranks are redundant

Fix a retained vertex v and an outgoing branch. A valid certificate contains its original transition and a finite list `[u0,…,um−1]` of removed, total local macros. Check:

1. The retained branch label, register decrement convention, initial matrix and original successor are exact.
2. That original successor is u0, or the final retained target if the list is empty.
3. Each local macro's source is its listed vertex; its exact certified zero-exit target is the next list entry, or the final target at the last entry.
4. Every list entry is in the certified macro domain and has a total local theorem valid on **all** natural register files.
5. The final target is retained; every recorded matrix is dimensionally valid and preserves the natural domain.

Induction on the finite list composes the total local runs. There is no extra well-foundedness premise: the explicit finite list is the induction data. Every retained macro edge has a strictly positive source realization because it begins with the retained test step. Cyclic or unterminated candidate normalization does not justify acceptance: the checker rejects any list whose bindings fail or whose endpoint is not retained. If a generator uses fuel, exhaustion is a rejection, never halt or success.

For retained starts, no separate vertex-rank table is used or needed. This includes source entry 0, which remains retained.

### Further simplification found by this review: suffix coverage

The 182 references on the 376 guarded edges contain **all 178 removed vertices**. The only repeated occurrences are the four conditional-clear loops. For each removed vertex u, choose any occurrence in an already checked edge path and take its suffix beginning at u. The suffix has exactly the same checked source/exit bindings and ends at a retained vertex. Because the local contracts hold for every register file, this suffix is a total, positive entry-normalization macro from u for arbitrary registers, not just registers arising along the original edge.

Consequently the concrete all-start theorem requires only a **coverage check plus suffix extraction**. It does not need separately serialized entry paths, in addition to not needing ranks. `ENTRY_SUFFIX_CERTIFICATES.json` records independently derived witnesses for inspection; they need not be part of a minimal trusted input.

The same observation applies at the first contraction: all 1,059 drains appear among the 1,243 certified affine-edge drain references. Their existing path suffixes give every removed drain's entry witness.

Generic caveat: a graph with an uncovered removed vertex does need another entry witness if the theorem quantifies over that starting vertex. Retained-entry soundness alone does not imply total normalization from all removed vertices.

## 6. Exact halting equivalence, not just forward simulation

Use a deterministic source transition F and a contracted transition M, an embedding of retained configurations into source configurations, and literal halt predicates. Require:

- Halt preservation **and reflection** on retained configurations, including exact final register files.
- Every nonhalt retained configuration has the appropriate M transition.
- Each M transition has a finite F realization of length k≥1 with exactly the stated endpoint registers.
- A literal source halt has no outgoing F transition.

Forward halting transport concatenates these finite realizations. For reverse transport, induct on the length n of a source run to a literal halt. At n=0, halt reflection gives contracted halt immediately. Otherwise either the retained state is already halt (the n=0 witness suffices), or its total contracted successor has an F expansion of some length k≥1. Determinism implies that this expansion and the given halting run have the same prefix. The expansion cannot pass beyond that run's halt, because a literal halt has no successor. Thus k≤n, the residual source run has length n−k<n, and the induction hypothesis applies to the contracted successor. Append one M step.

This proves halting equivalence and equality of terminal registers. It avoids assuming an inverse step relation or a global measure. A failed source lookup/fuel exhaustion is not a halt witness. Positive progress is essential to the strict decrease in n. For arbitrary removed starts, first apply the covered suffix normalization and the same deterministic prefix argument.

At the raw `RegisterPath` level there is one further adapter: canonicalize the decoded consumed path, rather than equating arbitrary raw pointer lists with their canonical leaf strings. `consume` truncates and zero-extends to the actual leaf depth. `step_tsite`/the canonical normalization lemma must establish that equivalent decoded sites have the same next transition, and terminal correspondence must use the literal `.halt` decode. Our independent graph builder follows this rule; this mathematical review does **not** claim its proposed adapter is kernel compiled.

## 7. Reuse existing arithmetic, but not at a false boundary

`L2Lib222.pair162` is related but not identical. Its contract includes the initial transfer of `tw` into `s1` and `s2` before the tested register-6 boundary. Therefore its zero-input behavior is not the checkpoint theorem above. Reuse requires a checked path/boundary adapter, an exact register-field correspondence, and preservation of the arbitrary-file contract. Do not apply the theorem solely because its name says “pair”.

`Cantor.tri` recursion and `P_step` are appropriate arithmetic ingredients. A fresh matrix-power formalism or the unrelated `ArithmeticCantor` interface for arbitrary IOpen models is unnecessary for these two Nat inductions. A full existing pair-macro adapter may reduce occurrence-level work, but it is a separate obligation and no direct reuse is certified here.

## 8. Recommended minimal formalization interface

1. Define exact source-step and literal-halt semantics, with a finite-register projection and an arbitrary higher-register frame.
2. Prove the drain, triangular-tail, guarded-triangular and conditional-clear local totality theorems, with exact full-register output and positive run witnesses.
3. Prove a list-path composition theorem and an acceptance-soundness theorem for the concrete structural/matrix comparisons. Index validity, malformed input and non-retained endpoints must reject.
4. Prove the positive deterministic macro halting theorem and the canonical consumed-path adapter.
5. Check the retained entry/terminal bindings and concrete certificates in the proof kernel. For all-start results, additionally check coverage and derive suffix witnesses; omit separate rank inputs.

The arithmetic core should stay a composition circuit with explicit guards. Expanding chains of quadratic summaries into a single large polynomial increases degree and proof effort without improving the transport theorem. It would be incorrect to call the 189-node core affine.

## Artifacts and reproduction

- `independent_verify.py`: independent verifier, run with `python -I -B independent_verify.py`.
- `INDEPENDENT_AUDIT.json`: concrete checks and regression counts.
- `LOOP_BINDINGS.json`: all full local matrices, exact zero exits, and affine-source hash.
- `ENTRY_SUFFIX_CERTIFICATES.json`: derived existing-path suffix witnesses for each removed start.

The first-level generic semantic theorem, canonical path adapter, matrix interpreter correctness, and guarded macro transport remain proof-assistant obligations. The result is a carefully checked mathematical simplification proposal, not permission to delete or replace existing endpoint proofs without those obligations.

### Standalone verifier safety checks

The verifier explicitly rejects optimized Python (`-O` and `-OO`) and any presence of `PYTHONOPTIMIZE`, even under `-I`/`-E`, before reading inputs. Its validation uses an explicit exception-raising `check`, rather than relying on removable Python assertions.

A full isolated run from unrelated working directory `/tmp` passed. A separate temporary bundle, with no surrounding research directories, produced byte-identical `INDEPENDENT_AUDIT.json`, `LOOP_BINDINGS.json` and `ENTRY_SUFFIX_CERTIFICATES.json`. Temporary-copy mutations confirmed rejection of a missing phase-five source, a same-length changed source and a missing phase-five pin. Optimized invocations and `PYTHONOPTIMIZE` values `1`, `0` and the empty string were all rejected. See `PORTABLE_CHECKS.json`.

The mandatory source is bundled as `affine/current_sources/KSource215Data.phase5.lean` with `affine/CURRENT_PHASE5_SOURCE_PIN.json`. Its commit is `0359ebda60aaf52758358e1450a04988136db67e`, Git blob `c966e0626e98d038d8b4e9300d37414e2ea128ed`, SHA-256 `ccf9e2970482a772bea93919974431c39c442a6c23f83731c0b561c9945fae1e`, length 432,131 bytes. This is the same previously compared production source, now a mandatory portable input. No received data or core certificate was modified.

Final verifier code SHA-256: `9e9077a7188560ae254624e4c36089b807ed7f203f67613ef86035ba6a94f5a5`.
