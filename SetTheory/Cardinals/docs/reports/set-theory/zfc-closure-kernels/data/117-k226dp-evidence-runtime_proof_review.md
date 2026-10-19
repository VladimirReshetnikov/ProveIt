# Independent review of the K228 runtime proof

**Conclusion.** The `prove_blocks` + `case` route establishes the needed unbounded mathematical simulation theorem for the exact final K228 table. The initial seed fits its quantified frame family exactly. Composition still needs two explicit mathematical arguments: normalization of a program-counter word to a leaf by zero padding, and equivalence of the four rewritten closed source chunks. Both arguments are given below, and their finite premises have been independently checked. No soundness gap was found in the reviewed runtime route. This is a mathematical proof with executable evidence, not a newly compiled Rocq endpoint for 228 states.

The reviewed final inherited-label table has SHA-256 `b51892325a6f179ae27d5178c56598213c3463c4ff1f66aae953f3f8a192bf4d`; its 5,121-leaf source has SHA-256 `61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b`. The engine and helper are the unchanged `symbolic_runtime.py` and `independent_runtime.py` in the retained 237-state verification package. Exact final runtime evidence is in `runtime228-original.json` and `runtime228-original_cases.json`; finite interface evidence is in `runtime_interface_audit.json`.

## 1. The quantified frame

Put

\[
B(v)=0\,1^{v+1},\qquad C(v)=1\,0\,1^v.
\]

For a finite list, extend these encodings by concatenation. A dispatcher frame consists of state 96, a head immediately right of a left marker 1, zero exterior to the left, and the following word to the right:

\[
 p\;0^{64+g-|p|}\;1\;
 B(V_0)\cdots B(V_8)\;B(s)\;B(A)\;0^\omega.
\tag{1}
\]

Here `p` is a leaf word of length at most 40, `g` is any natural, `s` is any natural, and `A` is any finite list of naturals, including the empty list. The physical values are related to logical registers by

\[
 V_{\pi(i)}=R_i,\qquad
 \pi=(6,2,0,4,3,7,8,5,1).
\]

This is exactly the permutation in K230's `Interpreter230Check.v`, and exactly the permutation used by the Python engine. There are at least ten encoded registers: nine primary values and the explicit first spare `s`. Thus the engine covers the nonempty-spare premise used by the inherited Rocq simulation invariant.

For a decrement's zero branch, the selected logical register is set to 0. For its positive branch it is represented as `1+n`, where `n` is an independent arbitrary natural. All other eight primary values remain independent arbitrary naturals. These two branches cover every valuation. An increment's extra output spare has value 1; the arbitrary existing spare list is preserved before that appended block.

The tape outside (1) is zero, rather than an arbitrary infinite binary background. That is the intended scope and is sufficient for a machine started on the blank tape.

## 2. Why the symbolic execution is universal

A run atom is a repeated bit whose length is an affine expression in thirteen slots: constant, gap, nine primary parameters, first-spare value, and total remaining-spare-list width. The normalization routine requires every coefficient of every run length to be nonnegative. A literal step from a non-self-loop requires the length's constant coefficient to be at least one. Consequently the cell exists for every valuation; the implementation never substitutes a large finite test value for a variable length.

When a row is a self-loop moving in the current scan direction, the engine consumes a whole homogeneous run. This is ordinary induction on its arbitrary natural length. The length-zero instance has no movement and no transition, and the successor instance is the literal row followed by the induction hypothesis. No bound on that length enters the argument.

Opaque finite-list atoms have a separate justification. `prove_blocks` checks the one-block transformations, on the actual final table, at inherited entries 73, 95, 48 and 112. The proof surrounds the block by two opaque arbitrary contexts and fails if either context is inspected. Each traversal returns to the same control entry beyond the transformed block, takes exactly `v+2` transitions, and has the corresponding displacement. Induction on the number of blocks therefore gives traversal of every finite list, including the empty list. The total-width slot represents

\[
 W(A)=\sum_{v\in A}(v+2).
\]

Its treatment as an independent nonnegative parameter is harmless: every actual list instantiates that slot with its actual width, and neither the control proof nor the tape equality assumes a relation that could exclude a finite list.

The only additional list normalizations are

\[
 C(A)1=1B(A),\qquad
 1\operatorname{rev}C(A)=\operatorname{rev}B(A)1.
\]

The first follows from `C(v)1=1B(v)` by induction on `A`; the second is its reversal. Merging adjacent equal-bit runs, removing a zero-length run, and absorbing finite zeros into the adjacent infinite zero exterior are exact word identities. These normalizations do not discard a nonzero tape cell or an unknown data block.

Thus each successful symbolic derivation denotes an exact concrete run for every allowed valuation and list. The 4,000-iteration bound restricts construction of a symbolic derivation. It does not restrict any concrete tape length, register value, spare-list length, or runtime.

## 3. Full tape, head and positive-time contracts

The symbolic state represents both sides of the head as ordered lists of atoms, together with the scan direction and control state. Equality of normalized target states entails equality of the represented entire tape relative to the final head, not merely equality of selected registers. The separately accumulated displacement must equal the expected marker displacement: zero ordinarily, minus one on a program-counter overflow. This ties the relative tape equality to the same absolute coordinates up to the stipulated head movement.

For every nonhalting source instruction, `case` returns only upon reaching its exact expected dispatcher frame. That expected frame includes the primary updates, preserved arbitrary spare list, appended `B(1)` for an increment, updated program-counter word, and increased gap where required. A premature halt would cause a missing-table-row failure before this endpoint, so a successful nonhalting case excludes interior halt. For a source halt, arrival at the separate halt outcome is the required endpoint; its final tape and head need not match a nonhalting frame.

The final certificate covers all 6,656 guarded cases and rederives all four list schemas. It uses 1,614,426 symbolic rule applications, reaches every one of the 456 literal rows, and has maximum case-construction length 415. Every successful case has an affine duration with nonnegative coefficients and positive constant coefficient; the smallest such constant is 13. Row coverage is a useful completeness check on the table, but universality comes from the parametric derivations themselves.

In particular, an infinite sequence of source instructions produces an infinite concrete machine run: the accumulated concrete times tend to infinity because each instruction requires at least one transition. Conversely, determinism and the absence of interior halt mean that any finite machine halting run must be accounted for by a finite source execution ending at a halt leaf. There is no possibility of infinitely many zero-time simulated instructions before a finite halting time.

## 4. The program-counter interface

A source operation can produce a program-counter word that is shorter or longer than the next leaf word. To apply the next per-leaf theorem, follow its bits and then zeros down the complete source tree. The resulting leaf word differs from the stored word only by appending zeros or removing a zero suffix. Such a change leaves the physical PC-plus-padding word in (1) unchanged, since the header stays at the same distance from the head.

The independent interface audit checks this property for every nonhalting guarded successor, as well as the initial empty word. It finds exactly one leaf after zero extension, verifies that any discarded suffix contains no 1, and checks the full source trie is binary and prefix-free. The resulting program-counter normalization therefore does not alter a physical tape configuration.

The gap update is `g'=g+delta+overflow`, where `delta` is 1 only for a successful positive decrement. Consequently `g'` remains nonnegative. An increment appends one spare block and other instructions preserve the spare list; the list never becomes empty. The frame family is therefore closed under every instruction's output and under leaf normalization.

## 5. Exact initialization

The final K228 blank startup takes 409,835 transitions. Its endpoint is state 96, head at absolute coordinate -5, with exactly 351 one-cells. The independent audit reconstructs all of them from (1), using

\[
 R=(3,0,0,0,3,0,0,0,0),\quad
 g=117,\quad s=1,\quad A=[1]^{166}.
\]

The physical primary values are `(0,0,0,3,0,0,3,0,0)`, the header distance is `64+117=181`, and there are 167 spare blocks of value 1. These are exactly `R0`, `boot_regs` and `boot_right` in the pinned K230 development. The initial stored PC is empty; its normalized leaf is `000`, and the three zeros simply use three cells of the same 181-cell padding.

The support reconstructed independently from this formula agrees with the complete support in the startup certificate. Thus the seed is an actual instance of the universally quantified frame theorem; there is no unproved appeal to a vaguely equivalent or sufficiently large initialization.

## 6. The source rewrite and its logical connection

The independent audit parses the actual `p230_tab` list from the pinned Rocq `Prog230.v`, traverses its 5,124 nodes, and checks that its 5,125 leaves exactly match the released `sites230.json`. It then verifies that the new source is obtained by precisely four replacements of

\[
 H=\bigl((D_6,(I_5,C_2)),I_5\bigr)
 \quad\longmapsto\quad
 H'=\bigl(I_5,(D_6,C_2)\bigr).
\]

No additional source change is present in the accepted K228 pair. Here `D_6` is decrement-with-zero-exit on register 6, `I_5` increments register 5, and `C_2` is the indicated continue operation. Both chunks are closed: the relative control paths keep their repeat inside the chunk and their exit is the common next instruction outside it.

If the incoming value of register 6 is `n`, the old chunk executes `n` copies of decrement/increment/continue, followed by the zero decrement and final increment. The new chunk executes `n` copies of increment/decrement/continue, followed by the final increment and zero decrement. Both take `3n+2` source operations, terminate for every natural `n`, set register 6 to zero, add `n+1` to register 5, and preserve the remaining registers. Registers 5 and 6 are distinct. Both have the same single external exit and neither halts internally.

Control flow from outside a closed source subtree enters its leftmost leaf: a sequential successor enters that subtree at its beginning, while break and continue target ancestor/sibling boundaries. It cannot enter an internal leaf from outside. Therefore replacing any occurrence of `H` by `H'` preserves complete-program halting, by matching chunk-entry and chunk-exit checkpoints and all ordinary instructions. Applying that argument to the four independently located occurrences connects the new source to the exact pinned K230 program.

Combining this source equivalence, exact blank initialization and positive runtime simulation gives the arithmetical transfer

\[
 \operatorname{Halts}(K_{228},\mathrm{blank})
 \longleftrightarrow
 \operatorname{Halts}(K_{230},\mathrm{blank}).
\]

The existing K230 theorem then supplies the logical equivalence with `StandardZFC` refutation and hence with the negation of `Con(ZFC)`. All new transfer arguments are finitary inductions on naturals, source syntax and finite lists, and are formalizable in ZFC.

## 7. Scope and limitations to state in the report

The fixed new table has a proved mathematical transfer; it is not merely a bounded simulation candidate. However, the Python engine and the above elementary soundness argument are not a newly compiled Rocq proof object. The existing Rocq endpoint remains K230. Its set-theoretic and proof-enumerator calibration is an inherited dependency, not something re-established by scanning this transition table.

The local delayed-erasure explanation uses the extra implication `169/read-1 => right neighbor 1`. The predecessor-bit invariant alone does not establish that implication on every initial binary tape. The startup checker establishes it at all six relevant blank-prefix visits. For the infinite part, the accepted proof uses the complete direct K228 runtime theorem, which already proves the final instruction contracts and does not assume that guard. Therefore failure of the stronger all-tape fold checker is correctly distinguished from failure of the blank-start theorem.

Full replay should rerun `prove_blocks` and every `case` on the pinned bytes, with assertions enabled, rather than merely trusting the saved PASS label. The finite interface audit and canonical relabeling check should also be included. No new internal PA derivation, serialized ZFC derivation, global state-count minimum, or machine smaller than the delivered table follows from this work.
