# Independent review of AX11QH4L and AX11QH4R

## Outcome

Both supplied 194-state constructions passed independent literal-table verification and exact structural novelty checks. The relative halting transfer to the pinned PA194AX11QH parent has an explicit factor-two witness bound. This review does **not** establish an absolute iPRA/Con(PA) calibration or a sub-194 machine.

The authoritative dense-table SHA-256 values are:

| Role | SHA-256 |
|---|---|
| Parent PA194AX11QH | `19e215df20429fa6a35f0a99ba0dcfcb40893a6e4b9a4ae6e450b0225f110e50` |
| AX11QH4L | `c825ec97fdaa36868d1830b601863d255853ebe061af8b22f432d55233763659` |
| AX11QH4R | `9ea0169880ecaea748d11217c829420aa8694948d2578b8fc28adcc3bcf76815` |

## Construction and materiality

The source instructions are unchanged from the parent, but the repeated four-increment physical decoder changes. Its balanced association is replaced by `((i,(i,i)),i)` or `(i,(i,(i,i)))`. The raw table gains helper 330; the compatible fold set grows from seven to eight. Each final table has `135 + 67 − 8 = 194` working states and 388 actions.

AX11QH4L changes 183 of the 3,671 encoded source addresses; AX11QH4R changes 244. In each variant 122 addresses grow by one bit and 61 shrink by one bit. The maximum address length is 36, below the 48-bit minimum header allocation. Every resolved instruction, branch target, opcode, and logical register field matches the parent.

The new helper occurs in 183 distinct symbolic source-outcome contracts in each variant. Thus it affects recurring implemented operations. It is not exercised during the finite initialization prefix, which is a different phase of execution; no claim is made that every control is visited by the actual blank computation.

## Independent physical verification

The audit reused the supplied PA1944L **independent** checker unchanged. That checker imports no constructor and no arithmetic-box oracle. It parses each new literal table, checks the label bijection and dense/native conjugacy, derives four generic unary-list sweep lemmas from the actual rows, and checks each source operation over nine arbitrary natural register values, both decrement branches, arbitrary nonempty finite spare lists, and arbitrary affine header padding. Two source resolvers independently recover the same control-flow graph.

Both runs exited successfully. AX11QH4L passed all 4,778 outcomes in 1,136,120 symbolic operations; AX11QH4R passed all 4,778 outcomes in 1,135,937 operations. Each maximum case length was 403 symbolic operations, and every affine duration had positive constant term at least three. These operation counts describe the verifier, not a bound on concrete arbitrary-register execution time.

For both tables, direct literal replay from an entirely blank tape reaches the complete expected source-25 frame after 58,088 transitions, at native control 84 and head −2. The entire finite-support tape is compared, including the code word, padding, nine primary registers, and 26 spare blocks.

The supplied parent universal certificate is separately bound to the parent table and its recorded contract hash. It was not described as a fresh parent universal replay. The clock comparison script freshly replays the parent's finite 57,922-step startup as well as both new startups.

## Exact clock comparison

The script `check_clock_comparison.py` validates all 4,778 case pairs and writes them explicitly to `clock_comparison_full.json`. It checks that positive decrement uses the same residual-value coordinate in all tables, so coefficient comparison is comparison on the same arbitrary natural parameters.

All twelve nonconstant affine coefficients are identical in the three implementations. Their maximum is eight; the maximum constant term is 534. Constant differences, new minus parent, are:

| Difference | AX11QH4L cases | AX11QH4R cases |
|---:|---:|---:|
| −2 | 0 | 61 |
| 0 | 3,670 | 3,548 |
| 2 | 61 | 61 |
| 4 | 574 | 635 |
| 6 | 412 | 473 |
| 8 | 61 | 0 |

All motion vectors also coincide. The 4,777 nonterminal outcomes have zero displacement, hence zero root overflow. The unique terminal operation is source site 10, address `001`; all three implementations take three transitions and move right by three cells. Logical register updates, appended spare blocks, positive-decrement gap changes, and frame heads therefore agree at every corresponding ordinal source boundary.

Writing `d_P`, `d_L`, and `d_R` for matched operation durations, coefficientwise comparisons establish

`d_P ≤ d_L ≤ 2 d_P` and `d_P ≤ 2 d_R`, `d_R ≤ 2 d_P`.

The same inequalities hold for startup lengths. They consequently hold for the accumulated primitive-recursive clocks at corresponding source boundaries, including the final halt instruction.

With `HaltBy(M,t)` defined using an absorbing halt state, the ordinary written primitive-recursive induction argument gives:

* `HaltBy(P,t) → HaltBy(L,2t)`;
* `HaltBy(L,t) → HaltBy(P,t)`;
* `HaltBy(P,t) → HaltBy(R,2t)`;
* `HaltBy(R,t) → HaltBy(P,2t)`.

For the forward construction, define the boundary clock by primitive recursion, adding the checked affine duration of each source outcome. Quantifier-free induction proves equality with the encoded source frame at those boundaries. Positive durations give a clock at least the source-instruction count. A bounded inverse-clock search therefore locates the current simulated source segment from any physical time. Each nonterminal segment is proved not to halt early; the terminal segment is the checked three-step case. This supplies the reverse witness direction without an unbounded search or stronger induction.

These are ordinary mathematical weak-arithmetic arguments supported by executable finite certificates. No new Lean/Rocq kernel proof is claimed. The list- and run-induction soundness of the symbolic checker is part of the written proof boundary; executing Python is not itself an iPRA derivation.

## Structural novelty

The comparison snapshot is `32d0d8b7d93a63ad4106c18cdb29b37927acdad2`. The frozen inventory combines the authoritative current filed-table catalogue with a fresh literal/explicit-JSON census of all five current incoming archives. It contains 95 historical 194-state table classes, of which 94 have a spanning root. Every retained representative's bytes and catalogue identity were rechecked.

The novelty checker compares complete canonical tuples, allowing arbitrary state renaming, every spanning root, reflection, global bit exchange, and ignored terminal write/move decoration. Neither new table matches a historical table, and the two new tables do not match one another. A table without a spanning root cannot be isomorphic to these spanning graphs. Symbol exchange is only a stronger structural comparison; it does not preserve the zero-blank convention by itself.

## Remaining boundary

The new proofs transfer halting behavior to the exact pinned AX11QH parent. The supplied AX11QH report contains a separate written relative argument to primary PA194; it is an inherited proof dependency, not a new result of this review. The authoritative repository still leaves the literal primary iPRA/Con(PA) calibration open. Thus neither the physical certificates nor the factor-two transfer should be presented as a newly completed absolute consistency equivalence.
