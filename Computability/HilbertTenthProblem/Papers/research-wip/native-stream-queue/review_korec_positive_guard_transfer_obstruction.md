# Independent review of the packed positive-guard transfer obstruction

**PASS, with no requested author correction.** The specified one-row
376-to-375 change fails to preserve the actual U21 program/input relation.
At the fixed positive program parameter E=2 the genuine machine diverges
for every ordinary positive input x, while the altered polynomial has a
full positive zero for every such x. This does not prove that the altered
polynomial has no other universal slices, or that every possible packing
of the local vector guard must fail.

The reviewed author packet is frozen at:

| File in `/tmp` | SHA-256 |
|---|---|
| `korec_positive_guard_transfer_obstruction.md` | `29a3e9c08648201d64a8a07ff4d081e93e4af4474834f9ef93134aea50c443cd` |
| `korec_positive_guard_transfer_obstruction.py` | `68c8895a1a2c0e72f41825ae7c41ff418dca16bd29d9e1dba6185a924a92ef86` |
| `korec_positive_guard_transfer_obstruction.json` | `f6c771b9a0b2e582375178df47c7618da26e8d15a720afd196793a229d7804ac` |

## 1. Exact source and domain binding

I inspected all 376 literal rows of the `units`, `program_radix=false`
record of `korec_packed_repunit376.json`, as data only. Its external
parameters are `program,input`, and it has 50 positive witnesses.
The sole removed row is exactly

    counter_M_325 = counter_digit_mask_92 - Z_sum_146.

Its sole consumer is `range_mask_93`; redirecting that operand replaces
the mask `(h-1)(VJ-Zword)` by `(h-1)VJ` both in the global range unit and
in the joined native mask. The other use of `Z_sum_146`, in
`current_base_159`, survives. Thus the chronological control code still
uses the selected zero edge. Further deleting that word's producers
would not be the stated candidate.

My structural check reconstructs this precise mutation and verifies
acyclicity, all supplied/computed liveness, and **375=143M+232A**, with the
same 50 positive witnesses. It does not evaluate either array. The final
nine-factor product-minus-one shape and all other source rows remain
literal. This rejected one-program 375 source must not be confused with
the separately accepted two-program 375 interface listed in the parent.

The machine parameter is E directly, not E-1: the positive-program410
change is inherited by the current source. At E=2 its initial registers
are therefore `(0,2,x,0,0,0,0,0)`. The later minimal-radix change has
`B=D^8`, not the older `2D^8`. Both details agree with the actual rows.

## 2. Divergence and the false branch

I independently transcribed the transition semantics, parsed the literal
21-state table and its labels from the pinned parent proof, and used
affine polynomials in two independent symbols x,A. Every tested symbolic
value is either identically zero or strictly positive for x,A>=1.
This verifies branch choice for the whole domain, not just sampled inputs.

The genuine 59-transition prefix ends at state 0 with
`(1,2,x,0,0,0,1,0)`. The genuine 30-transition cycle maps
`(A,2,x,0,0,0,1,0)` to `(A+1,2,x,0,0,0,1,0)` at state 0.
Neither path visits halt. Induction on the number of cycles proves
nontermination for every x>=1; no finite time cutoff supplies this proof.

After the prefix and 26 further genuine transitions, time 85 has state 10
and registers `(1,2,x,0,0,1,1,0)`. The instruction is `D 5 11 12`.
Taking its zero edge to 12 is false because register 5 equals 1, but
its prescribed zero-edge update changes no register. State 12 then
genuinely decrements positive register 2 and reaches 17; state 17 genuinely
tests zero register 4 and reaches halt 21. The final registers are
`(1,2,x-1,0,0,1,1,0)`. There are exactly 88 transitions and one false guard.

My freshly written checker matches every one of the author's 59+30+88
saved transition records, including before/after vectors and labels.
It executes only its own transition formulas, never the author program
or any saved arithmetic source array.

**Remark 1 (retained failed redundancy proposal).** Positivity alone does
not make the selected zero-clearing subtraction redundant. At time 85
the selected zero edge leaves a positive addressed counter unchanged.
All update equalities can hold while its zero test fails. The previously
accepted local vector theorem has a separate product guard which rejects
this row; it did not claim that the guard itself was redundant.

## 3. All remaining packed and positive-native conditions

Choose dyadic h above x+4 and all fixed counter values. Set D=2h,
B=D^8, T=88, P=B^T and J=(P-1)/(B-1). The 34 selector words choose exactly
the displayed edges. The stored post-decrement counter digits are
nonnegative and at most h-3, including pure-test positive rows which
contribute one to both action words. Hence ordinary digit comparison gives

    B(W+I)+2D+xD^2 = W+L+P Y,
    B following+D = current.

Every counter digit is below D, every control code below B, and the final
vector has register 2 equal to x-1>=0. The E2 input is bound directly;
there is no alternative input code or variable-duration free parameter.

Let R0=(h-1)VJ and Rstar=(h-1)(VJ-Zword). The relaxed mask permits every
stored counter digit, whereas the cleared mask loses exactly

    W-(W AND Rstar)=D^5 B^85.

All genuine zero-test positions have zero addressed digits. This is the
only lost bit contribution. Every one of the eight range-digit differences
between R0 and W is at least 2, with no borrow. Thus
`gamma=R0-W-2>0` makes the altered range factor exactly +1. The two exact
transport equations make both transport factors +1 as well.

With the actual 35 lanes, `H=Cpack+P^34 W`,
`M=Cmask+P^34 R0`, `Q=B P^35`, one has
`0<=H<M<Q`, Q dyadic, and `H AND M=H`. Therefore at q=16Q the actual
fields

    16(Q-M)-15, 4, 16(M-H)+2, 16H+8

are positive, have the prescribed low residues, and sum to q-1.
These are exactly the complete native AND extension hypotheses, not
the false hypothesis that the outer path is a genuine halted computation.
The accepted native theorem supplies all six native factors equal to +1
with positive private coordinates.

I checked the source-specific index rewrite:
`r=(q-1)S`, where `S=5+Bpad+q(Bpad+q F3)` and `Bpad=16M+10`.
It equals the four-field packed index. In particular q<r<q^4. For the
canonical native X=2^(2r+1), divisibility by dyadic q is integral and
`X/q>r>S`; consequently `bound_beta=X/q-S` is strictly positive and
respects the literal bound-only producer `X=q(S+bound_beta)`. The
normalized strong and coupled-index construction is inherited with its
full positive extension, not justified by an off-zero coordinate map.

There are 38 explicit outer witnesses: 34 edge hats, two counter hats,
height slack and global slack. The remaining 12 are the actual native
ports `f,h,i,j,o,tau_gap,eta,zeta,ga,y_aux,odd_half,bound_beta` with the
`native__` prefix. Their existence makes the actual modified final
polynomial zero. No enormous Pell tuple was materialized. This reasoning
works for every x>=1; the author's numerical packing at x=1,h=16 is only
one finite corroboration.

## 4. Independent evidence and scope

My fresh checker performs the structural source mutation and affine
transition checks above. Separately written reverse-Horner packing
formulas verify all remaining outer equations, the exact missing mask
term, all selector lanes, strict field/range positivity, the joined AND
and the specialized index identity for x=1,2,7,16,31,255. At x=1 they
also match the author's 34 selector hats, both counter hats and global
slack exactly. P has 3521 bits and Q has 123241 bits in that case.
These calculations evaluate handwritten formulas, not saved source DAGs.

**Remark 2 (ordinary product is not a synchronized guard).** The note's
second counterexample is correct: a legal zero test at a zero counter
followed by its increment has guard-factor digits `(-1,0)` and `(0,2L)`.
Both corresponding products vanish, but the two ordinary packed words
multiply to `-2Lb`, nonzero in any positive radix b. This rejects that
specific proposed substitution; a separately paid diagonal-extraction
or selected-product construction remains outside the conclusion.

I read the full author MD lines 1–274 and PY lines 1–180, and the saved
traces, source-binding metadata and outer witness fields in its receipt.
I read the following parent notes completely as inert text; their full
byte pins are authenticated and recorded in my receipt:

| WIP note | Inclusive lines |
|---|---:|
| `korec_packed_repunit376.md` | 1–150 |
| `korec_packed_zero_range397.md` | 1–237 |
| `korec_packed_positive_program410.md` | 1–172 |
| `korec_packed_counter_units.md` | 1–410 |
| `korec_packed_counter_compiler.md` | 1–323 |
| `residue_affine_packed_history.md` | 1–288 |

I also read the full native interface notes
`native_binary_index_coupled_units.md` (1–316,
SHA-256 `efea1218eb5fadc1ad224a2ef6864fb5ea4fecbd5231d7b1379e3e376af690b5`)
and `native_binary_masked_selection63.md` (1–254,
SHA-256 `c2e08f2d9fdaaf2e17880d7a131254492afd7ef21b035985714734cbc158c53e`).
This is a new check of the present extension interface, not a new full
audit of every earlier Pell lemma or external machine-universality proof.
The parent source is inherited as the accepted literal compiler; its
selected 376 rows were read, with the new mutation checked structurally.
Other parent receipt variants were not audited.

Own fresh normal and optimized runs from `/` passed with byte-identical
receipts before freeze. No author, archived, frozen, supplied or predecessor
helper was executed/imported; no saved or mutated arithmetic array was
evaluated. There were no repository/Git edits. The universal84 construction
is unchanged; this packet establishes a concrete failed transfer, not an
operation improvement or a global lower bound.

The fresh companion `review_korec_positive_guard_transfer_obstruction_checks.py`
has SHA-256 `c940c18094bdd4f4056fdf5a8561aa8a67b8be46abb3607e868c6be1504c797f`;
`review_korec_positive_guard_transfer_obstruction.json` has SHA-256
`30edf06a8204bd4437e0c05b7f467b8bb8c15b630d2119a33d20706ccacafae9`.
