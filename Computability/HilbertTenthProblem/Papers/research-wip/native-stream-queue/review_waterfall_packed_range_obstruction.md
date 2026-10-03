# Independent review of the Waterfall packed range obstruction

**PASS; no correction requested.** The pinned family satisfies the actual five outer equations and every other typed AND obligation of both raw forms emitted by `u15_packed_consumed_affine505`. Widening only the left-tape range mask admits a false seven-step history. The existing compiler retains that range lane and correctly rejects the family.

The independently authenticated author artifacts are [source](waterfall_packed_range_obstruction.py), [receipt](waterfall_packed_range_obstruction.json), and [proof](waterfall_packed_range_obstruction.md). This review's [checker](review_waterfall_packed_range_obstruction.py) and [receipt](review_waterfall_packed_range_obstruction.json) are separate; the checker does not import or use the author's algebra or source evaluator.

## Actual source and scope

The two tested raw polynomials have complete ledgers `320 = 116M + 204A` and `318 = 116M + 202A`, respectively. Both have 51 positive witnesses and natural raw tape parameters `L0,R0`; their full comparison counts are 11 and 10. The label “505” identifies the parent compiler and its ordinary-input result, not the number of operations executed by these raw fixtures.

The independently reconstructed dependency closure contains 228 source gates per form. It covers all five actual outer comparisons, all three joined AND words, their disjoint top tags, and the cap. Its free coordinates are exactly the two raw tapes, 29 edge hats, and ten other positive outer witnesses. None of the 12 remaining native witnesses is used or supplied. The centered state row and relabeled B/J controller are read from the actual saved complete source; no generic substitute controller is tested.

The checker pins the author trio, the parent Python and full-source receipt, and the placed original TM table before using their contents. It independently parses all 29 table transitions and checks every corresponding relabeled compiler rule. All byte pins appear in the saved receipt. No historical compiler suite is executed.

## General family and carry defect

For `B=2^a`, `a>=9`, set `D=B/64`, `P=B^7`, and `J=1+B+...+B^6`. The literal seven selected edges are `0,2,4,13,12,14,17`, corresponding to

```
A0, B0, C0, G1, G0, H0, I1 -> J1.
```

Use the author's left, right, and popped digits, zero raw input, and final tapes `Lf=B/8-1`, `Rf=11`. The checker builds these directly from the table and rational polynomials in the indeterminate `B`; it does not read numerical family coordinates from the author's fixtures.

Its independent local tape calculation gives left residuals

```
[0, 0, 0, 0, B, -1, 0]
```

and seven zero right residuals. Packing cancels `B*B^4-B^5`; the shifted packed recurrence has the equivalent cancellation `B*B^5-B^6`. Thus the tape equation can lose chronological information when digits are allowed to exceed the intended bound. The proof is an exact polynomial identity, not a numerical observation.

Executing both actual source closures over rational-coefficient polynomials proves all ten outer residuals identically zero. In particular it includes the current centered state equation, head shift, both tape equations, and aggregate bound. It also proves the exact source formulas for `B,D,P,J`, all joined words, and all four tagged/cap outputs: 22 additional source-to-formula equalities in total.

The aggregate is

```
H+G+ZL+ZR+ZU = B^7/2 + 10B^6 + 5B^5 + 2B^4 + 3B^2.
```

The independent checker expands its complementary bound after substituting `B=512+u`. The constant term is positive and every coefficient is nonnegative. This proves strict positivity for every real `B>=512`, hence for all relevant dyadic bases. The same exact procedure checks positivity of every supplied positive outer coordinate and the required packed-word upper bounds. The bits and integrality statements, in contrast, are asserted for the dyadic family only.

## Complete lane accounting

In increasing base-`P` lane order the actual words are

```
A: H, G, U, H, G, E0, ..., E28
M: (B-1)Dir, (B-1)Dir, Dir, (D-1)J, (D-1)J, J, ..., J
Z: ZL, ZR, ZU, H, G, E0, ..., E28.
```

Here each `Ei` is the incidence word obtained by subtracting one from its positive edge hat. For dyadic `B`, the direction masks act independently on base-`B` digit blocks. The incidence masks admit the literal zero/one edge digits. The right tape digits are at most five, less than `D>=8`. Every lane is canonical below `P`.

Exactly lane 3 fails: the left digits `B/2` and `B/4-1` exceed `D-1`. All left digits are still below `B`. Replacing only that mask by `(B-1)J` therefore makes it pass and changes the joined mask by exactly

```
P^3 (B-D) J.
```

All 33 other lanes stay unchanged and satisfied. With `T=P^34`, the tags `Ajoin+2T` and `Mjoin+T` remain disjoint; all tagged values remain below `B*T`. Consequently the complete relaxed joined relation holds and the original tagged relation fails. Deleting the lane and reindexing the remaining blocks cannot restore the omitted restriction.

Independently evaluated bases `2^a`, for `a=9,10,11,12,13,14,15,16,17,20,31,64`, verify the bitwise conclusions with exact integers: 396 unchanged lane checks and 408 relaxed lane checks. The general digit-block proof supplies the unbounded family claim; these finite checks are additional evidence.

Literal TM execution from zero raw tapes reaches `I0` with tapes `(0,5)` before the seventh instruction and reaches `A1` with tapes `(0,2)` afterward. The proposed sequence instead uses `I1` and ends at `J1` with tapes `(B/8-1,11)`. This establishes a false chronological history. It does not establish nonhalting of that input.

## Claims retained and excluded

The author's timestamp expression agrees algebraically with the earlier Waterfall macro-count identity after separating the initial term from the sum. It does not supply exact unweighted digit sums merely by reducing a packed word modulo `B-1`. The counterexample establishes the stated obstruction to deleting the range lane under the current outer conditions; it is not a lower bound against every stronger clock or range construction.

No complete numerical native Pell assignment is constructed here. The review verifies the outer arithmetic and the complete typed exact-AND ports; it neither replays nor independently reproves the inherited native existence theorem. In particular, it does not claim a zero of the original full polynomial, a full positive native extension computed by the checker, a zero on a fixed ordinary-input program slice, or a new universal arithmetic bound. The original guard is effective, so no repair patch is appropriate.

## Frozen replay

```
python review_waterfall_packed_range_obstruction.py \
  --repo /path/to/Proofs \
  --subject-root /path/to/frozen/author/trio \
  --expect review_waterfall_packed_range_obstruction.json
```

The receipt records 456 formally executed source gates, ten exact outer residual identities, 22 joined/tagged source identities, and 12 extra-radix interface fixtures. A private replay of the small author obstruction CLI also reproduces its complete saved receipt with exact type-sensitive comparison. This is the only subprocess replay; historical whole suites are intentionally outside the audit.

Frozen author source: `da29a82c4c8140b3c53991081ef3a77149d3d1de39be5b7e5043edd627c349a6`.

Frozen author receipt: `b92c447dbc1b0a0dd0aef6e33ea05e94b4cd4df9c53efe6795e139766b137024`.

Frozen author proof: `e16165bd366d4c7d46aa4851849946191e47400b6c2979cca0ff762f309dca26`.

Independent checker: `6aa9948e0c63edc848354199a0946f051919f024eca9eabf78b0451179c10774`.

Independent receipt: `f42b0cf0e033caf720cf747e9cb40c9165fd0f3b554c96ec4a4eb28de0f26fd9`.
