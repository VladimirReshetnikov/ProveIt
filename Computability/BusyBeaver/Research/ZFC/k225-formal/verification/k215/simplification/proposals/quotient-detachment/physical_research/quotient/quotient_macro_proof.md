# Quotient-MP: an exact source experiment, not a smaller binary machine

The numerical semantic rule is justified separately in `quotient_detachment.md`.
This note concerns its implementation in the pinned primary K215 source, SHA-256
`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`.

## The concrete replacement

In the 106-instruction MP branch at source path `110100101`, replace primitive
ordinals 4652 through 4660 inclusive. The inherited pairing routine has already
established

    R1 = 0, R5 = h, R6 = 0, R7 = P(a,b),

where R1 is the current formula, R5 the cached formula, and R6/R7 scratch registers.
The old nine instructions move `4*P(a,b)` through R1 to R6. The new nine instructions
compute `R6=floor(h/4)`, `R5=P(a,b)`, and `R7=0`, leaving R1 zero. The inherited exact
equality test therefore accepts exactly `floor(h/4)=P(a,b)`.

Writing `(x,y)` for a binary source node, the first source variant is

    D4 = (CD5, ((CD5, (CD5, (CD5, CI6))), CC2))
    X  = (CD7, (CI5, CC2))
    replacement = (D4, X).

The source interpreter uses decrement-and-skip `CD`, increment `CI`, and a
backward jump across the specified number of right ancestors `CC`.

## All-natural macro proof

All registers other than R5 and R6 are untouched by D4. For any nonnegative k,
the four terminal cases give

    (R5,R6)=(r,k)  ->  (0,k),          0 <= r < 4.

For every n,k >= 0, one complete positive iteration gives

    (R5,R6)=(n+4,k) -> (n,k+1),

and returns to the first instruction of D4. This takes six primitive transitions.
The terminal cases take respectively 1,4,5,6 transitions for residues 0,1,2,3.
Induction on h div 4 proves termination and the exact contract

    (h,k) -> (0,k+floor(h/4)).

The duration is `6*floor(h/4)+sigma(h mod 4)`, where
`sigma(0)=1` and `sigma(r)=3+r` for r=1,2,3. No interpretation of h as a well-formed
formula is used in this arithmetic contract.

The transfer X has the standard all-natural contract

    (R5,R7)=(u,p) -> (u+p,0),

with duration 3p+1. Composing the two proves the promised replacement contract.
The inherited MP construction and equality continuation then give, with
`y=d+x`, the command effect

    (t,w,d,h; field x) ->
      (y,P(0,w),y,0)  if h div 4 = P(t,y),
      (0,w,y,0)       otherwise.

The candidate-list field is consumed exactly as before; the other registers
are unchanged and both scratch registers are zero on return. This calculation
does not prove consistency calibration: the separately proved semantic rule
and strong compiler transport are needed for that conclusion.

## Exact source evidence

The generator enumerates all associations of the six-leaf division word using
the already present CC1, CC2, and CC3 operands. Eight have the desired finite
interface; the source-only minimum among them is 210 distinct subtrees. The
baseline has 202. All eight have 4,751 primitive occurrences, depth 47, and
maximum zero run 6. Both independent CFG resolvers agree. Since the replacement
has the same nine leaves, every primitive and every guarded edge outside the
replacement interval is exactly unchanged under its original ordinal.

`check_quotient_mp.py` independently runs the entire MP branch, including its
input-field reader, constructor, comparison, and success/failure paths. The
selected source passes 5,688 finite cases, including all four residue tags,
zero-pair aliases, mismatches on both sides, and nonzero underlying stacks.
These finite tests corroborate the all-natural arithmetic proof; they are not
its substitute and are not proof-assistant certificates.

## Physical cost and an explicit failure boundary

The 210-node associations introduce `CD5` at a right-child leaf. Other variants
introduce `CI6` at a right-child leaf. Those polarities have no generic entry in
the inherited conservative allocator, so its raw rejection does not mean that
the source semantics are wrong.

A compatible lowering for variant v00 replaces the right-child `CI6` with
`(CI6,(CD1,CC1))`. R1 is zero throughout the division, so the appended clear-R1
loop executes one zero test and has no effect. Each complete division cycle
takes seven rather than six transitions. This source has 4,753 leaves and
212 distinct subtrees. It passes the same 5,688 complete-MP tests.

The unchanged conservative allocator gives **234 states** for this source and
passes all 4,752 internal prefixes and all 4,753 literal primitive-entry checks.
Its identity control reconstructs the original 215-state table byte-for-byte.
This is a prefix/entry price only: no new arbitrary-register runtime proof or
blank-start consistency theorem was established for that 234-state table.

Thus quotient detachment is a mathematically useful interface relaxation, but
this concrete implementation does not yield 214 states. A different comparator,
constructor sharing scheme, or physical encoding is needed for a state saving.
