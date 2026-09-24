# The complementary zero label saves one addition: 117 operations

The serial controller can emit the complement of its requested zero
label. This lets its top-mask equation use a factored complement and
saves one addition. The complete count is **117 operations: 56 products
and 61 additions/subtractions**, with the same 43 positive unknowns and
31 equations as the cyclic-entry118 predecessor.

The fixed graph still has precisely its original source-zero semantics.
All twelve native fields and both complementary zero flags are retained.
This change does not use either of the false support-typing implications
recorded in `EXPLORATION_ZERO_MASK_TYPING.md`.

The full source and finite receipt are
`../verification/explore_complement_zero_serial_composition.py/.json`.
Its dependencies are the complete
`EXPLORATION_CYCLIC_ENTRY_SERIAL_COMPOSITION.md` and the earlier merged
bound and raw compiler proofs. This is a further alternative universal
upper bound; the smaller existing universal bound remains 90.

## 1. Keep the true zero flag, but output its complement

Let z_i in {0,1} remain the original zero requirement attached to graph
state i. The numerical meaning is unchanged: z_i=1 requires the active
register to be zero before its signed update. Write

    Z=FZ-J, D=FZbar-J.

The retained equation FZ+FZbar=2J+H, after native decoding, says

    Z+D=H,

so both words are Boolean subsets of the counter-block heads. The new
fixed ROM zero-output terms occur for states with z_i=0, rather than
z_i=1. Thus the ROM emits D, and a source-zero requirement is indicated
by absence of that output. The typed complementary flag Z still exists
explicitly; no non-head event is permitted.

The state and sign terms of K, the state coordinates, count marker and
forbidden output mask are unchanged. Only the subset of the fixed zero
label terms is complemented. The same Sidon separation proof applies.
Choose the new fixed power-of-three Rmin at least as large as the old
one and sufficiently large for the newly compiled K:

    Rmin>max(KS,gS,2S+1,Zall,12(KS+Zall+1)).       (1)

It is still imposed by the one existing product R=Rmin*zR. Fixed
numerals may change with the program, but every product with a variable
remains paid.

## 2. The complementary top equation

The old top source is

    6T=2(2J+H)+(R-3)Z.

Using the retained head geometry H(R-1)=2J and Z+D=H, this is exactly
equivalent to

    6(J-T)=(R-3)D.                              (2)

For clarity this identity holds over integers before any digit
interpretation. If E_top denotes the old left-minus-right top residual,
E_head=H(R-1)-2J and E_pair=FZ+FZbar-H-2J, the new residual is

    E_new=-E_top-E_head-(R-3)E_pair.              (3)

The equality of residual combinations does not require any expression
to be positive. The actual pre-mask bound J-T>=0 is independently
available from the merged program bound, as recalled below.

In the cyclic routing source, replace the output h_z(FZ-J) by
h_z(FZbar-J), and replace the fixed program numeral K by its complemented
label table. The resulting complete route is

    (RK-g)C=(gI)(2J)+R[V+h_s(FKplus-J)+h_z(FZbar-J)].

The control endpoints remain identical and the first-return compiler
argument is unchanged. Every other source polynomial is retained,
apart from the fixed coefficient in the paid R threshold.

## 3. Exact arithmetic count

The old zero/top block, including the raw expression shared with the
ROM, evaluates

    top_mask=6*T,
    twice_head=head_rhs+head_rhs,
    R_minus_three=R_minus_one-2,
    raw_Z=FZ-J,
    zero_spread=R_minus_three*raw_Z,
    top_rhs=twice_head+zero_spread.

It costs two products and four additions/subtractions. The new block is

    top_complement=J-T,
    top_mask=6*top_complement,
    R_minus_three=R_minus_one-2,
    raw_D=FZbar-J,
    zero_spread=R_minus_three*raw_D.

Compare top_mask=zero_spread. This costs two products and three
additions/subtractions. The existing ROM output product now uses raw_D,
so no separate complementary flag extraction is added. All mask fields,
Horner operations, the q^12 scale chain and the 43-operation Pell kernel
are unchanged. Hence

    118-1=117=56M+61A.

No supplied coordinate or equality is deleted. The inherited acyclic
auxiliary-norm correction retains its position. The checker separately
verifies (3), every new source comparison, and the precise primitive
deletion/substitution, rather than counting a symbolic quotient for free.

## 4. Noncircular soundness and numerical zero tests

The program support equations still give

    TC+TV=J+C+V+(Zall-S)H>J.

Together with T+TC+TV+beta=q=2J+1 and positive beta, this proves T<=J
and TC+TV<q before any mask is used. The retained native flag-pair
equations have the same preliminary bounds. Equation (3) restores the
old top source directly. Thus the predecessor's complete preliminary
range proof, strong program-width argument, twelve-field mask, and
field recovery all apply in their established order. This step does
not attempt to infer head support from T alone.

After decoding, D and Z are complementary Boolean head words. Equation
(2) becomes

    T=J-((R-3)/6)D
      =(R/3)H+((R-3)/6)Z.                       (4)

Therefore every block always has the top guard bit. A block with D=0
has all its lower guard bits as well, forcing both numerical tracks to
vanish; a block with D=1 has only its top guard bit. The source-zero
meaning is exactly the original one.

The unchanged count-marker argument makes each program row a singleton,
and the unchanged forbidden zero-target position makes the emitted D
bit equal 1-z_i for that source state. Thus D=0 is equivalent to the
graph's requested zero test. State transitions, sign labels, ordinary
counter values, first-plus input, parity-derived banks and zero target
are all preserved. The previous proof never used the name or polarity
of the fixed Boolean label in its ROM separation argument.

## 5. Positive converse, widths and parity

Take any admissible history of the original labelled graph. Choose R
divisible by the new fixed Rmin and large enough for all its finitely
many counter values. Construct the same true zero word Z and its
complement D=H-Z, and keep both native fields J+Z and J+D. Define T
by (4). Every numerical guard and equation (2) is satisfied.

In the recompiled ROM, use

    V=KC-g Next-h_s Kplus-h_z D.

Each selected output is removed from a one digit without borrowing.
The remaining junk is Boolean and still contains the count-marker
unit digit, so V>0. The forbidden mask remains the same, and both
program Test fields are positive Boolean words.

The last physical source value is one and its sign is minus because
the final numerical value is zero. Its true zero requirement is
therefore z_i=0 and its emitted complement is D=1. Consequently the
last T block is R/3, exactly as in the merged-bound converse. The
unchanged estimate

    T<=q/3+q/(2R)-1/2,
    TC<=J, TV<(KS+Zall)H

and (1) provide the positive beta=q-T-TC-TV. No different endpoint
assumption is needed.

The duration is still an even number of three-register banks. J and H
are even. The two native zero fields still sum to 2J+H, so their parity
is unchanged, independently of the number of actual zero requests.
The program fields have total

    NC+NV+NTC+NTV=2(C+V)+5J+(Zall-S)H,

which is even. Hence the complete twelve-field word is native, has
unit digit two and is even, and the same full fixed-sign43 positive
converse constructs all remaining kernel witnesses.

The new width and recompiled junk may differ from an old particular
witness. The equivalence is of the complete labelled-history relation,
with all positive witnesses explicitly supplied in the converse; it
is not an assertion that the old numerical junk V stays unchanged.

## 6. Universal-family and evidence boundary

The fixed graph produced by the ordinary-input three-counter compiler
is unchanged. Only the table's emitted auxiliary zero label is
complemented, with its numerical interpretation established above.
Thus the cyclic-entry universal quantifiers carry over: for every
recursively enumerable set of positive integers there is a fixed
117-operation system, with one raw positive parameter x and 43
positive existential unknowns, accepting exactly that set. The existing
90-operation universal family remains smaller.

The checker records the full source and primitive count, exact
complement identities, finite tests for both zero-label polarities,
and two complete canonical histories under the recompiled table and
threshold. Enormous Pell coordinates are supplied by the full proven
converse; their hypotheses, not the coordinates themselves, are checked
in those canonical receipts.

The fresh receipt gives 2,040 complete zero-head sets and 14,344
individual block checks, including both constant label choices, and
verifies all state/sign/complement targets in the six fixed program
rows. Its two full canonical histories have 12 and 18 serial blocks,
check all 21 outer residuals, and use a counter width of 1,506 ternary
digits. Their packed words have 343,721 and 515,581 bits and exact
central-binomial valuations 216,864 and 325,296. These are complete
canonical source/mask checks, not an exhaustive search over malformed
joint assignments or a numerical construction of huge Pell coordinates.
