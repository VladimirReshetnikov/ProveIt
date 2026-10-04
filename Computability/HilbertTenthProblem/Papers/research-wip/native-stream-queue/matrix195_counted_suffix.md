# A counted suffix gives an exact ordinary-input matrix target

The context-absorbed 193-generator construction admits an exact lift to **195 integer matrices in dimension seven**, with a target whose only varying entry is the ordinary input x itself. Its target assembly uses **zero arithmetic gates**: every entry is a fixed numeral or a direct copy of x. A three-coordinate control block forces exactly x copies of the repeated input matrix in the witness word. Consequently the separate external Pell-index relation disappears.

This is a change of computational substrate, not a lower arithmetic bound for a universal Diophantine polynomial. The new matrices are singular, the dimension rises from four to seven, and an accepting word gains x+1 factors. Encoding an arbitrarily long product with a fixed number of integer witnesses remains unpaid. The proved universal polynomial bound remains 84 operations. The program-specific alphabet retains the inherited effective initialization theorem; this packet does not implement the arbitrary-program compiler.

## Exact fixed-program construction

Use the [fixed-context source](matrix193_context_absorption.md). For each fixed program it gives 193 integral block matrices M_i with invertible 2 by 2 upper and lower blocks, and a fixed matrix

    B = Psi((01010111)^2).

The inherited equivalence is

    x belongs to S
      iff some nonempty product M equals diag(B^(-x),P),
    P = [[1,2],[0,1]].                                      (1)

Here x is the original positive input. The [initialization theorem](u15_unary_block_interface.md) and context transfer provide the effective fixed-program numeral recipe for every c.e. set S. In the saved concrete fixture the contexts are U="[110", V="A0]", and

    B = [[-52109,29036],[-94920,52891]].

That illustrative fixture is not asserted to be the initialized program for an arbitrary selected S. The construction below applies to every alphabet supplied by (1).

Let E_ij denote the 3 by 3 matrix unit with zero-based indices. Set

    O = E_00,
    F = E_01,
    D = [[0,0,0],[0,1,1],[0,0,1]].

For each old generator emit

    L_i = diag(M_i,O).

Emit two further fixed generators

    END   = diag(I_4,F),
    COUNT = diag(diag(B,I_2),D).                            (2)

The new input target is

    T(x) = diag(diag(I_2,P), F + x E_02).                    (3)

All 195 matrices are integral and are fixed after choosing the program. No input-dependent generator is present. The inherited generators have rank five, END has rank five, and COUNT has rank six; in particular this is a directed semigroup of singular integer matrices, not an SL(7,Z) representation or a mortality construction. The target has rank five.

## The control block proves the exact count and order

For an arbitrary word over the three control letters O,F,D, its product has entry (0,1) equal to 1 if and only if its spelling is

    O^n F D^k,       n,k >= 0.                              (4)

On this language its entire product is

    F + k E_02.                                            (5)

To prove this for words of any length, O is an idempotent supported only at coordinate 0; D is supported only at coordinates 1 and 2. Their mixed products in either order are zero. The only letter linking coordinate 0 to those coordinates is F. Before F, a D kills the product; after F, an O or a second F kills the product. Words containing no F have entry (0,1) zero. Finally the lower-right block of D is [[1,1],[0,1]], whose kth power is [[1,k],[0,1]]. This proves (4) and (5), including empty O and D parts. The empty word has control I_3 and does not pass the required entry.

Thus any product of the matrices (2) equal to (3) must have the literal shape

    L_(i1) ... L_(in) END COUNT^k,

and (5) forces k=x exactly over the integers. This is an equality of a literal occurrence count with the input, without a congruence or hidden exponent witness. If n were zero, the lower physical 2 by 2 block would be I_2, contradicting P. Hence the old prefix is nonempty, as required by (1).

For a shaped word, its complete product is

    diag(M_(i1)...M_(in) diag(B^k,I_2), F+k E_02).          (6)

Since B is invertible, at k=x equation (6) equals (3) exactly when the old product is diag(B^(-x),P). Conversely every old witness gives a new witness by appending END and exactly x copies of COUNT. This proves

    T(x) belongs to the new directed semigroup
      iff diag(B^(-x),P) belongs to the old one.             (7)

Together with (1), (7) is an exact ordinary-input universal family of fixed-program matrix membership predicates. The word maps are explicit in both directions. An old word of length n becomes a word of length n+1+x. The statement also holds at x=0; the represented c.e. language is still stated on positive inputs.

Singular control is safe here because the target has a specified nonzero control entry. Invalid words may produce a zero control block, but then cannot equal the target. This argument would not establish a mortality theorem with target zero.

## Target arithmetic and a seven-observation interface

The complete target is

    [[1,0,0,0,0,0,0],
     [0,1,0,0,0,0,0],
     [0,0,1,2,0,0,0],
     [0,0,0,1,0,0,0],
     [0,0,0,0,0,1,x],
     [0,0,0,0,0,0,0],
     [0,0,0,0,0,0,0]].

Its straight-line source is empty. The single supplied port x reaches an output by copying; there is no multiplication by one or addition of zero. Thus the complete target loader has 0 M + 0 A operations, no auxiliary witnesses, and degree one. The full product predicate, its comparisons and the arithmetic of every selected transition are excluded from this loader ledger and still require a complete certificate.

The parent first-row theorem also allows an exact seven-observation interface on products of this fixed alphabet. In zero-based positions require

    (0,0),(0,1) = 1,0;
    (2,2),(2,3),(3,2) = 1,2,0;
    (4,5),(4,6) = 1,x.                                    (8)

The control pair first forces the shape and count, including its entire control matrix. Every lower physical block has determinant one, so the three lower observations force its remaining entry to be 1. Every upper physical block belongs to the inherited H', because both the old blocks and B do. The existing injectivity of the first-row map on H' therefore forces the full upper block to be I_2. All off-diagonal block entries are identically zero. These arguments establish (8) if and only if full equality to (3), only for products of the emitted alphabet. They do not assert these observations determine arbitrary 7 by 7 matrices.

This bypasses the recently proved three-gate target floor by changing the dimension, alphabet and witness language. It does not contradict that floor for generic Pell-coordinate target assembly under whole-group basis changes.

## Complete fixture and fresh evidence

The [saved receipt](matrix195_counted_suffix.json) contains all 195 full 7 by 7 matrices, the target copy template, and four complete accepting words and products. The [fresh helper](matrix195_counted_suffix.py) authenticates the context-absorption source, receipt and proof, plus the directed-semigroup and ordinary-input proofs. It reads them as data and executes none of their code.

| Resource | Context-absorbed parent | Counted-suffix fixture |
|---|---:|---:|
| Generators |193|195|
| Matrix dimension |4|7|
| Entry slots |3,088|9,555|
| Nonzero entries |1,543|1,750|
| Maximum magnitude bits |72|72|
| Sum of magnitude bits |53,734|54,001|
| Target assembly |3 gates from indexed Pell ports|0 gates from ordinary x|
| Separate external index relation |unpaid|required count enforced by the word|

The two loader counts have different supplied-port contracts; their comparison is not an end-to-end arithmetic saving. The alphabet grows, and no entry-bit improvement is claimed.

The newly reconstructed accepting examples are:

| Ordinary x | Rewrite steps, including cleanup | Inner tiles | Lifted factors |
|---:|---:|---:|---:|
|0|12|83|168|
|1|44|843|1,689|
|2|76|2,371|4,746|
|3|108|4,667|9,339|

The finite control audit evaluates all 29,524 words of length at most nine, including invalid orders, absent and repeated END letters, and both empty boundaries. It compares literal matrix multiplication with an independent O* F D* spelling test. A further 384 full block identities compare direct 7 by 7 multiplication with (6), including old prefixes whose lower block does not meet P. These tests corroborate the unrestricted proof above; they are not its basis.

The historical accepted 167-factor word becomes a 168-factor word at x=0. Separately, the helper freshly simulates the actual 91 literal rewrite rules on U (W^2)^x V for x=0,1,2,3. Before halt it checks unique enabled machine rewriting; after halt it chooses legal binary cleanup rules. It constructs all context-copy tiles, checks the full literal correspondence equation, emits the A/C/reversed-B word and the counted suffix, and evaluates every entry of the resulting 7 by 7 product. Wrong input targets, an incorrect phase order and repeated END are explicitly rejected. No arbitrary-program initialization is executed, and no nonhalting claim is inferred from these accepting examples.

The helper uses explicit exceptions, strict dependency byte hashes, duplicate/nonfinite JSON rejection and recursive type-exact receipt comparison. Replay from any directory is

    python3 matrix195_counted_suffix.py --root ABS_WIP --expect ABS_JSON
    python3 -O matrix195_counted_suffix.py --root ABS_WIP --expect ABS_JSON

The mutually exclusive --output FILE writes a deterministic receipt. These are bounded exact matrix and rewrite checks. There is no complete Diophantine source yet, and no operation bound is inferred from either the fixed number of matrices or the empty target source.
