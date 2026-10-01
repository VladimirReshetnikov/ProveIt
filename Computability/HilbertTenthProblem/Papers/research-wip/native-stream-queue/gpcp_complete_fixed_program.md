# Complete fixed-program GPCP equations with ordinary integer input

The [ordinary-input boundary](gpcp_fixed_program_input_bridge.md) and the
[uniform affine-pair history](pcp_uniform_affine_pair_history.md) now compose
into a complete positive-integer Diophantine representation of each fixed
binary-input Turing machine language. The machine must ignore every
permitted leading zero padding. Both the ordinary integer input and the unbounded
common tile word are paid; their independent packing parameters are all
existentially quantified.

The compiler [source](gpcp_complete_fixed_program.py) and
[receipt](gpcp_complete_fixed_program.json) give literal arithmetic schedules,
positive-witness lists, comparisons, final sum-of-squares schedules and exact
degrees. A further paid three-operation input loader makes a single fixed
universal interpreter table represent every recursively enumerable set.
That table is effective but is not numerically instantiated here. The small
34-tile example recognizes positive odd integers and is not a universal table.
The separate universal75/88 arithmetic frontier is unchanged.

## 1. Fixed table, varying ordinary input

Let M be a fixed deterministic Turing machine with finite tape alphabet
containing 0,1 and a blank, start state s and accepting state h. States,
tape symbols and the fresh symbols `[`, `]`, `#` are disjoint. The accepting
state has no ordinary transition. A conventional input-format interpreter
can first normalize leading zeros and supply these conventions for any
recursively enumerable language on positive integers. Acceptance must be
invariant for every permitted n>=max(2,bit_length(x)); eventual invariance
alone would not control all existentially allowed paddings.

`build_for_tm` uses the exact paid boundary's rewriting compiler: local
transition rules simulate each left, right or stay move; boundary rules
extend the represented finite tape by a blank when required; accepting
cleanup erases tape symbols on either side of h. Thus, for any sufficient
padded binary input word b_n(x),

    u_n(x) = [ s b_n(x) ],          v = [ h ],
    M accepts x  iff  u_n(x) =>* v.                         (1)

Every reachable configuration before cleanup has exactly one state and
the two markers. Only the accepting state enables cleanup. This invariant
supplies the reverse implication; the local rule table does not introduce
unrelated computations. The prior boundary proof covers every movement
direction and cleanup. The start and accepting states are distinct.

Take one copy tile (a,a) for every symbol, including #, and one tile
(l,r) for each rewriting rule l=>r. The rule sides are nonempty and do
not contain #. Let sigma and tau denote the two tile morphisms. The fresh
delimiter equivalence proved in the boundary packet is

    exists w: sigma(w) # v = u_n(x) # tau(w)
        iff u_n(x) =>* v.                                  (2)

In its reverse direction, splitting at each # produces successive pairs
of ordinary rewriting regions; the region boundaries match because the
whole words are equal. For a reflexive derivation the copy word for u
works. An empty tile word never solves this boundary: the left word would
start with # while the right word starts with `[`. Therefore the
positive-duration history compiler covers every solution of (2).

Assign distinct digits to the fixed alphabet, reserving digits0 and1 for
the input bits. Choose a fixed width k>=4 large enough for all digits,
R=2^k, and the injective word code

    code(a_1...a_m) = R^m + sum_j digit(a_j) R^(m-j).

Each tile (l,r) gives the paid fixed affine map

    (U,V) -> (R^|l| U + value(l), R^|r| V + value(r)).        (3)

Products by these fixed numerals are charged. Starting from
`(1, code(u_n(x)#))`, a common tile word w ends at

    Ufinal=code(sigma(w)),
    Vfinal=code(u_n(x)#tau(w)).                              (4)

The boundary's terminal comparison is exactly

    R^|#v| Ufinal + value(#v) = Vfinal.                     (5)

Injectivity of code converts (5) into (2). Fixed-length symbol codes are
applied after the symbol-level argument; no unproved binary alignment
condition is used.

## 2. Literal composition and positive projection

The boundary compiler already proves, with positive witnesses, that its
computed `input_bottom` equals `code(u_n(x)#)` for some sufficient n,
and imposes (5). Its recoder uses its own q,P,J,K and two native cores.
The history compiler has a separate duration, base, repunit, selector
family, two histories and one prescribed-AND core. The two geometries
are not identified: n measures input digits and t measures selected tiles.

The composition prefixes every history register and witness by `hist__`
and shares only `Vinitial`, `Ufinal`, `Vfinal`. The endpoints are positive
existential witnesses, so x is the only free input in the direct version.
No output register is declared a free witness and no comparison is hidden.

By default, `Vinitial` is replaced by the already paid `input_bottom`
register, and its defining comparison and positive witness are removed.
This is valid before either native theorem: for positive q,z, the fixed
framing formula

    (code(prefix)*q^k+z)*R^|suffix|+value(suffix)             (6)

is strictly positive. It restores exactly the removed coordinate in a
positive zero of the projected system. The retained-coordinate option
is also provided and has a lower degree.

For soundness, restore (6) if projected. Apply the complete input recoder
and complete history theorems independently. Their endpoints satisfy (5),
so (2) and (1) give acceptance. For completeness, an accepting computation
has a finite rewriting derivation and a nonempty common tile word.
Choose any sufficient recoder padding n. Its complete positive converse
supplies the first two native cores. The independent history converse
chooses a large enough dyadic height and supplies its third native core.
The disjoint auxiliary lists create no compatibility condition. Together
they satisfy every comparison, and hence the final sum of squares.

These are parametric positive-witness arguments. The executable fixtures
materialize outer histories and truthful AND interfaces but leave the
astronomical native Pell coordinates as explicit placeholders.

## 3. Costs and degree

Write s for the number of fixed tiles, H for the history certificate's
actual operation count, and

    ell(k)=floor(log2 k)+popcount(k)-1

for the boundary's paid binary power-chain length. The raw full compiler
has the following exact counts, before any optional program loader:

| Initial endpoint | Certificate | Comparisons | Positive witnesses | Final polynomial |
|---|---:|---:|---:|---:|
|Supplied Vinitial|H+134+ell(k)|55|3s+79|H+298+ell(k)|
|Computed Vinitial, default|H+134+ell(k)|54|3s+78|H+295+ell(k)|

Every comparison is finalized by a paid subtraction and square, followed
by the paid sum. The ordinary x is a free positive input, not counted
as a witness. Both endpoint alternatives and both physical layouts are
compiled, so operation and degree tradeoffs remain visible.

Let N=3s+4 for the contiguous layout and N=4s+4 for the interleaved layout.
The exact total degrees of the complete sum-of-squares polynomial are

    supplied Vinitial: max(24N+16, 2k+2),
    computed Vinitial: 12(k+1)N+16.                         (7)

The source checks structural upper degrees for all residuals and evaluates
their leading homogeneous forms on a positive weight vector. A nonzero
sum of squared leading values proves attainment. It records a hash and
bit length for the potentially large leading coefficient. This audit
uses no zero-set relation such as q=2^n or P=B^t. It is applied to the
actual composed source, including optional loaders.

For the illustrative odd-integer recognizer, k=4 and s=34. Its ledgers are:

| Layout / initial endpoint | Certificate | Equations | Witnesses | Polynomial | M+A | Degree |
|---|---:|---:|---:|---:|---|---:|
|Contiguous / supplied|835|55|181|999|427M+572A|2560|
|Contiguous / computed|835|54|180|996|426M+570A|6376|
|Interleaved / supplied|832|55|181|996|423M+573A|3376|
|Interleaved / computed, default|832|54|180|993|422M+571A|8416|

The automatic choice minimizes the literal history operation count,
then uses smaller scale exponent and multiplication count as tie-breakers.
These numerical counts concern this small decidable example only.

## 4. One fixed interpreter, with a paid program loader

Fix a universal interpreter Mstar on positive integer input N. It ignores
leading binary zero padding, decodes

    p=v_2(N),             x=(N/2^p-1)/2,

and accepts exactly when program p accepts x. A fixed ordinary Turing
machine implements this effective decoding and universal simulation.
The previous construction therefore gives one fixed alphabet, tile table
and polynomial for Mstar, independent of the program chosen later.

With two free positive parameters x and program_code, the literal loader
computes

    twice=x+x; odd=twice+1; N=program_code*odd.             (8)

Its cost is exactly **3=1M+2A**. For each recursively enumerable language,
choose an index p and specialize `program_code=2^p`. Then v_2(N)=p and
the decoded argument is x. Consequently this one fixed polynomial is
universal with a positive program parameter. Non-power-of-two values of
the parameter merely define additional recursively enumerable slices.
The claimed universal slices use the stated power-of-two constants.

If a program numeral C=2^p is fixed when compiling, the equally paid
loader `N=(2C)*x+C` costs **2=1M+1A**: 2C is a fixed numeral, and its
multiplication by x still costs one gate. This specializes the same
interpreter without changing its table.

The parameter version has polynomial degree2 in x and program_code,
while the fixed-numeral version is affine in x. Both are included in the
literal degree audits. In this raw compiler q remains a supplied recoder
witness; for k>=4 neither loader changes the exact maximum degree(7).
Later projections that inline q must recompute the degree.

No explicit universal interpreter transition table is supplied in this
packet, so it does not give a numerical universal operation bound.
What is closed here is the complete fixed-program, ordinary-input,
unbounded-history representation, with an effective and fully paid
universality interface.

## 5. Reproduction and limits

Run `gpcp_complete_fixed_program.py` in the research environment with
SymPy available. `--write` regenerates the checked-in receipt. The default
audit checks 384 complete residual/SOS identities, including192 signed
assignments, across both layouts, both initial-endpoint conventions,
two widths and all three loader modes. It also checks29 exact degree
ledgers, twelve genuine outer machine/word/matrix/history runs and1024
independent universal-loader decoding cases. The degree audits include
a one-tile, width100 case where the boundary degree dominates.

Signed checks establish literal source identities, not signed-witness
kernel theorems. Outer machine fixtures check both accepting and rejecting
inputs; only accepting ones satisfy the terminal comparison. All native
extensions are justified by the component proofs above. There is no Lean
formalization or optimality claim.
