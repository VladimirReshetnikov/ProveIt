# Exact finite factor partitions for the complete Tseytin universal equation

The [source](tseytin_universal_factor_partitions.py) and
[receipt](tseytin_universal_factor_partitions.json) give complete universal
polynomials along this operation/propagated-degree frontier:

|Operations|M|A|Certificate|Comparisons|Positive witnesses|Degree bound|
|---:|---:|---:|---:|---:|---:|---:|
|425|199|226|405|7|65|5868|
|426|198|228|403|8|65|5140|
|428|198|230|402|9|65|3578|
|430|198|232|401|10|65|2720|
|432|198|234|400|11|65|2012|

Every row retains the [complete425 parent's](tseytin_universal425.md)
one fixed positive program parameter and ordinary positive input. For
every computably enumerable positive set T, the parent's effective
recipe supplies the same constant A_T for every row, and each row satisfies

\[
 x\in T\iff\exists z_1,\ldots,z_{65}>0:\ F(x,A_T,z)=0
 \qquad(x>0).
\]

The finite family consists of two word-strong bases, every disjoint
partition of their factors, and either a sum-of-squares finalizer or one
distinguished anchored group. The exponent component, actual 24-tile C2
presentation, fused query loader and all outer history rows remain fixed.
The frontier is exact for the specified propagated-degree objective and
literal schedules. It is not a global arithmetic lower bound or a claim
of exact expanded polynomial degrees. The established 75-certificate /
87-polynomial result is unchanged.

The normalized word-strong subfamily alone has frontier
425/5868, 427/5802, 429/4316. The ordinary word-strong subfamily has
426/5140, 428/3578, 430/2720, 432/2012. All witnesses are retained in both
bases. The accepted-input theorem uses positive extensions; it does not
assert equality of all supplied positive zero tuples across partitions
or bases.

## 1. The two complete factor bases

Use W for the product of the word block's factors, P for the six exponent
factors, and R_i for the ordinary residuals. The normalized base has the
seven word factors, in this order:

    and__R15, and__P17, and__first_unit, and__bs_q,
    and__f_square_minus_one, and__index_unit, and__linear_unit.

The six following exponent factors are

    exp__N0, exp__N1, exp__Ns, exp__N3, exp__Nk, exp__Nl.

The normalized base has six ordinary residuals: the global range bound,
two chronological transports, two padded native inputs, and the fused
loader. Its complete factor/residual ancestor graph has 393 gates,
including every charged fixed-coefficient operation. Product-tree gates
are not part of that ancestor graph.

For the ordinary word-strong base, let Delta denote the word native
`and__A` discriminant, and t=`and__ic2`=i c². Replace the two rows

    Ns=f²−Delta t²,       R16=Delta² t²

by

    Ns=f²−1,             R16=Delta(f²−1),

remove Ns from the unit factors, and retain the paid strong comparison

    t²=Delta(f²−1).                                         (1)

The private multiplication `and__normalized_strong_Q=Delta*t²` disappears.
There are now twelve unit factors, seven ordinary residuals and 392 core
gates. The supplied coordinate list remains exactly the same. Its i has
the ordinary strong meaning rather than the normalized meaning.

This is an existing complete native interface, not an inferred reversal
of an existential theorem. The builder regenerates both complete word
cores from the same computed-field parent through the original or
normalized norm-unit construction and then the
[index/coupled-unit construction](native_binary_index_coupled_units.md).
It checks literal equality of every live native row, factor and native
comparison. The fixed outer graph and the exact sharing and endpoint
substitutions are unchanged. The native theorem applies after a valid
positive word input is restored in Section 3.

For a useful all-integer comparison between the two bases, replace the
ordinary i by Delta times the normalized i, leaving the other supplied
coordinates fixed. If Ns denotes the normalized strong factor, direct
substitution gives

    ordinary strong residual = Delta(1−Ns),
    ordinary auxiliary factor
      = normalized auxiliary factor
        +Delta(Ns−1)(V²−y²).                               (2)

Every other retained factor and ordinary residual is identical. On
positive assignments this forward i change is positive. Equations (2)
are correction identities, not a full off-zero polynomial identity or
an inverse on all positive tuples. The complete normalized strong
construction supplies fresh positive auxiliary coordinates in the other
direction, while preserving the outer accepted relation.

## 2. All partitions and both finalizers are paid

Let f_1,...,f_n be a fixed base's factors. Partition their indices into
nonempty disjoint groups G_1,...,G_g and compute

    U_j=product(f_i : i in G_j).

There are exactly n−g paid product gates. With m ordinary residuals,
the unanchored polynomial is

    F_SOS=sum_i R_i² + sum_j (U_j−1)².                     (3)

For any distinguished group a, the anchored polynomial is

    F_a=U_a*(1+sum_i R_i²+sum_(j != a)(U_j−1)²)−1.        (4)

All arguments are integers. A zero of either finalizer forces every
ordinary residual to vanish and every U_j to equal 1. For (4), the
parenthesized positive integer must divide 1; it therefore equals 1 and
U_a=1. Each individual factor is consequently an integer unit, and

    W*P=product_j U_j=1.                                  (5)

Conversely all individual factors equal to 1 and all ordinary residuals
zero make every plan vanish. No sign is silently dropped.

If c is the number of core gates, the certificate has c+n−g gates and
m+g comparisons. Both displayed complete schedules have the same cost

    c+n+3m−1+2g.                                         (6)

For SOS this is c+n−g plus 3(m+g)−1. For the anchored form, the m+g−1
ordinary comparisons cost 3(m+g−1)−1 for residuals, squares and their
sum, and the final +1, multiplication and −1 cost three more. Here m is
always at least six, so no empty-sum special case is needed. These give
423+2g in the normalized base and 424+2g in the ordinary base. Every
fixed numeral multiplication, subtraction, comparison residual and
finalizer gate is included. Every emitted gate reaches its output.

## 3. The sign filter and universal domain order

Grouping can split the six power factors between several groups. From
(5), all six remain integer units, so the independent
[exponent52 signed projection](pell_fixed_affine_exponent52.md) applies
before any word-history semantics:

    P=+1 implies Q=B^x,
    P=−1 implies Q=B^x/16,          B=2^96.                (7)

On the inherited valid program recipe, the fused loader has modulus
d=B²−1 and program coefficient A=8 A_old, where A_old=h6 modulo d.
Its numerator at the second branch in (7) has one of the two residues

    8(15759360 B+558888960),
    8(24115200 B+550533120).

Both are strictly between 0 and d. The loader comparison requires
residue zero, so P=−1 is impossible. This uses exactly the parent's
coefficient/sign certificate, stored again in the receipt. Hence P=1,
Q=B^x and W=1 for every grouping.

Only now does the same loader force

    I=c2_initial=8 enc8(S phi(beta r_x beta))+6.            (8)

The mathematically restored parent word `(I−6)/8` is a positive integer
and the actual literal query code. Restore the two original endpoint
rows from that word. Every remaining word register, factor and ordinary
comparison is the chosen complete word base. W=1 now invokes its full
semigroup/history theorem. Its C2 query equals `aaa` exactly when x is
in the enumerated set. Thus every positive zero has the correct input
semantics. In particular no word theorem was invoked at an arbitrary
positive I, and no assumption about its being divisible into a word
code was needed before the loader.

For the converse, a true C2 query has a literal finite rewrite history.
The inherited history theorem supplies all positive outer coordinates
and a complete prescribed native extension. Choose the canonical native
extension with checksum, index and coupled-linear factors all +1. The
first, main and auxiliary norms are +1; in the normalized base the fresh
normalized strong norm is also +1. The ordinary base instead satisfies
(1). Independently choose the exponent52 positive extension on the
P=+1 branch, for which all six factors individually equal +1. Equation
(8) supplies the positive fused endpoint and the paid loader equality.
These choices make every group product +1, proving completeness for
every plan, including groups mixing word and power factors.

This establishes accepted-input equivalence. The coupled word theorem
allows a private checksum/index sign restoration, and grouping may
impose stronger sign constraints on those supplied factors. We make no
claim that every parent supplied positive zero passes every grouping.
The single normalized all-factor anchor is an exception with a simple
algebraic statement: reassociating the same full product gives exactly
the complete425 integer polynomial on every supplied tuple.

## 4. Degrees and the exact finite optimization

The normalized factor weights are

    931,2158,503,72,1154,429,429,5,7,14,22,3,3,

with maximum ordinary residual degree r=69. The ordinary weights are

    931,1006,503,72,429,429,5,7,14,22,3,3,

with r=858 because the strong comparison (1) is retained. The two
main-norm cancellation identities in the parent are checked against the
literal source and applied at arbitrary integer assignments. No equality
valid only at zeros is used in degree propagation. Every other register
uses the sum of operand degrees for multiplication and their maximum
for addition/subtraction.

If d_j is the sum of the weights in group j, the objectives are

    2 max(r,d_1,...,d_g)                       for (3),
    d_a+2 max(r, d_j for j != a)               for (4).    (9)

The [existing exact subset DP](neary_woods_universal_joint_and_coupled_partitions.md)
is reused without modification. For a subset M, opt(M,k) is the least
possible maximum group sum over partitions into exactly k groups. Fix
the least index of M in the first chosen nonempty subset A. Then

    opt(M,k)=min_A max(weight(A),opt(M minus A,k−1)),       (10)

with opt(M,1)=weight(M). Enumerating these A removes only group-order
symmetry. Certified lower bounds and attained upper bounds prune states
only when no strict improvement is possible. For each total group count,
the algorithm compares SOS with every possible nonempty anchor subset
and the optimal remaining partition. Its returned objective is therefore
the minimum of (9), not a greedy approximation. Equation (6) makes group
count an exact operation-cost coordinate within each base.

The normalized floor is 4316=2*2158 and is attained by three SOS groups
of weights 2158,1863,1709. An anchored plan omitting the weight2158 from
its anchor exceeds4316. If it contains2158 but omits1154, its bound is
at least2158+2*1154=4466; if it contains both but omits931, it is at least
3312+2*931=5174; if it contains all three, it is at least4243+2*69=4381.
Thus no anchor lowers that floor.

The ordinary floor is2012=2*1006, attained with four SOS groups of
weights931,1006,858,629. An anchor omitting1006 exceeds2012. An anchor
containing1006 has bound at least1006+2*858=2722. This proves its floor.
The receipt also enumerates all8191 and4095 nonempty anchor subsets as
independent exact floor certificates. The combined finite-family floor
is2012, attained at432 operations. No conclusion about other native
bases, alternate arithmetic circuits or actual expanded degrees follows.

## 5. Reproduction and scope of evidence

`base(normalized=True|False)` returns a fresh canonical factor scaffold.
`grouped(base,partition,anchor)` emits any valid disjoint grouping;
`anchor=None` selects SOS. `build(operations=432)` chooses a combined
frontier row; `normalized=True|False` restricts it to a subfamily.
`polynomial_source`, `degree_bound`, `ledger` and `frontier` expose the
complete graph, bound, literal counts and optimal schedules. Canonical
packet guards include source, factors, comparisons, domains, interfaces,
program recipe and semantic flags. No unchanged historical metadata is
used to claim a tuple bijection.

The receipt contains all25 group-count winner ledgers, seven complete
frontier source schedules and their digests, plus ten additional
nonoptimal ordered/anchor plans. The author's separate scalar finalizer
checks give560 complete retained-register/output identities,280 signed.
Sixty-four strong-base forward maps check every retained register and
both corrections (2), including32 signed maps; all32 positive maps keep
the forward coordinates positive. Another64 signed assignments check
the canonical425 complete-polynomial identity. Finite sign enumeration
checks155648 factor-sign assignments and6206 accepted group/filtered-power
patterns; these are sign-algebra tests, not positive Pell zeros.

Independent Bell enumeration checks the reused optimizer on24 smaller
weighted problems through eight factors, covering15885 complete set
partitions. Eighteen malformed plans or canonical-packet mutations are
rejected. Author generation and a separate fresh receipt replay passed.
All six local links and whitespace checks pass. Root
independently reviewed the full proof and source and replayed the receipt,
with no findings. A separate oracle checked73 additional ordered grouping
contexts across both bases and every group count, including438 complete
core/manual-finalizer outputs(219 signed assignments), independent
opcode/liveness ledgers, and both claimed degree floors by exhaustive
anchor enumeration. Its degree propagation separately verifies both
main-norm cancellations. No giant complete Pell tuple is materialized; the
unbounded positive extension follows from the cited component theorems.
