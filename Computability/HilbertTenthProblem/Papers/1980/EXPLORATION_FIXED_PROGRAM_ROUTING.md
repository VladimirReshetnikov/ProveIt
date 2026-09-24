# Fixed program lookup and time wiring in one equation

A fixed finite successor table can be enforced by a five-operation
arithmetic equation, with five further operations for its two support
tests. Its cost is independent of the number of states because all table
coefficients are fixed numerals. With bounds, packing, power recovery and
the existing ternary Pell kernel included, this gives a complete
**70-operation deterministic finite-graph history component: 39 products
and 31 additions/subtractions**. It has one positive parameter q,
24 positive unknowns and 17 equations.

This component proves finite control routing, not universal computation.
A deterministic finite graph is eventually periodic. Counter-dependent
branch selection, register selection, zero tests, raw input and a faithful
halting condition remain separate. Section 8 distinguishes the fixed-frame
component from the variable-width interface needed by counter histories.
No universal frontier is changed.

The complete schedule and fresh source comparisons are in
`../verification/explore_fixed_program_routing.py`, with its JSON receipt.
The checker instantiates a small fixed table, and separately checks the
general coefficient construction on all successor maps of two and three
original states. Fixed numerals may be large; evaluating a multiplication
by one still costs an operation.

## 1. A fixed table encoded without self-loop contamination

Let f be a fixed function on a finite state set. First replace each state
i by (i,epsilon), epsilon in {0,1}, and replace the successor by
(f(i),1-epsilon). The enlarged function has no fixed points, including
when the original program instruction loops to itself. This transformation
only changes the finite constant table. Fix initial and final states of
the enlarged graph, denoted i0 and i1.

Number its m>=2 states from zero and choose the integer *exponents*

    a_i=3^i, d=max_i a_i.

They form a Sidon set: equality a_i+a_j=a_k+a_l determines the same
unordered pair of indices, including repeated indices. This follows
directly from uniqueness of ternary digits, whose coefficients in these
sums are at most two.

Define the fixed integer numerals

    S=sum_i 3^(a_i), g=3^d,
    K=sum_i 3^(d+a_f(i)-a_i),
    I=3^(a_i0), F=3^(a_i1).                         (1)

All exponents in K are nonnegative. Its exponents are distinct. Indeed,
an equality a_f(i)-a_i=a_f(j)-a_j gives equality of two Sidon pair sums.
Either i=j, or both edges are fixed points; the latter is excluded.
Thus K itself is a ternary Boolean numeral.

Choose an even positive integer B so large that W=3^B satisfies

    W>max(K*S,g*S,2*S+1).                           (2)

This is a choice of a fixed numeral for the fixed program, not a
variable exponent operation. Such a B is finite and effectively
constructible. The values W,K,S,g,I,F and their fixed products and
differences are all literal numeral inputs to the arithmetic schedule.

For a single selected state i, the coefficient of the formal product

    K(T)*T^(a_i)

at target exponent d+a_j is exactly 1 if j=f(i), and 0 otherwise.
An individual summand can reach that target only if

    a_i+a_f(k)=a_j+a_k.

The Sidon alternatives are k=i with f(i)=j, or i=j with f(k)=k.
The latter is the self-loop contamination removed by the phase split.
Since K(T) has distinct exponents, its product with a single monomial
has only zero-one coefficients: this coefficient statement is also
valid for the normalized integer product in radix three.

## 2. Row geometry and two exact support tests

Supply positive H,Rep,C,V,TestC,TestV,alpha and the seventeen retained
positive Pell variables. The length q is a positive parameter. Impose

    q=(W-1)*H+1,
    Rep=((W-1)/2)*H,                                (3)
    C+Rep=S*H+TestC,
    V+(g*S)*H=TestV,                                (4)
    TestC+TestV+alpha=q.                             (5)

The coefficient (W-1)/2 in (3) is a fixed integer numeral, not a
division instruction. Equations (3), (4), and (5) cost respectively
three, five, and two operations.

Before power or digit decoding, H>0 gives q>=W and
Rep=(q-1)/2. Condition (2) gives S*H<Rep. Thus (4)-(5), using only
positive supplied variables, give

    0<C<TestC<q, 0<V<TestV<q.                        (6)

All four fields are therefore bounded before being packed. No independent
comparisons or assumptions of carry-free concatenation are being used.

After the kernel proves q is a power of three, (3) and W=3^B imply
q=W^t for some t>=1. Hence H=1+W+...+W^(t-1), while Rep is the
full ternary repunit below q. S*H repeats the fixed set of source
positions in every row, and (g*S)*H repeats the target positions.
Condition (2) places both inside their rows.

Once C,V,TestC,TestV are Boolean, the first equality in (4) can be
written TestC=C+(Rep-S*H). Both summands have raw digits at most one.
Their sum has no ternary carry, and TestC's Booleanity forces C to
be supported on S*H. Similarly TestV's Booleanity forces V to avoid
all positions of (g*S)*H. These are exact digitwise support and
disjointness tests. Neither uses an unbounded product as if it had
already been normalized without carries.

## 3. The merged routing equation

Impose the single equation

    (W*K-g)*C+g*I=(g*F)*q+W*V.                     (7)

The three products and two sums cost five operations. In particular,
W*K-g and g*F are fixed numerals. No variable-width program table is
treated as a free input here.

To see its meaning, temporarily introduce the mathematical next-state
word Next. Ordinary lookup and time wiring would be

    K*C=g*Next+V,
    C+q*F=I+W*Next.                                (8)

Eliminating Next yields (7). The elimination must be justified in the
reverse direction because g and W are not relatively prime. The next
section supplies exactly that check; it is not a formal cancellation
of an arbitrary congruence.

## 4. Bounds and mask: all 70 operations

Pack the four fields as

    P0=C+q*V+q^2*TestC+q^3*TestV.                   (9)

Six Horner operations construct (9), and (6) proves 0<P0<q^4.
Append the unchanged 49-operation component from
`EXPLORATION_BASE_THREE_PELL_KERNEL.md`:

    L=q^4, D0=9L, r=D0-3P0-1,

with its explicitly counted powers and 43 Pell primitives. Its
soundness implication proves q is a power of three and all four
bounded fields are ternary Boolean. The complete count is

| Part | Operations |
|---|---:|
| Fixed row geometry and repunit (3) | 3 |
| Two support tests (4) | 5 |
| Merged lookup and time (7) | 5 |
| Shared bound (5) | 2 |
| Four-field packing | 6 |
| Lower-half ternary mask and Pell kernel | 49 |
| Total | 70 |

All seven outer witnesses are positive; no zero-valued variable is
silently supplied as a positive unknown. There are six outer source
equations and eleven mask/kernel equations. The exact checker compares
all seventeen fresh source polynomials with the acyclic primitive
schedule. Its sole triangular adjustment is the inherited penultimate
Pell residual adjustment.

## 5. Soundness, including normalized ROM multiplication

Decode geometry and support as in Section 2. Every base-W row of C
is a subword of S and is therefore at most S. By (2),

    K*(each C row)<=K*S<W.                          (10)

Consequently the integer product K*C has no carry between time rows,
even if a malformed C row initially contains several state bits.
Internal ternary carries in such a row are not yet ruled out.

Reduce (7) modulo W. Since q is divisible by W and g divides W,
its lowest row c0 satisfies c0=I modulo W/g. Both c0 and I are
at most S<W/g by (2). Thus c0=I as integers. Define

    Next=(C-I+q*F)/W.

This is a positive integer. Its rows are the later C rows followed
by the single final row F, so it is Boolean, supported on S*H, and
smaller than q. Substituting into (7) gives exactly K*C=g*Next+V.
The words g*Next and V are Boolean and have disjoint supports by (4).
Their sum is therefore carry-free in radix three.

The first C row is the single monomial I. Its K product is Boolean,
and the target coefficient calculation in Section 1 proves the first
Next row is exactly the successor of i0. It follows that the second
C row is one-hot. Repeat through all time rows, using (10) to prevent
inter-row carries at each stage. Every C row is one-hot, every transition
is f, and the final row F is reached after exactly t steps.

Thus, for arbitrary positive q, this complete system has positive
witnesses only if

    q=W^t for an integer t>=1, and f^t(i0)=i1.       (11)

The proof did not assume a one-hot history, a prime-power input length,
or a carry-free constant-table product in advance.

## 6. Positive necessity and automatic parity

Conversely assume (11). Let C contain its one-hot state rows and let
Next contain their successors. Define V=K*C-g*Next. In each row the
integer K product is a shift of the Boolean numeral K, with exactly
one of its m terms at a tested target. Removing that term leaves a
Boolean row avoiding all targets. Since m>=2, each junk row is
nonzero. Therefore V>0.

Set H,Rep from (3) and TestC,TestV from (4). They are Boolean and
positive. TestC contains the complement of S*H and the selected source
positions; the complement is nonempty by (2). TestV contains the
nonempty target mask and the disjoint junk. Every Boolean word below q
is at most Rep, so TestC+TestV<=2Rep=q-1. Hence the required
alpha=q-TestC-TestV is a positive integer. All outer equations hold.

The packing needs the even parity used by the existing positive Pell
converse. It is automatic and does not require a duplicate field:

    C+V+TestC+TestV
       =2(C+V)+Rep+(g-1)*S*H.

The last term is even, and Rep=((W-1)/2)H is even because B was
chosen even. Also q is odd. Thus P0 in (9) is even, and so is
r=9q^4-3P0-1. The Boolean mask supplies central-binomial divisibility,
and the existing positive converse constructs all seventeen Pell
witnesses. This proves the converse of (11).

No enormous Pell tuple is numerically instantiated. Its existence
uses the already proved general formulas, with all hypotheses supplied
by this component.

## 7. Finite evidence

The exact coefficient regression checks 1,036 source/target pairs over
all successor maps on two and three original states, each expanded by
the phase bit. It checks the actual Sidon target equality and excludes
every unintended summand. Ninety-six canonical histories separately
verify all outer equations, positive slacks and exact central-binomial
valuations.

An adversarial finite check enumerates all 16,384 two-row source-support
subset histories for two-state maps and all fixed initial/final choices.
The rows may have no head or several heads. It solves (7) for V, tests
the positive source equations and complete packed-mask valuation, and
finds exactly sixteen accepted candidates, all the correct deterministic
paths. These finite checks support the general proof; they are not an
exhaustive search over arbitrary encodings or all integer tuples.

## 8. What can and cannot be shared with a counter machine

The useful result is the constant-sized lookup and support interface,
not the computational power of (11). Every fixed deterministic finite
graph is eventually periodic. The 70-operation relation alone has no
unbounded data-dependent branch and is decidable.

For a counter instruction with two possible successors, it is not sound
to put both edges into K and retain the same proof. A selected source
would then produce both targets. The disjointness test forces both into
Next; it does not choose one according to whether a counter is zero.
Likewise, replacing a source by a chosen instruction/branch label
requires a paid link proving that the label matches the counter test.
These are explicit remaining control obligations.

The table itself can remain a fixed numeral when control positions stay
at fixed offsets but counter bits occupy an expanding part of each
time frame. If that frame radix is a variable R instead of fixed W,
the natural merged equation is

    (R*K-g)*C+g*I=(g*F)*q+R*V.                    (12)

Now R*K-g is not free. Constructing it adds one product and one
subtraction, making (12) seven operations rather than five. The fixed
support words S,K,g are still numerals; no R-dependent instruction
polynomial was introduced. A proved frame bound
R>max(K*S,g*S,2*S+1) restores the same no-carry argument, but that
bound and the variable-frame geometry must be charged or deduced from
other source equations. Simply declaring such a bound would be circular.

A possible next interface uses branch-event labels, their fixed ROM
successors, and separately verified zero/nonzero and register-selection
events. It must also connect the raw input stream and an accepting
instruction. The current counter-history components only increment on
every row, so arbitrary activation and mixed increment/decrement remain
unsolved as well. The five-operation identity is a concrete sharing
opportunity; it is not a completed universal program compiler.
