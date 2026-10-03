# Four branching physical rows: selectors58, FIFO66, centered carry71

The rows `0->0`, `0->1`, `1->2`, `2->0` escape the unique-output
hypothesis of the [read-functional obstruction](native_read_functional_controller_regular.md).
This note gives an exact **58-operation four-selector predicate** and an
exact **66-operation ordinary-input FIFO predicate** for these rows. A
centered scalar affine controller costs five more operations, but the
resulting **71-operation family is not universal**: any such controller
accepting every positive even ordinary input accepts every positive input.

An arbitrary finite controller and this specific affine controller are
different interfaces. Universality of a coded finite-control simulator does
not certify its controller in five operations. The complete universal
certificate bound remains75.

## 1. Four true selectors with a derived fifth field

Supply positive q,F0,F1,F2,F3 and the seventeen positive coordinates of
the44-operation raw Boolean ternary kernel in
[the existing Boolean source](input_bridge_boolean_ternary60.md), together
with positive bound_beta. Compute

    G=F1+F2, H=F0+G+F3, q_calc=H+H+1,
    r_packed=F0+qF1+q^2F2+q^3F3+q^4G,
    X_bound=r+bound_beta.

Require q_calc=q, r=r_packed and X_bound=X, where the raw kernel uses
`X=wq`, `Y=3s+1` and its unchanged ten equations. G and H are computed
registers; they are not extra existential witnesses or free assertions.

The exact projection is:

    q=3^t,
    Fi=sum_(j<t) [label_j=i]3^j, labels in {0,1,2,3},
    every label occurs,
    H+G is even, where H=(q-1)/2 and G=F1+F2.             (1)

All bounds precede power recovery. Positivity and q=2 sum Fi+1 give
q>=9 and 0<Fi,G<q. Therefore the actual packed integer satisfies

    q^4+q^3+q^2+q+1 <= r < q^5,
    X>r, Y>=4, E=XY>r+1,
    a=Y(X+1)>2r+1, P=2XY^2+1>A=a+3.

The raw-kernel bootstrap in
[raw Boolean fields, Section1](native_controller_raw_boolean_gates.md)
uses X>r and these lower bounds, not a bound r<q^4. Its first index is
at least r+1, its main index is at least r+2, and hence the relaxed-rank
and signed-parity thresholds hold. The same index, ratio, and exponent
arguments recover main index2r+1, even r, X=3^(2r+1), and

    Y=floor((X+1)^(2r)/X^r), q=3^t.

Since Y=1 modulo3, the binomial criterion gives Boolean ternary digits
throughout r. Each of the five q-sized fields was already bounded by q;
there are no field carries, so Fi and G are all Boolean ternary words.

Now G=F1+F2 gives coefficientwise equality: each discrepancy belongs
to[-1,2], which contains no nonzero multiple of3. Thus F1 and F2
are disjoint. The same least-nonzero-digit argument applied to
`F0+G+F3=H` gives a three-way partition of every position. These two
facts give exactly four-way one-hot selectors. The even packed index
is equivalent to H+G even because q is odd.

Conversely selectors satisfying(1) make all five packed fields Boolean
and the packed r even. The raw-kernel positive converse applies with
X=3^(2r+1), the displayed binomial floor, w=X/q,
s=(Y-1)/3 and bound_beta=X-r. All are positive integers. The remaining
positive Pell witnesses are supplied by that same constructive converse.
This establishes both directions for all admissible indices, not merely
for the finite test examples.

The checksum costs5 additions, Horner packing4 products and4 additions,
and the X bound one addition. With the raw44 kernel this is
**58=29M+29A**, with13 equations and23 positive coordinates in total.

## 2. A complete finite FIFO predicate on ordinary2x

Interpret the four labels as the displayed rows, in their listed order.
The read and append streams are the computed registers

    D=F2+2F3, A=G+F2=F1+2F2.

These are genuine ternary digit words: one-hot selection excludes carries
in their definitions. Supply positive ordinary input x and positive W,
width_beta,L, and require

    I=x+x, D=I+WA, I+width_beta=W, q=WL.                (2)

The factorization and q=3^t give W=3^m for0<=m<=t. Since0<2x<W,
we have m>=1. The standard finite FIFO identity

    D+3^t*final=I+W*A

then proves that(2) is exactly a t-step run of the stated four physical
rows, from the width-m ordinary ternary queue encoding2x to the all-zero
queue. Conversely such a run supplies all three positive new witnesses.
The input is ordinary x; no variable radix conversion has been assumed.

There is a useful exact parity consequence. From(2), modulo2,

    D-A=2F3-G is even, so G is even.

The selector kernel gives H+G even, hence H even, which is equivalent
to t even. Thus the precise finite-run predicate requires an even number
of steps and at least one use of each of the four rows. These are explicit
conditions, not missing exceptional cases of the converse.

The suffix computes A in one addition, D in two additions, I in one
addition, transport in one product and one addition, the width in one
addition and geometry in one product. It costs8 operations. The complete
source is **66=31M+35A**, with16 equations and26 positive existential
coordinates besides x. All supplied coordinates occur in its polynomials.
The exact DAG and independently expanded residuals are in the
[checker and receipt](native_four_row_fifo66.py).

This source accepts every positive x when no controller is attached.
For a constructive witness choose an even m with3^(m-1)>2x. In the first
queue sweep send one high padding zero through0->1; leave other zeros
unchanged, and apply1->2 and2->0 wherever forced. During the second and
third sweeps leave all zeros unchanged. The marked pulse follows1->2->0;
every original symbol has also become zero by the end of sweep3.
Since m>=2, any other cell is zero by its third visit and uses0->0
then. The marked pulse supplies the other three rows, so all four occur.
The total time3m
is even. This provides all the outer witnesses and, by Section1, all
positive kernel witnesses. It supplies erasure, not selective acceptance.

## 3. The five-operation centered controller

For fixed signed integers a,b,c,g, add

    aF1+bF2+cF3=g.                                     (3)

Three products and two additions give **71=34M+37A**,17 equations and
the same26 positive witnesses. Equality(3) is exactly the integral carry
path

    3k_(j+1)=k_j+lambda_(label_j),
    lambda=(0,a,b,c), k_0=-g, k_t=0.                    (4)

To prove the converse from(3), reduce the weighted sum successively
modulo3; each required numerator is divisible by3 and the final carry
is zero. Conversely(4) telescopes to(3). Carries may be signed, but
are mathematical decoded states, not new positive witnesses. They stay
in a computable finite range by the contraction in(4). Label0 fixes
the zero terminal carry, so this is the zero-absorbing, centered affine
controller family. It is not every finite-state controller or every
affine controller with a nonabsorbing terminal state.

## 4. Symbol transports obstruct universality of71

Let I1,I2 be the Boolean ternary indicator words of initial symbols1,2,
so I=I1+2I2. Only label1 appends1, and only label2 appends2. The
same finite FIFO identity applied to each symbol-indicator lane gives

    F2=I1+W*F1, F3=I2+W*F2.                            (5)

No operation is removed or treated as free here: these are consequences
used in the proof. Substitute(5) into(3):

    (a+bW+cW^2)F1+(b+cW)I1+cI2=g.                     (6)

Suppose the controller accepts infinitely many inputs
`x_n=(3^n-1)/2` for even n. These are ordinary positive even integers.
Their initial queues have n low trits all equal to2, followed by zero
padding. Thus I1=0, I2=x_n and W>2x_n, with W tending to infinity
along the accepted instances. Equation(6) becomes

    (a+bW+cW^2)F1+c*x_n=g.                            (7)

If c is nonzero, then for all sufficiently large W its quadratic
coefficient has sign c. Both terms in(7) have sign c, and the absolute
value of the second tends to infinity. This contradicts fixed g. Hence
c=0. If b is nonzero, then |a+bW| tends to infinity and F1>=1, again
contradicting(7). Hence b=0.

If a is nonzero, then F1=g/a is one fixed positive integer on every
accepted run. But the first n physical reads are all2, so none can use
label1. Its first n selector digits vanish; equivalently3^n divides F1.
No fixed positive F1 has this property for unbounded n. Therefore a=0,
and(7) also gives g=0.

We have proved that accepting infinitely many of this explicit sequence
forces the controller to be trivial. In particular any71 controller
accepting all positive even ordinary inputs has a=b=c=g=0. Section2
then supplies witnesses for every positive input. A proper computably
enumerable set containing all positive even integers, such as their union
with a proper nonrecursive computably enumerable subset of the odds,
cannot be represented by this71 family.

This is not a lower bound on all arithmetic encodings of these four
rows, nor on nonabsorbing, nonlinear, or separately guarded controllers.
It identifies precisely why the five-operation centered controller is
insufficient even when the physical rows support a richer coded machine.

## 5. Verification boundary

The checker verifies every source residual of58/66/71 against the literal
DAG, preserving the inherited auxiliary-norm correction. It checks9,360
arbitrary positive checksum tuples,153,360 independent supplied-input,
label-word and width combinations, and positive erasing constructions for
200 ordinary inputs. Accepted finite FIFO instances also verify(5), and
the carry checker compares the scalar equation with every local integral
carry step. None of the finite checks materializes the enormous Pell
witnesses; their existence follows from the retained constructive proof.

The universality exclusion in Section4 is parametric and uses arbitrarily
long input blocks. Finite experiments alone would not prove it. Independent
proof and source review passed, including3,876 additional pre-power tuples
and4,375 centered all-two-input necessary-equation checks. No Lean
formalization or improvement below complete75 is claimed.
