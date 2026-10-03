# Native dual-rail FIFOs with ordinary input in 65 operations

The final refinement costs **65=33M+32A**. It places the required
origin bit on the append stream and computes only q-1 for the shared
offset. The67 and66 references first establish transport, typing and
ordinary-input semantics. A general Boolean-filtered affine carry
controller then fits a literal75 architecture; its universality is open.

The four-field typing relation composes with an ordinary-input queue in
**67=33M+34A**, with 19 equations and 24 positive auxiliaries beyond
seven positive parameters. The initial queue contains the ordinary
integer `6x+2`, without converting x to a sparse numeral or exponent.
Each read and append trit is represented as the sum of two Boolean
trits. The component has no synchronized controller: by itself it
admits every positive input. The complete universal bound remains76.

## Exact source and projection

Use positive parameters x,W,q,F0,F1,F2,F3 and the complete
[57-operation four-field source](native_controller_four_fields55.md),
including its supplied positive H and computed 2H. Add two positive
coordinates beta,L. Define arithmetic registers

    D=F0+F1-2H, A=F2+F3-2H, I=6x+2,

and impose

    D=I+W*A,             I+beta=W,             q=W*L.    (1)

The mathematical decoded Boolean words are Di=Fi-H for i=0,1, and
Ai=F(i+2)-H for i=0,1. These four differences are not individually
computed. They may be zero; every supplied field is strictly positive.

The exact projection is as follows. There are integers t>=m>=2 with
q=3^t, W=3^m and I=6x+2<W. The fields encode four length-t Boolean
streams d0,d1,a0,a1. Their scalar read and append streams have trits

    d_j=d0_j+d1_j,             a_j=a0_j+a1_j,

and describe a t-step FIFO run starting at I and ending at zero. One
step removes the units trit and appends the supplied trit at the top:

    N_(j+1)=floor(N_j/3)+(W/3)*a_j,   d_j=N_j modulo3.   (2)

The encoding of a trit1 can be either (1,0) or (0,1). Trit0 must be
(0,0), and trit2 must be (1,1). Any controller using the individual
Boolean labels must account for this nonuniqueness. No such controller
is implicit in (1).

## Soundness

The57 theorem gives q=3^t, H=(q-1)/2 and the stated Boolean fields.
It also gives F0's units trit2 and an even sum of the four fields.
The positive divisibility equation in (1) makes W and L powers of3,
with W<=q. Since W>I>=8, W>=9 and t>=m>=2. Each scalar sum has
ordinary ternary digits0,1,2, with no carries. Thus

    0<=A,D<=2H=q-1<q,            0<I<W.

The first equation (1) is the exact finite transport identity. Reducing
it modulo3 gives d_0=I modulo3. After removing this trit and dividing
by3, the corresponding identity for the remaining streams gives the
next read digit. Induction proves (2), with 0<=N_j<W at every step.
Indeed removal leaves a value below W/3, and appending a trit at most2
keeps the next value below W. The full transport identity gives N_t=0.
This is the same exact causality argument as the retained native FIFO
lemma; no controller word is assumed to derive it.

## Positive converse and the parity/origin conditions

Conversely take any run with the stated geometry and any Boolean splits
of all its read and append trits. Set Fi=H plus the corresponding Boolean
word. All fields and all four slacks q-Fi are positive. Telescoping (2)
gives D=I+WA. Since W is odd and I is even,

    F0+F1+F2+F3 = D+A+4H = 0 modulo2.                   (3)

The origin condition is automatic too: W is divisible by3 and
I=6x+2, so the first read trit is2. Its unique Boolean split is(1,1),
which makes F0's units trit2 as required. Therefore all hypotheses of
the exact57 typing theorem hold, including its necessary index parity.
Its full parametric positive Pell map supplies the retained kernel.
Choose beta=W-I>0 and L=q/W>0. All equations (1) follow.

In particular, for every x>=1, choose the least W=3^m>I and let t=m.
Read the initial queue once and append zero at every step. This gives
a positive arithmetic witness through the typing converse, for either
choice of split at each input trit1. Hence the bare component accepts
all ordinary inputs; it supplies initialization and transport only.

The fixed affine input map is invertible on its image. A prospective
universal controller must simulate a machine for the transformed inputs
6x+2, or prove an equivalent normalization. It must not silently identify
the native individual Boolean word D0 with the ordinary integer x.

## Literal count

Append these ten instructions to the57 source:

    read_fields=F0+F1; D=read_fields-2H;
    append_fields=F2+F3; A=append_fields-2H;
    six_x=6*x; I=six_x+2;
    scaled_append=W*A; transport=I+scaled_append;
    width_bound=I+beta; length_product=W*L.

Here 2H is the already computed register. The ten instructions cost
3M+7A. Compare D=transport, width_bound=W and q=length_product.
Together with57=30M+27A this gives67=33M+34A. The seventeen core
coordinates, four field slacks, H, beta and L give24 auxiliaries.
The parameter list is x,W,q,F0,F1,F2,F3.

## A precisely scoped 75-operation carry architecture

There is room for one restricted arithmetic carry controller in eight
more operations. Fix integer weights c0,c1,c2,c3 and an initial carry cs,
with the fixed compiler constraint

    c0+c1+c2+c3=0.

Four scalar products and four additions impose

    c0*F0+c1*F1+c2*F2+c3*F3+cs=0.                       (4)

The coefficient constraint cancels the four H offsets exactly. The
carry reconstruction theorem therefore identifies (4) with the entire
finite integer carry path

    3 carry_(j+1)=carry_j+c0*d0_j+c1*d1_j+c2*a0_j+c3*a1_j,
    carry_0=cs,             carry_t=0.

The carry values are deduced integers in a fixed finite interval, not
additional positive existential coordinates. Zero read and append give
the absorbing zero self-loop. The digit labels are Boolean, so this
architecture is outside the previous unfiltered full-trit width-decision
theorem. Its universality is **open**. No coefficients implementing an
arbitrary recursively enumerable set, input normalization theorem or
sound accepting simulation have been supplied. Thus75 is a literal
conditional architecture count, not a complete universal bound.

## Evidence

The [checker](native_dualrail_fifo67.py) independently expands all19
source equations and checks the67 ledger, retaining the exact auxiliary
norm correction. Its bounded scan compares arbitrary Boolean-stream
tuples against a direct step-by-step FIFO implementation, including zero
append streams and both labelings of a read trit1. It supplies positive
outer maps for the first200 ordinary inputs and audits the offset
cancellation used by (4). The full Pell extension is the parametric
typing theorem, not a numerical materialization.

The [receipt](native_dualrail_fifo67.json) is compared by default.
Independent full scoped proof/source/default review passes. A subsequent
focused extension review caught temporary-register name collisions in the
eight-operation schedule; distinct names and a combined75-register audit
now address them. No universal simulation is tested or claimed.

## 66 operations with the origin on the append stream

Keep the57 typing source, but interpret F0,F1 as append planes and
F2,F3 as read planes. Compute

    A=F0+F1-2H, D=F2+F3-2H, I=2x,
    D=I+WA, I+beta=W, q=WL.                              (5)

The initial value now needs one multiplication, saving the addition in
I=6x+2. Everything else in the ledger is unchanged: **66=33M+33A**,
19 equations and24 positive auxiliaries beyond the same seven parameters.
The exact semantic projection is a FIFO run from2x to zero with
q=3^t, W=3^m, t>=m>=1, 2x<W, and with the first Boolean append plane
equal to1 at the origin. In particular the first scalar append trit is
1 or2. The first read trit is unrestricted. If the first append trit
is1, its split must be(1,0); later trit1 splits remain arbitrary.

For soundness, I>=2 and the positive bound imply W>=3, and the same
transport proof applies. For the converse, every run and split with the
stated first-append condition satisfies the typing origin condition.
The packed parity remains automatic: D+A=2x+(W+1)A is even. All four
field slacks, beta and L are positive, so the exact57 positive extension
applies without any change to its kernel proof.

Every positive x again has a bare-component witness. Choose the least
W=3^m>2x. Read the initial m-trit queue while appending1 on the first
step and0 thereafter. At time m, the queue contains1; read that1 and
append0. Thus t=m+1, q=3W, and the final queue is zero. Split the first
append as(1,0), and split the read trits in either permitted way. This
proves coverage of every ordinary input, while still making no accepting
controller claim.

The checker audits the66 source independently and compares arbitrary
Boolean streams through t=3 with direct FIFO execution. It also constructs
these maps for x=1,...,200. The unchanged67 checks are retained.

### The74 carry architecture and a more general endpoint

The eight-operation extension now gives a literal **74=37M+37A**
architecture. Under the zero-sum coefficient condition its carry has
initial value cs and final value0, with append weights c0,c1 and read
weights c2,c3. Its universality remains open.

There is also a mathematically exact interpretation without zero-sum
coefficients. Let K=c0+c1+c2+c3 be even, choose fixed integer initial
carry cs, and set cf=-K/2. In (4) replace the free fixed numeral cs by
the free fixed numeral cs+K/2. No variable arithmetic is added. Indeed
the original global carry equality is

    sum_i ci*(Fi-H)+cs=q*cf.

Substituting q=2H+1 and cf=-K/2 makes this exactly

    sum_i ci*Fi+cs+K/2=0.                                (6)

Hence the same eight operations express the full carry graph with h=0,
initial carry cs and terminal carry cf=-K/2. The fixed sum and half are
computed when choosing the program numerals, independently of x. This
does not assert that all weights can be halved or that a variable half
is free. The stated fixed restriction is simply K even.

Unless K=0, the terminal carry is not absorbing under zero labels.
This architecture therefore cannot import a zero-extension argument
from the earlier queue model. A universal simulation would have to reach
the exact endpoint at its accepting time and satisfy the first-append
condition, while excluding all unintended accepting paths in the whole
carry graph. Neither version has such a compiler yet. Independent full
proof/source/default review of the66 refinement and endpoint extension
passes, with no findings.

## 65 operations by computing only the shared offset

The aggregate projections in (5) use only2H, never H by itself. Retain
the55 source and compute the single register Q=q-1, instead of supplying
H and computing q=H+H+1 in two additions. Then use

    A=F0+F1-Q, D=F2+F3-Q, I=2x,
    D=I+WA, I+beta=W, q=WL.                              (7)

The exact55 theorem already proves q=3^t, so Q=2H for the mathematical
repunit H=(q-1)/2. Thus every65 solution extends to66 by supplying that
positive H, and every66 solution restricts to65 by forgetting H. Their
positive parameter projections are identical. This is a source-equivalence
proof, not an assumption that an uncomputed H is an arithmetic register.

The total is **65=33M+32A**, with18 equations and23 positive auxiliaries
beyond x,W,q,F0,F1,F2,F3. With x the only free ordinary input, the full
component has29 positive existential coordinates. The checker expands
the65 polynomials independently, and the literal combined carry schedules
execute with disjoint register names. The arithmetic register named
`twice_H` in the source now computes q-1 directly.

The eight-operation carry specializations above consequently cost73.
More usefully, two further operations permit an unrestricted affine
carry offset and independently prescribed endpoints within75.

### A general Boolean-filtered affine carry controller within75

Fix integer weights c0,c1,c2,c3, offset h and endpoint carries cs,cf.
Here c0,c1 weight the append planes and c2,c3 the read planes. Put
K=sum(ci), and first assume h-K is even. Define the fixed program
numerals

    lambda=(h-K-2cf)/2,             delta=cs-cf.

Append the equation

    sum_i ci*Fi+lambda*Q+delta=0.                         (8)

Its literal schedule has four products ci*Fi and three additions to
sum them, one product lambda*Q, one addition of that product, and one
addition of delta. This costs10=5M+5A, so the complete arithmetic
architecture has **75=38M+37A**,19 equations and29 positive witnesses
when x is its only free input. All program numerals are fixed independently
of x. The products by fixed coefficients are fully charged even when a
particular choice happens to simplify them.

The mathematical equality behind (8) is exactly

    sum_i ci*(Fi-H)+hH+cs=q*cf.

Indeed Q=2H and q=2H+1 give (8) upon substitution. The exact carry
reconstruction theorem therefore proves that (8) certifies the entire
finite carry graph

    3 k_(j+1)=k_j+h+c0*a0_j+c1*a1_j+c2*d0_j+c3*d1_j,
    k_0=cs,                         k_t=cf.              (9)

All four labels are Boolean. The inferred carry remains in a fixed
finite integer interval, for example with absolute bound
max(abs(cs),ceil((abs(h)+sum(abs(ci)))/2)). No carry word or additional
state coordinate is assumed or supplied. Conversely any such path,
together with the specified FIFO run and its origin condition, satisfies
the source and inherits the complete positive65 Pell extension.

The fixed parity restriction is harmless for choosing a machine: if
needed, double every ci, h, cs and cf before forming lambda and delta.
Every original carry path doubles. Conversely a scaled path starts even,
and its recurrence has an even added term, so induction makes every
carry even; division by2 recovers the original path. Thus the scaling
preserves the entire labelled language, not only the intended paths.

In particular this75 architecture includes arbitrary weights with h=0,
cf=0 and the absorbing zero endpoint. Its Boolean labels distinguish
it from the earlier full-trit unfiltered width-decision theorem. The
remaining research question is now concrete: can this whole carry graph,
coupled to the scalar FIFO initialized by2x and the first-append condition,
represent every recursively enumerable set by fixed program numerals?
No compiler proving that claim has been supplied. The75 count remains
a conditional architecture, not an established universal certificate.

Independent full scoped proof/source/default review of this final65 and
general75 refinement passes, including the absence of H from the source,
the complete75 schedule and the entire-path scaling argument.
