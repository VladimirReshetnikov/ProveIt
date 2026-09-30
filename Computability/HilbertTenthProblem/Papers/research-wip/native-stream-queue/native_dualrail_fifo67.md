# A native dual-rail FIFO with ordinary input in 67 operations

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
