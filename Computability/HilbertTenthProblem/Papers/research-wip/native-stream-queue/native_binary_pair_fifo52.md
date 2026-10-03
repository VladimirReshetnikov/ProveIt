# A native paired binary FIFO in 52 operations

The [43-operation power-of-two relation](pell_kernel_power_two43.md)
supplies inexpensive geometry for two synchronized binary queues. With
ordinary positive input x and a high marker in the second coordinate,
the exact FIFO component costs **52=29M+23A**, with18 equations and28
positive existential coordinates besides x. A general affine carry
controller fits a literal **61=34M+27A** architecture.

This is a component theorem. In particular, the full binary alphabet
makes an absorbing-endpoint affine controller decidable by the earlier
effective Presburger argument. A universal compiler needs additional
constraints or another controller. The complete universal bound remains76.

## 1. Exact source and interface

Use positive parameters x,K,W,q,D0,D1,A0,A1, where Di are read streams
and Ai append streams. The executable names are `read0`, `read1`,
`append0`, `append1`, avoiding collisions with retained kernel registers.
Take all seventeen positive witnesses of power43, and additional positive
L,beta,alpha0,alpha1. Add

    W=2K, x+beta=K, q=WL,
    D0=x+WA0, D1=K+WA1,
    D0+alpha0=q, D1+alpha1=q.                           (1)

The exact projection has q=2^t and W=2^m for integers t>=m+1,m>=2,
K=W/2 and 0<x<K. The ordinary binary digits of Di,Ai give a t-step
paired FIFO run of physical bit width m, with initial coordinates
(x,K) and final coordinates(0,0). Both append streams must be nonzero.
There is no prescribed first append bit or scalar-code interpretation.

The initial word consists of the ordinary low-first binary digits of x
in the first coordinate, padded with zeros, and one marker bit at the
highest position of the second coordinate. Since x<K, the first
coordinate is zero at that marked position. It is a four-symbol queue
whose symbols are pairs of bits. Interpreting these pairs as machine
symbols, normalizing the input, or recoding a larger alphabet still
requires a compiler proof.

## 2. Soundness and positive converse

Power43 gives q=2^t. The positive divisor equations give W=2^m,
K=2^(m-1) and t>=m. Since K>x>=1, K>=2, hence m>=2. The read
bounds give 0<Di<q. The positive transport equations give

    0<Ai<q, 0<x<K<W.

Every such integer automatically has a length-t binary expansion with
digits0 or1. This uses a proved power and paid integer bounds, without
an extra sparse encoding or digit conversion. Positivity of either Ai
and transport imply Di>W, so q>W and t>=m+1.

For each coordinate let d_j,a_j be the corresponding bits. Reduction
of D=I+WA modulo2, followed by successive divisions by2 in the proof,
gives the exact recursion

    d_j=N_j modulo2,
    N_(j+1)=floor(N_j/2)+(W/2)*a_j,
    N_0=I, N_t=0.                                     (2)

At each step 0<=N_j<W. Both coordinates have the same W, t and time
position, so they form one paired queue run. This proves soundness.

Conversely take any paired run satisfying the stated initial geometry,
terminal condition and nonzero append streams. Telescoping(2) gives
the two transports. Since I0=x and I1=K are positive, both read streams
are positive too. All streams are bounded by q=2^t. Set

    beta=K-x, L=q/W, alpha_i=q-Di.

These coordinates are positive integers. Power43 supplies its full
positive kernel witness independently of the streams. Thus every
equation(1) holds. No parity or origin condition on the four streams
is imposed by this geometry-only kernel.

Every positive x has a bare-component witness. Choose the least power
K of two exceeding x; put W=2K and q=2W. Append the pair(1,1) once,
then append(0,0) while reading the m initial positions. Both queue
coordinates are now1. Read this pair and append(0,0), giving t=m+1
and zero final contents. The stream values are

    A0=A1=1, D0=x+W, D1=K+W.

The two separate read bounds hold without a further padding step.
This construction proves coverage of all ordinary inputs, not acceptance
by any particular finite controller. A proposed universal compiler must
also guarantee nonzero append streams on its genuine accepting runs.

## 3. Complete ledger and the general carry extension

Beyond power43 the source computes W from2K, x+beta, WL, the two
products WAi, the two transport sums, and the two read bounds. These
are4 multiplications and5 additions. Thus the complete count is52,
with18 comparisons. There are21 positive auxiliaries beyond eight
parameters, including x; equivalently28 existential coordinates besides x.
Every supplied coordinate appears in the expanded source.

For fixed integer coefficients c0,c1,c2,c3,h,cs,cf, add the equality

    c0*D0+c1*D1+c2*A0+c3*A1+(h-cf)*q = h-cs.           (3)

Five products and four additions implement(3); the right side is one
free fixed numeral and the comparison is free. It adds9 operations and
one equation, giving61=34M+27A. No additional positive witnesses encode
the carry states. The complete labelled relation is exactly

    2k_(j+1)=k_j+h+c0*d0_j+c1*d1_j+c2*a0_j+c3*a1_j,
    k_0=cs, k_t=cf.                                    (4)

Telescoping gives(3), since the binary repunit is q-1. Conversely,
successively reducing the global identity modulo2 reconstructs every
integer carry and its final endpoint. All these carries lie in a fixed
finite interval: the absolute bound max(|cs|,|h|+sum|ci|) is invariant.
This equivalence includes every four-bit label and every reachable carry;
there is no implicit edge filter.

## 4. Why an unrestricted absorbing controller is insufficient

The all-zero label fixes the terminal carry exactly when cf=h. In this
case(3) loses its q term. Substitute both transport identities and W=2K:

    (2K*c0+c2)A0+(2K*c1+c3)A1+c0*x+c1*K+cs-h=0.         (5)

For fixed program data and ordinary x, positive A0,A1 and a power K of
two with K>x satisfy(5) exactly when the absorbing architecture has a
positive arithmetic witness. Necessity is substitution. For sufficiency
choose any sufficiently large q=2^t so q is divisible by W=2K and both
positive read values are below q. Binary typing is automatic; the
transport theorem and global carry reconstruction supply the entire run.
Power43 supplies all remaining positive kernel coordinates.

Formula(5), with the positivity and K>x inequalities, is a one-parameter
Presburger formula whose coefficients are integer polynomials in K.
The constructive elimination and power-orbit argument in
[the effectivity audit](input_bridge_presburger_effectivity.md) therefore
decides its existential power-of-two parameter. Having two append
variables does not change that theorem. The dependence on numerical x
is effective. This rules out an unrestricted absorbing affine controller
as a universal replacement in this particular paired binary architecture.

This conclusion does not cover cf!=h, an added code filter, nonlinear
constraints, or a different computation interface. The smaller component
count creates room to investigate such constraints; it does not supply
them automatically.

## 5. Evidence

The [checker](native_binary_pair_fifo52.py) independently expands every
source equation and the inherited auxiliary norm correction, audits the
52 and61 schedules, compares arbitrary bounded positive stream tuples
with direct paired FIFO execution, and constructs positive outer maps
for the first200 inputs. It separately checks the global/local carry
equivalence on two-step Boolean words.

Default execution compares the [receipt](native_binary_pair_fifo52.json).
The large kernel extension is supplied by the exact power43 theorem;
these stream checks do not materialize it or test a universal compiler.
Independent full proof, source, and default-replay review passed. No Lean formalization
or smaller complete universal bound is claimed.
