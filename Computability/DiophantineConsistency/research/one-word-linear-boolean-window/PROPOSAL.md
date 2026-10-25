# One-word Boolean transport: exact carries and a carry-free obstruction

There is a precise obstruction to packing a Boolean tableau into a
carry-free FULL fixed-target scalar convolution. The primary repository
already proves the needed spectral theorem; its plus-form specialization
below excludes the proposed cofinal unique-Start layout for every nonzero
nonnegative fixed multiplier. Boolean linear slack equations do not avoid
that theorem merely by adding finite lanes.

Deliberate carries remain an escape. Section2 proves the exact integer
congruence equivalent to a UNIQUE cyclic carry stream in a fixed finite
alphabet, including collisions of offsets modulo the word length. Section4
identifies the local Boolean content and the missing global construction.
No compiler, source generator, program or Lean command is run or supplied;
no nine-positive equation or numerical improvement is claimed.

## 1. Exact fixed-gap problem and ordinary digit notation

Fix B>=3,K0>=1 and1<=E<=B-2. The constants may come from a newly designed
compiler; no compact44 mask or K215 encoding is required. For N>=1,h>=0 put

    q=B^N, M=q-1, J=1+B+...+B^(N-1), a=B-1-E.

Thus0<a<B-1. An intended word C,0<=C<B^N, has ordinary base-B digits
c0,...,c_(N-1) in{0,...,B-1}. With alpha=EJ+1 and F=M-EJ-C, transport is

    (K0+B^h+1)C = -EJ modulo M
                  = aJ modulo M.                         (T)

This is only transport. F>0 and all mask, marker, computation and rank
conditions remain additional requirements. The earlier local mask lemma
for the compact44/indexed tuple proves none of those joint requirements.

Write the FIXED ordinary base-B expansion K0=sum_(r=0..m) kr B^r, with
0<=kr<B, and let S=2+sum_r kr. For every cyclic cell index j define

    dj=sum_r kr*c_(j-r)+c_(j-h)+cj,                     (D)

where EVERY subscript is reduced modulo N. If two or more offsets collide,
their coefficients ADD: no independence or distinctness is assumed. The
coefficient mass remains S, so0<=dj<=S(B-1), even when N=1 or m>=N.

## 2. Exact cyclic-carry equivalence, uniqueness and sharp interval bound

THEOREM. For every digit word above, (T) holds if and only if there is an
integer cyclic stream t0,...,t_(N-1), tN=t0, satisfying

    dj+tj = a+B*t_(j+1)       for every j.               (C)

This stream is UNIQUE, and necessarily0<=tj<=S-1 for every j.

Proof. Put vj=dj-a and V=sum_j vj B^j. Folding each actual product monomial
exponent modulo N uses B^N=1 modulo M, so

    V = (K0+B^h+1)C-aJ modulo M.

This folding is valid with arbitrary offset collisions; it is not digitwise
carry elimination. If (C) holds, telescoping the COMPLETE weighted sum gives

    V=sum_j (B*t_(j+1)-tj)B^j=(B^N-1)t0.

Hence (T). Conversely, if V=M z, set tN=z. For j=N-1,...,0 recursively
define tj=B*t_(j+1)-vj, using integer multiplication/subtraction only.
Then t0=B^N z-V=z=tN, giving the exact cyclic solution. No divisibility
of individual intermediate digit expressions has been presumed.

The difference of two solutions satisfies uj=B*u_(j+1); cyclicity gives
(B^N-1)u0=0 and hence every uj=0. Thus the carries are determined by C,
not independent slack or controller witnesses.

For the bounds, choose a minimum carry u=t_(j+1). Equation(C) gives
B u=dj+tj-a>=u-a, hence (B-1)u>=-a>-(B-1). Integrality gives u>=0.
At a maximum v=t_(j+1), B v<=S(B-1)+v-a, so
(B-1)v<=S(B-1)-a<S(B-1), and v<=S-1. This also covers N=1.

The exact model is consequently a fixed finite-alphabet carry system with
one long displacement h. It is not a proof that that particular family of
systems can simulate any machine. Canonical carries can have S values; they
are not automatically Boolean, and constructing them locally must preserve
their unique cyclic global closure.

## 3. Spectral obstruction to a carry-free full-target strategy

The primary HTP note native_controller_single_field_spectrum.md proves the
following mechanism for every fixed integer scalar convolution kernel.
Here is the complete adaptation to the ACTUAL plus sign in (T).

Let U be any real cyclic vector of length T, let R be cyclic shift, let
k(Z) be a fixed nonzero polynomial with nonnegative integer coefficients,
and let lambda be a fixed l-periodic forcing vector, where l divides T.
Suppose for any displacement H that the entire coefficientwise equation is

    [k(R)+R^H+I]U=lambda.                              (L)

Set A(Z)=-(1+k(Z)) and

    G(Z)=A(Z)A(Z^-1)-1.

It is NONZERO: G(1)=(1+k(1))^2-1>0. On a T-th root-of-unity Fourier mode
zeta with zeta^l!=1, the forcing vanishes. Any nonzero U mode there must
therefore satisfy zeta^H=A(zeta), and taking absolute squares gives
G(zeta)=0. This necessary condition is independent of H and T.

Clear negative exponents to obtain a nonzero polynomial g of degree D.
For D=0 take P=l. Otherwise a root of unity of order n in g has
phi(n)<=D. The elementary inequality phi(n)^2>=n/2 follows from
phi(n)^2/n=product_(p^e||n) p^(e-2)(p-1)^2: all odd-prime factors are
at least1, and the sole possible factor below1 is p=2,e=1, equal1/2.
Thus n<=2D^2, and one valid fixed bound is

    P=lcm(l,1,2,...,2D^2).

Every surviving Fourier mode has order dividing both P and T. Cyclic shift
is diagonalizable, so repeated roots cause no generalized-mode exception.
Consequently U has period dividing gcd(P,T), uniformly in word length and
displacement. The usual exceptional wire kernels from the general theorem
do not occur for this nonzero nonnegative plus-form k.

This conclusion concerns the ACTUAL claimed coefficientwise presentation.
A deliberately signed polynomial k can instead have G identically zero
only if 1+k(Z)=epsilon*Z^r, epsilon=+/-1. Indeed two distinct extreme
exponents of A give a nonzero extreme coefficient in A(Z)A(Z^-1); a single
term must have coefficient+/-1. The resulting equation has one shifted
wire and one signed shifted wire, with fixed affine forcing, rather than
a multi-input gate. This is a structural statement, not a general theorem
about every endpoint extension of a wire family. For example the positive
integer K0=B^r-1 also has a signed representation Z^r-1. Carry-free equality
in that presentation must not be identified with carry-free equality in its
ordinary nonnegative digit presentation. Neither follows merely from(T).

Apply this first at the ordinary base-B cell level with k(Z)=sum kr Z^r,
l=1 and H=h. If someone removes the carries from(C) and proves dj=a
coefficientwise, ALL cell digits have period bounded by the fixed P.
The conclusion holds for any finite cell alphabet or fixed periodic mask.
In binary micro-position coding one can instead take T=dN,l=d,H=dh;
the same proof gives a bounded number of cells. Within-cell cyclic wrap
does not evade the theorem.

An encoding with exactly one Start cell requires the full cell period N.
It therefore cannot supply a required cofinal family of uniquely marked
tableaux under these carry-free hypotheses. This is an obstruction to that
specific completeness design, not to arbitrary one-word encodings, varying
right-hand sides, nonlinear tests or carry-dependent constructions.

PERIODIC-CARRY REFINEMENT. If the actual carry stream is forced to have a
fixed period l, the right side of the coefficientwise equation

    [k(R)+R^h+I]c=a+(B R^(-1)-I)t

is l-periodic, with R acting by (R t)j=t_(j-1) as in(D).
The same Fourier proof still applies. If carry periods are only bounded by
a fixed L0, one uniform bound can include lcm(1,...,L0). Thus carry periods
must not be bounded by a fixed constant in a cofinal design. Every finite
cyclic word still has period N; literal nonperiodicity is not required.
Allowing internal Boolean additions but
resetting every whole-cell boundary to zero simply reinstates the macro-cell
carry-free theorem; finite extra within-cell lanes do not avoid it.

## 4. Local Boolean gates are real, but do not supply the global compiler

For Boolean x,y,z,u, the INTEGER equality

    x+y-2z-u=0

is equivalent to z=x AND y and u=x XOR y. The four input pairs prove this
directly: sums0,1,1,2 uniquely determine the Boolean quotient z and
remainder u. This is a legitimate local Boolean linearization.

A binary carry column with fixed output bit1 has

    x+y+p=1+2z.

If its incoming carry p and outgoing carry z are Boolean, this gives
z=x AND y and p=1-(x XOR y). With fixed output bit0 it instead gives
z=x OR y and p=x XOR y. These are exact ordinary local gate relations.
They exhibit how deliberate carries can be nonlinear in the visible bits.

Two cautions prevent treating that observation as a compiler. First, the
canonical global carry alphabet is not automatically{0,1}. For example
x=y=0,p=3,z=1 satisfies the fixed-output-one column but has z!=x AND y.
This is a counterexample to an UNTYPED local gate claim only, not a claimed
full source or computation counterexample. Second, p is the previous
column's unique outgoing carry; independent gate-by-gate choices of p do
not constitute a cyclic stream. Copies, carry typing, wire routing, all
unselected convolution columns and the closing boundary need proofs.

Jones's primary1982 coding argument illustrates the distinction. Its section3
packs a bounded tuple into c, uses the NONLINEAR product c^delta*D0 and tests
a selected central coefficient with explicit masks and coefficient bounds.
The movable base B=beta*b^delta depends on an unbounded size ceiling.
That construction is not a fixed-coefficient scalar full-target linear
convolution theorem. The repository's ShortPackedMaster also retains the
power equation explicitly and justifies mask typing before combining tests.
Neither provides a free fixed-radix Boolean carry compiler here.

## 5. Fixed coefficients, padding and controller still to prove

A successful positive result must specify ONE finite multiplier/mask recipe
and a digit/carry alphabet independent of tableau dimensions. It must prove:

1. every accepted digit word and its UNIQUE bounded carry stream decode to
   the intended accepting computation, including all unmatched output bands;
2. every accepting computation admits those words and carries on a cofinal
   padding schedule, with positive C,F,alpha and correct markers/alignment;
3. the fixed native masks really type every required word/carry constraint,
   without splicing coefficient tuples or leaving an extra free carry word;
4. coordinated accepted word changes satisfy transport AND yield the needed
   actual packed-rank residues at those SAME licensed dimensions;
5. the arithmetic/Pell converse is rebuilt with those native hypotheses.

At fixed N,h, every accepted change still satisfies
(K0+B^h+1)deltaC=0 modulo M, hence deltaC is a multiple of M/g for
g=gcd(K0+B^h+1,M). The carries change uniquely with it. Independent dummy
flips or arbitrary slack-bit choices cannot be reinstated as a controller.
If the desired controller must cover all dN rank classes, g>=dN is necessary.
The earlier large-kernel arithmetic dimensions do not by themselves ensure
that bound, masked computation words, rank units or the padding schedule.

For the retained rank formula, a kernel step M/g has rank increment
M^2(q^2-1)/g. Its being a unit modulo dN is sufficient only together with
an appropriate family of accepted no-wrap kernel parameters. No such family
or complete accepting-word construction is produced here.

The useful result is narrower and concrete: carry-free full-target Boolean
packing is excluded under explicit cofinal-marker hypotheses, and any
remaining deliberate-carry route has the exact unique finite-state system
(C), rather than an unspecified linear-congruence heuristic, to construct.
There is no nine-positive equation, source compiler or count claim.
