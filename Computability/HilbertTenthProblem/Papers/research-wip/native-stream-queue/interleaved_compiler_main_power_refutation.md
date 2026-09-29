# The interleaving shortcut is false even with the actual main Pell power

The direct one-field interleaving shortcut remains unsound when its temporal
multiplier is **twice the actual main Pell power**. This new complete source
has **74=41M+33A**, 31 strictly positive coordinates and20 equations. For
every fixed admitted native compiler it has positive witnesses at every
positive ordinary input, including rejected inputs of the fixed empty-set
compiler.

This strengthens the
[independent-stride refutation](interleaved_compiler_collapse_refutation.md).
It resolves the additional fixed-point obligation at the actual packed index:
the Boolean word is chosen to satisfy both its transport residue and the
congruence that makes its freshly generated main Pell power the intended
stride. It does **not** refute either earlier open75 candidate or the
established complete76 theorem.

## 1. Exact source

Use the notation and all fixed numerals of the cited74 source:

    B=2^d, d a power of5, Q=B^2,
    m=MC+B*MF, K0=DC+Q*DR,
    q=n^2, D0=n^3,
    (Q-1)J=q-1,
    r=(q-V)(q-1)+m*J.

The fixed masks MC,MF are even and their populations sum to d. Thus m is
even and has exactly d set bits in a 2d-bit Q-cell. Retain the unchanged
43-operation **base-two** kernel, with X=w*D0 and main parameter A=a+2.
Retain the positive separated-field equations and the raw bound, but replace
its independent stride by2X:

    C=Z+W,
    V=Z+B*F,
    (K0+2X)*C=F+z*(q-1),
    C+alpha+4d*x=q.                                     (1)

Retain the four ordinary-input bridge equations at

    u=4d*x+b, Delta=(a+2)^2-1, H=4a+3,

exactly as in the cited source. In particular their intended endpoint is
still W=2^u=2^b*Q^(2x); the odd fixed inner width b and the ordinary input
semantics are unchanged.

Delete the instruction/comparison `P*v=q` and its two supplied coordinates.
Add the one multiplication `twiceX=2*X`, then use that register in the
existing sum `K0+twiceX`. All other instructions are retained. Hence

    51 mask/kernel operations +9 outer operations +14 input operations
      =74=41M+33A.

There are31 positive supplied coordinates and20 equations. The fresh source
checker expands every polynomial, including the unchanged auxiliary-norm
correction. Numerals, reusing X and comparisons are free; multiplying X by2
is explicitly charged.

## 2. Choose a fixed comparison stride and a fixed padding prime

Put P0=Q^h for a fixed h in{1,2}, and define

    K=K0+P0, L=1+B*K.

Because d is a power of5, B=2 and Q=-1 modulo5. Therefore

    L(h=2)-L(h=1)=B*(Q^2-Q)=4 modulo5.

Choose h so that5 does not divide L. This needs no change to the compiler
numerals. The chosen h, K and L depend only on that fixed compiler.
In particular L is odd, `gcd(L,d)=1`, K>Q and L>B+1.

Apply the elementary
[prime-padding Boolean CRT lemma](pell_kernel_prime_padding.md) with

    S=L*d.

It supplies a fixed odd prime ell coprime to `S*Q*(Q-1)`, a fixed k<ell
with `k | ell-1`, and e>=1 such that

    Q^k=1 modulo S,
    e=v_ell(Q^k-1).

For completeness, its prime existence proof uses only cyclotomic
factorization. Let t be the order of Q modulo S, let m0=lcm(2,t), and take
A0=m0*S*Q*(Q-1). Any prime ell dividing Phi_m0(A0) avoids A0 because
Phi_m0 has constant term1. Thus ell avoids m0,S,Q,Q-1. Since ell does not
divide m0, the factorization of the squarefree polynomial T^m0-1 modulo
ell shows that A0 has order m0 modulo ell. Consequently ell=1 modulo m0.
Taking `k=lcm(t,ord_ell(Q))` gives `k | ell-1` and k<ell. The positive
integer Phi_m0(A0) exceeds1, so a prime divisor exists. All choices are
fixed and effective before the varying input is considered. No primitive
prime divisor theorem or prime-distribution theorem is assumed.

For all sufficiently large padding exponents a0, put

    N=ell^a0, q=Q^N, n=B^N, J=(q-1)/(Q-1), M=m*J.

The lemma represents **every** residue modulo `S*N=L*d*N` as a Boolean
sum of allowed unit-cell weights Q^i with `1<i<N-1`. Its construction
leaves cells0 andN-1 unused. This uses only O(N/ell^e) available cells;
it does not mistakenly request L*d*N independent bits.

One way to see the efficient coverage is that the powers Q^(kj),
`0<=j<N/ell^e`, enumerate precisely

    {1+S*ell^e*t modulo S*N : t modulo N/ell^e}.

After a fixed shift of the cell indices and at most one distinguished
additional unit bit, a fixed-cardinality consecutive subset of these
additive residues attains any target. Its physical indices fit because
k<ell<=ell^e. The cited lemma proves the cardinality choice, all integrality,
reserved-cell separation and strict upper index bound.

## 3. Two compatible residues at the actual packed index

Fix any positive ordinary x, and put

    u=4d*x+b, W=2^u.

Choose a0 large enough for the preceding Boolean lemma, for u<q, and for
the same two strict bounds used in the independent-stride refutation:

    B*(q-1)>L*W,
    (L-B-1)*q+B+1-W>L*(4d*x).                            (2)

All are eventually true along N=ell^a0. Define D=dN. Then

    gcd(L,D)=1, gcd(q-1,D)=1.                            (3)

For the second claim, q=-1 modulo5 because N is odd, so q-1 is a unit at
the only prime factor of d. At ell, Fermat's theorem gives
`Q^(ell^a0)=Q modulo ell`, and ell does not divide Q-1. The first claim
uses the chosen5-adic unit L and ell coprime to S.

Require V to satisfy the two residues

    V=-W-B*(q-1) modulo L,
    V=q+(M+1-d*h)*(q-1)^(-1) modulo D.                   (4)

They have a unique simultaneous class modulo LD by (3). The second was
obtained by rearranging the **actual** affine packed formula:

    r(V)+1=(q-V)*(q-1)+M+1=d*h modulo dN.                (5)

There is no unrelated provisional packed index in (5).

Reserve the two allowed unit-cell bits

    Vfixed=1+Q^(N-1).

Apply the prime-padding lemma to the target class in (4) minus Vfixed,
and call its selected Boolean sum T. Put V=Vfixed+T. The reserved cells
are untouched, so

    V AND M=0, V odd, q/Q<=V<q.

Define

    C=(V+W+B*(q-1))/L,
    Z=C-W, F=(V+W-C)/B,
    alpha=q-C-4d*x.                                     (6)

The first residue in (4) makes C integral. The bounds (2) give C>W and
alpha>0. Since L=1 modulo B, F is integral. Since K>Q and V>=q/Q,

    L*(V+W-C)=B*[K*(V+W)-(q-1)]>0,

so F>0; also F<q/B. Thus all coordinates in (6) are strictly positive,
and they satisfy

    C=Z+W, V=Z+B*F, K*C=F+(q-1).                       (7)

These equations temporarily use the fixed comparison stride P0. The next
step transports (7) to the actual power in the source.

## 4. Fresh kernel witnesses and the actual temporal multiplier

Set r to its exact packed value. The mask and oddness give

    n^2=q<=r<q^2=n^4,
    r odd, popcount(r)=3dN=3log_2(n).

The established complete76 positive kernel converse, with its old scale
parameter replaced by n, supplies every kernel witness freshly at this r
and D0=n^3. In particular

    X=2^(2r+1).

Equation (5) now yields

    2X=4^(r+1)=4^(d*h)=P0 modulo q-1,

because q=4^(dN). This is the retained power at the final packed index.
Furthermore r>=q and N is sufficiently large, so r+1>d*h and 2X>P0.
Consequently

    lambda=(2X-P0)/(q-1)

is a positive integer. Replace the temporary transport quotient1 by

    z=1+lambda*C>0.                                     (8)

Then (7) gives exactly

    (K0+2X)*C=F+z*(q-1).

All other outer and kernel equations remain satisfied. Neither lambda nor
P0 is a supplied source coordinate: (8) is the construction of the one
positive existential quotient z. No free arithmetic primitive has been
added to the 74-operation schedule.

Finally use the unchanged bridge witnesses

    kappa=psi_(a+2)(u), mu=chi_(a+2)(u),
    delta=(kappa-u)/Delta, phi=c-kappa,
    rho=(mu-a*kappa-W)/H.

Their integrality and positivity follow exactly as in the independent-stride
proof: u is odd and at least3, u<q<2r+1, W<C<q, the two standard congruences
hold, and `mu-a*kappa>kappa>=2(a+2)>W`. Thus all31 coordinates and all20
equations of the new main-power source have positive witnesses at x.

Since the construction works for every x and every admitted fixed compiler,
the fixed empty-set compiler gives false inputs. Reusing the actual main
power therefore does not repair the missing separation of the interleaved
fields. This statement concerns the exact source in Section1, not arbitrary
one-field compilers or the original complete76 construction.

## 5. Evidence and scope

The [checker](interleaved_compiler_main_power_refutation.py) verifies all20
expanded source residuals and the74-operation schedule. It imports the
independently proved and checked prime-padding selector, and constructs
three exact outer tuples at raw inputs1,2,3, with their actual packed-index
congruences. These use the small illustrative constants B=2,Q=4,m=2,L=19,
ell=37,k=18,N=50,653; their q values have101,307 bits and their packed
indices202,612 bits. Every separated outer coordinate is positive, and the
packed population is exactly151,959.

The illustrative width d=1 is not the huge width of an actual native
compiler; its large n and exact packed population satisfy every hypothesis
of the established positive kernel converse. The theorem applies to actual
compiler constants parametrically. The final main Pell power, auxiliary
Pell coordinates and enormous quotient (8) are proved by construction and
are not numerically materialized. No proof-assistant formalization or new
complete upper bound is claimed. The earlier open75 candidates remain open.

The [receipt](interleaved_compiler_main_power_refutation.json) is compared
by default. Author and two independent complete proof/source reviews pass;
fresh default receipt replay matches.
