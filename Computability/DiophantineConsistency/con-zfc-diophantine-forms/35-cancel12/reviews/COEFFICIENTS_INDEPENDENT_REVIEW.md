# Independent review of the mixed121/general-padding coefficient tuple

## Conclusion and scope

I found no new defect in the proposed combination of package 25's mixed-radix
clause compiler with package 24's general odd-modulus Boolean padding
controller. The new numerical choices

```
b=121, L=8801, d=bL=1064921,
lambda=2341, step=lambda-1=2340
```

satisfy the finite hypotheses of both source arguments. The geometry,
coefficient bytes, carry threshold, population balance, modular orders,
valuation, and unit conditions were recomputed by
`audit_coefficients_independent.py` without importing or executing the new
generator. Its receipt is `COEFFICIENTS_INDEPENDENT_AUDIT.json`.

This review validates a composition of ordinary mathematical proofs.
It does not provide a new Lean/Rocq certificate of the native compiler,
the Pell lemmas, or the K215 foundational calibration.

The reviewed source materials are package 25's
`coefficients/PROOF.md`, package 24's `sections/coefficients.tex`, the
frozen package-25 tile list, and the proposed generator and binding, all
relative to repository pin `8c6eec9d19ef80538c8e61ff6e0180040583446a`.

## Clause logic and support geometry

The clause weights remain `w_j=2^(10+2j)`. The low ten-bit field contains
the number of selected tiles, which lies between zero and 943. Mask 1022
permits exactly counts zero and one. Only after this fact is proved do
the copy and anchor fields contain values from `{0,1,2}`. Masking the
low bit of each radix-four field then enforces equality of each copy
bit to the selected tile bit, and equality of each anchor to the
selection count. The smaller outer radix does not change this reasoning.

The native support still has 989 elements. Its largest exponent is 3296,
less than half the new circumference 8801. The gap 1102 between the clause
targets is absent from the cyclic support difference set. The two anchor
target preimage sets intersect only at zero. All copy, spatial, anchor,
and reflected-clause basis identities were checked separately. Thus the
finite synchronization hypotheses of the inherited proof hold at the
new cell length. The new bit width remains odd, as in the sources.

The added population mask uses seven 119-bit fields and one 27-bit field,
at exponents 8792 through 8799, contributing `7*119+27=860` bits. Every
native convolution term lies at an exponent at most 8791. Spatial and
temporal words have still smaller supports. The new fields therefore
test identically zero digits for every aligned canonical witness,
including every allowable dummy-bit choice. They cannot obstruct
completeness. For soundness, the added tests are additional restrictions
and may simply be discarded before applying the original clause tests.

The independently computed exact carry data are

```
mass = 197499621873484079107937843923661852,
threshold = 1329227995784915872903807060280344578,
rho = 2^121 = 2658455991569831745807614120560689152.
```

The threshold is the maximum of `4*mass+8`, `2*mu+4`, twice the largest
padding field plus four, and 16. It is strictly smaller than rho. Hence
the inherited carry/slack bound remains valid. The padding mask itself
is not a new arithmetic summand and creates no convolution carries.

The native populations are exactly `d-989` and 989, and the low residues
remain `MC=2 mod4`, `MF_native=4 mod8`. All four materialized ports agree
with an independently implemented literal finite recipe, and each gzip
decodes to the corresponding raw integer. The complete raw payload is
533099 bytes. The shifted port is `MF_source=MF_native+B-1` throughout.

## General Boolean controller: proof transfer

The factorization `d=11^2*13*677` and primality of lambda are exact.
Direct cycle enumeration, separate from the generator's order-factoring
routine, gives orders 10, 12, 52 and 60 for B modulo 121, 13, 677 and
2341. Thus the order modulo d is 780, dividing 2340, and the order modulo
lambda also divides 2340. Moreover

```
B^2340 mod lambda^2 = 2556373 = 1 + 1092*lambda,
```

where `lambda` does not divide 1092. The required valuation is exactly one.

Choose independently padded tableau dimensions `w_c,h_c`, both sufficiently
large powers of lambda. Put `N=w_c*h_c=lambda^n`, require `h_c>lambda` and
`N>d*lambda^2`, and write `T=N/lambda`, `C0=d*lambda`.
All relevant orders divide `lambda-1`, so
`q=B^N` and `B^w_c` are congruent to B modulo `d*lambda`.
The new unit table verifies that both `B^2-1` and
`1+B*DC+B^2*(DR+1)` are nonzero modulo each prime dividing `d*lambda`.
Consequently the exact lower-dummy coefficient

```
Gamma = rho^1063*(q^2-1)*[1+q*(DC+B*DR+B^w_c)]
```

is invertible modulo `d*N`.

The orbit of `B^2340` modulo `lambda^n` has length T by the binomial
lifting identity. Modulo d the same element is one. By the Chinese
remainder theorem its first T powers are exactly the residues

```
1 + C0*z,  0<=z<T,  modulo C0*T=d*N.
```

To realize an arbitrary residue by a Boolean subset of
`B^(2+2340*j)` for `0<=j<T`, together with the extra entry `B^3`, first
multiply the target by `B^(-2)`. Choose epsilon equal to zero or one so
that subtracting `epsilon*B` gives a nonzero residue modulo lambda.
This is always possible because B is a unit modulo lambda. Its least
residue a modulo C0 satisfies `1<=a<C0<T` and `gcd(a,T)=1`.
If the remaining target is `a+C0*u`, choose z0 satisfying

```
a*z0 + a*(a-1)/2 = u mod T.
```

The a distinct orbit entries with additive coordinates
`z0,z0+1,...,z0+a-1 mod T` sum to that target. Add `B^3` precisely when
epsilon is one. The positions are distinct, because no exponent
`2+2340*j` equals three. Their largest possible cell index is

```
N-N/lambda-lambda+3.
```

Since `w_c=N/h_c<N/lambda`, the necessary positive translations by one
and by `w_c` remain below N; even their sum has a strict margin.
This is the same nonwrapping orientation used in the source lemma.

Changing the chosen lower dummy bits changes the actual packed rank by
`-Gamma` times the corresponding Boolean sum. Apply coverage to
`(R0-d*w_c)*Gamma^(-1)` modulo `d*N`. The resulting actual rank obeys
`R=d*w_c mod d*N`, which is the required temporal rotation congruence.
No halting run or accepting tableau was searched for in the finite audit.
The theorem is a conditional construction from any given finite halting
run, exactly as the inherited completeness argument requires.

## Transfer to positive and signed arithmetic interfaces

Every positive arithmetic skeleton needs the same valid native compiler
tuple, canonical slack, and calibrated K215 language. These have just
the same hypotheses after the replacement. The four ports must be
replaced together; substituting a native high mask for the shifted port
would invalidate this reasoning.

For the stronger signed interfaces, the source additionally chooses
canonical witnesses with a square X-scale, an odd Y-scale, and an odd
strong-rank multiplier. These conditions also survive:

1. All of `b,L,d,w_c,h_c,N` are odd. Therefore `u=d*N=log_2(q)` is odd.
   The unchanged low-mask congruences give `R=3 mod4`, so `R-u` is even.
   The inherited bound `R>3*q` makes `w=2^(R-u)` a positive square.
2. The canonical Pell parameter `A=a+2` is even, while R is odd.
   Consequently `c=psi_A(R)` is odd. Choose the strong rank `m=c*R`.
   Expanding the c-th power of `chi_A(R)+c*sqrt(A^2-1)` proves
   `c^2` divides `psi_A(c*R)` and that the quotient i is odd. For the
   divisibility, the linear radical term has coefficient `c*c`, and
   higher radical terms contain at least `c^3`. For parity, all terms
   with a positive power of the even number `chi_A(R)` vanish modulo
   two after division by odd `c^2`; the final term is odd. The case
   `c=1` gives i=1 directly.
3. Exact population balance, including the original two-bit surplus,
   still yields `popcount(R)=3*u+2`. The inherited half-binomial identity
   gives `v_2(Y)=popcount(R)-2=3*u`, so `s=Y/q^3` is odd.

These are proof obligations beyond merely checking modular residues.
They are the same canonical-witness arguments used by package 24, and
the new tuple satisfies every parity assumption they use.

## Remaining dependency boundary

The synchronization, native arithmetic, marked Wang tiling semantics,
Pell rank and population identities, independent rectangular padding,
and K215-to-finite-refutation theorem are inherited mathematical
dependencies. The local finite checks certify their new finite inputs;
they are not a replacement for those universal theorems. No global
minimum of coefficient height or construction complexity has been proved.
