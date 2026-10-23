# Independent review of the two signed-domain guard eliminations

This review was prepared independently of the signed16/signed15 circuit
generator. It checks the mathematical reductions and source dependencies.
It is an ordinary proof review, not a Lean/Rocq compilation certificate.

## 1. Residue-preserving Pell orbit

**Lemma.** Let t>=2, d=t^2-1, M>=1. Suppose a,H are integers, a>=1, and
a^2-dH^2=1. For every real bound L there are integers a',H' satisfying

    a'^2-dH'^2=1, H'>L, H'=H (mod M).

**Proof.** Put eta=t+sqrt(d)>1 and beta=a+H sqrt(d). Since
a^2-dH^2=1 and a>0, one has a>|H|sqrt(d), so beta>0 even when H<0.
The matrix A=[[t,d],[1,t]] has determinant 1. Its image in the finite
group SL_2(Z/MZ) has finite order k; M=1 causes no exception. Therefore

    (a_n,H_n)^T=A^(kn)(a,H)^T

is an integer Pell solution congruent to (a,H) modulo M. Its algebraic
unit is beta eta^(kn), and its conjugate is its positive reciprocal.
Consequently

    H_n=(beta eta^(kn)-beta^(-1)eta^(-kn))/(2 sqrt(d)) -> infinity.

Choosing n sufficiently large proves the lemma. No claim that eta is a
fundamental unit is used, and H=0 is permitted.

### Application to the Jones j coordinate

The relevant source definitions are

    B1=2R+1, C=B1+bw+phi, J=4A-5,
    D=(A^2-1)C^2+1, E=iJDC^2, F=(A^2-1)E^2+1,
    G1=A+F(CD+1-A), H=B1+jC,
    I=(G1^2-1)H^2+1, T0=QF+J(H-C).

Only H,I,T0 among the source conditions depend on j. The previously
guarded quantities imply R>=2, A>=4, C>0. Since i!=0, E!=0 and F>1.
Moreover CD+1-A>0, so G1>1.

The three positive numbers D,F,I are pairwise coprime. First E is divisible
by D and J, so F=1 modulo D and J. Next G1=1 modulo D, giving I=1 modulo
D. Finally JF divides T0, hence F divides H-C because gcd(J,F)=1.
Modulo F one has G1=A and H=C; therefore I=D modulo F. This proves
gcd(F,I)=1 as well. Since DFI is a square, each factor is a square.

Apply the lemma with t=G1 and M=CF to the square I. Choose H'>B1+C with
H'=H modulo CF. Then j'=(H'-B1)/C is an integer greater than 1, so its
shifted source coordinate j'_0 is nonnegative. I' is a square, while D
and F are unchanged squares. The divisibility condition is preserved,
because T0'-T0=J(H'-H) is divisible by JF. The other source square a0 and
the positive margin m do not involve j and remain unchanged.

Thus the j nonnegativity guard can be removed. The implication works for
any initial signed j. Completeness uses the original positive source
witness without needing a reverse orbit transformation.

## 2. A cofinal square family removes the radix guard

Let zstar=2^sstar be the fixed Jones index and L=5^33 for the nu=32 source.
Set

    bfloor=(2 zstar)^(L+1), b=bfloor*r^2,

and impose r!=0 through the merged nonzero factor. Every coefficient of
the digit polynomial e(T) is an integer in [0,2zstar-1], its degree is at
most L, and its digit exponents are distinct. Thus

    ystar=e(2zstar) <= (2zstar-1) sum_(a=0)^L (2zstar)^a
                       = (2zstar)^(L+1)-1 < bfloor.

Consequently r!=0 implies b>=bfloor>ystar, and
epsilon=b-ystar-1 is nonnegative. This proves soundness by substitution
into the signed16 source, without asserting that every r makes b a power
of two. The Jones source conditions themselves enforce the needed power
of two property at actual solutions.

### Completeness and exponent restrictions

The complete proof of `USys_of_mem` in `Master3.lean` was inspected, as
were `reduced_of_mem` in `NineReduce.lean`, `ratio_complete` in
`NineRatio.lean`, and `exists_B25core` in `Ratio.lean`.

In `USys_of_mem`, the choice

    exponent = x*ystar + sum(witness coordinates) + 1

is used only to establish exponent>=1, x*ystar<b, and each encoded
coordinate<b. After those initial bounds, every subsequent use is through
the power-of-two identity b=2^exponent and those inequalities. There is
no later exponent equality, parity requirement, or congruence requirement.
Replacing that choice by any sufficiently large exponent preserves the
construction of e,l,g, the transfer identities, the positive slack
coordinates, and the central-binomial divisibility predicate.

`reduced_of_mem` retains the chosen b and constructs epsilon=b-x*ystar-1;
it does not change b. `ratio_complete` takes the hypothesis
`exists k, b=2^k` for an arbitrary b satisfying its explicit bounds.
In `exists_B25core`, k is used to choose the further coordinate
w=2^(2R+1-k); positivity follows from b<=R. No prescribed residue of k
is required there either.

Now bfloor is itself a power of two, say 2^e0. The sequence

    r=2^t, b=bfloor*2^(2t)=2^(e0+2t)

has arbitrarily large exponents. Choose t so that e0+2t meets the original
lower bound, and carry out the same source construction. This establishes
completeness within the restricted square family. It is essential to
rebuild the source witnesses for the chosen larger radix; an arbitrary
old witness cannot simply have epsilon replaced by a square.

The five remaining square-stack guards are g0,s0,w0,phi and the positive
margin m. Counting eight signed base coordinates, five Pell witnesses,
and the two finalizer witnesses gives fifteen unrestricted integers.

## Review conclusion and limits

Both guard eliminations are valid by ordinary mathematics, with the
source's original coherent fixed coefficient tuple. This review supports
the signed15 construction's reduction theorem. It does not establish the
original compiler, the K215 endpoint, exact generated degree, or complete
end-to-end formal certification. Those are separate inherited or audited
dependencies. The reviewed source hashes and finite Pell diagnostics are
recorded by `review_signed_reductions.py` in `SIGNED_REVIEW_CHECKS.json`.
