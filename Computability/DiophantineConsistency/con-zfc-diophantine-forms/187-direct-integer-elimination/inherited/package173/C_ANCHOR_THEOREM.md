# Reusing the encoded row index as the Pell anchor

Ordinary arithmetic proof, independently derived for the current research
iteration. This note changes the semantic anchor and removes the derived-label
range test. It does not claim a new proof-assistant formalization.

## 1. Exact anchor substitution

Let `c0` denote the ACTUAL encoded row-index representative (called `C` in
the arithmetic front), not a translated storage coordinate. Retain its existing
principal Pell pair `(U,V)` and multiplication wire `Z=A*V`. In every private
anchor row replace the old nominal derived-label index `h` by `c0`, and replace
the old anchor pair by `(U,V)`. Use the same auxiliary/comparison rows

```
U^2-(A^2-1)V^2=1,
H^2-(A^2-1)J^2=1,
S^2-(D^2-1)R^2=1,
J=V^2(2e+1),
D=1+4J(2d+1),
D=A+Hf,    S=U+Hg,    R=c0+4Vr.
```

The principal norm and `A*V` wire already belong to the requested power
`(q+1)^c0`; they must not be duplicated. Retain the squared bound

```
V^2 = c0^2 + 1 + sum_(i != anchor) Y_i^2
      + a^2+b^2+c(c+1).
```

Retain the pooled orientation row, INCLUDING the reused anchor:

```
sum_i ((X_i-1)^2+(Y_i-k_i)^2) = (A-1)Q.
```

All private witnesses remain unrestricted integers. The actual nominal
index `c0` is initially signed. Its nonnegativity is NOT a hypothesis.
The frame must include `c0` and every retained/new actual base, index and
output. In particular it must include the new first-power index `D0*t`
when `F=t^(D0*t)` replaces `F=t^t`. Here `D0` is a fixed positive integer;
it is distinct from the private comparison center `D` above.

## 2. Noncircular soundness of the new anchor

The odd Pell frame gives `W>=258`, `|A|>W^W`, and `|A-1|>4W^3` before
any semantic sign recovery. All requested index squares are less than W.
The nonnegative ternary expression gives `|V|>|c0|` and `V!=0`. Since
`2e+1!=0`, J is nonzero and `V^2` divides J. The comparison center is
nondegenerate because `D=1+4J(2d+1)` has absolute value at least three.

Put `a0=|A|`. Pell classification gives positive i,l with

```
|U|=X_i(a0), |V|=Y_i(a0),
|H|=X_l(a0), |J|=Y_l(a0).
```

The inherited squared-divisibility lemma gives `i<=l` and `|V| | l`.
For clarity, its index-divisibility mechanism is: strong divisibility of
Pell ordinates gives `i|l`; writing `l=i*s`, composition gives
`Y_l(a0)=Y_i(a0)*Y_s(X_i(a0))`. Since
`X_i(a0)^2-1=(a0^2-1)Y_i(a0)^2`, the Pell polynomial expansion gives

```
Y_s(X_i(a0)) = s*X_i(a0)^(s-1) modulo Y_i(a0).
```

The abscissa is coprime to the ordinate, so divisibility by the second
copy of `Y_i(a0)` forces `Y_i(a0)|s`, and hence `|V||l`.

Classify the comparison pair at the signed center D. Polynomial transfer
through `D=A mod H` and `S=U mod H`, with its independent abscissa sign,
gives comparison index `j=+/-i mod 2l` by the same inherited Pell
abscissa comparison theorem used for the previous semantic anchor.
The identity `D=1 mod 4V` and `R=c0 mod 4V` give
`j=+/-c0 mod 4|V|`. Since `|V||l`, the two statements imply

```
i = +/-c0 modulo 2|V|.
```

But `1<=i<=|V|` and `|c0|<|V|`. If c0=0 there is no such i.
Otherwise the only possibility is `i=|c0|`. Thus

```
c0 != 0,  |V|=Y_|c0|(|A|).
```

The squared bound now gives each other classified principal index
`j_i<|c0|<W`, while the anchor index equals `|c0|<W`. The proof uses
no previous fact about the sign or arithmetic meaning of c0.

The unchanged orientation proof reduces the full pooled row modulo A-1.
Its small residue error is a sum of at most m squared abscissa/ordinate
errors, bounded by `4mW^2+4m<4W^3<|A-1|` for m<=15 and W>=258.
Therefore every error is zero. This identifies every retained principal
pair as the canonical signed-index pair `(X_ki(A),Y_ki(A))`, including
`(U,V)=(X_c0(A),Y_c0(A))`. It also applies to a new pair at index D0*t.
For negative A, the parity signs are handled by the same polynomial
identities; it would be incorrect to require all abscissae positive.

Consequently the singleton and pooled power lemmas are available in the
same noncircular order as before. After the radix is recovered with
`|q+1|>=2`, its request at exponent c0 forces `c0>=0`. Combining this
with c0!=0 gives c0>0. A positive-index premise has not been smuggled
into the anchor proof.

## 3. Cofinal CRT choice: no front-size bound is needed

Start with a finite proof and the factorial-free arithmetic completeness
construction. Fix the cofinal horizon `t=16+4z^2`, and put

```
F=t^(D0*t),  B=binom(F+t,t),  N=B^x,
y=F*(2v+1),  Hrad=2+4(c0+A1+...+A8).
```

Take D0>=1. The positive beta spacing and sufficiently large beta code x
are constructed BEFORE the independent CRT representatives. All front
indices `t,D0*t,F+t,y+1,x` are therefore fixed at that point.

As in the linear-CRT source, B is odd. Indeed t is divisible by four and

```
v_2(F)=D0*t*v_2(t) >= 2t > floor(log_2(t)).
```

For every 1<=i<=t this makes `v_2(F+i)=v_2(i)`, and subtraction of the
factorial valuation in the binomial coefficient gives `v_2(B)=0`.
Hence `N^2` is odd.

The generalized binomial-CRT compiler assigns each column, including c0,
a residue class modulo N^2. For each full prime power `p^e||B`, an assigned
row i satisfies `p^e | F+i`, and the c0 column is assigned the row index
`i-1` to precision `p^(2ex)`. Therefore its residue class satisfies
`B | c0+F+1`. Any further addition of a multiple of N^2 preserves this
divisibility, all higher CRT congruences, every range-binomial divisibility,
and every polynomial local-congruence identity.

Choose the eight other actual representatives A1,...,A8 positive in their
classes first. Now let M be the maximum of those eight values and every
other requested nominal index (including t,D0*t,F+t,y+1,x). Starting with
any representative c* of the remaining encoded-index class, choose an
integer k with

```
c0=c*+k*N^2 > max(M,2),  c0 even.
```

This is always possible: N^2 is odd, so the required parity selects one
class of k modulo two, and that class is unbounded above. Equivalently,
the permitted positive even c0 values form a cofinal progression of step
`2N^2`. No assertion that all fixed front indices lie below N^2 is needed.
This is stronger and simpler than the old fixed-window choice.

After choosing c0, define Hrad and q=(B*Hrad)^x. They were deliberately
left unfixed until after the CRT representatives. The self-sized radix
now dominates every ordinary representative, including the enlarged c0.
The actual frame W is computed after these powers are fixed. Neither N
nor any previously fixed CRT modulus depends on c0, Hrad or q, so there
is no circular choice. The existing range estimates use lower bounds
for Hrad, not an upper bound on c0/N^2.

## 4. Completing every private cap witness

Choose the positive canonical frame center A and all principal pairs.
Because c0 is even and greater than all other requested indices,

```
V=Y_c0(A) is even,   U=X_c0(A) is odd.
```

Let K=max_(i != anchor) k_i<c0. Recurrence gives
`V>(2A-1)Y_(c0-1)(A)`, while the sum of the at most 14 other squared
ordinates is at most `14*Y_(c0-1)(A)^2`. As A>W^W and c0<W, their
squared difference exceeds c0^2+1. The resulting nonnegative integer
slack has a representation `a^2+b^2+c(c+1)`, so the squared bound is
satisfied.

Set l=c0*V, H=X_l(A), J=Y_l(A). Composition gives
`J=V*Y_V(U)`. Since `U^2-1=(A^2-1)V^2`, the polynomial expansion gives
`Y_V(U)/V=U^(V-1) mod V`; more explicitly
`Y_V(U)=V*U^(V-1)+V^2*T` for an integer T. Therefore J/V^2 is an
integer congruent to the odd U^(V-1) modulo the even V. It is odd.
Set `e=(J/V^2-1)/2`.

The index l is even, hence H is odd. Its Pell norm gives gcd(H,J)=1,
so gcd(H,8J)=1. Ordinary CRT chooses D>=2 with

```
D=A modulo H,  D=1+4J modulo 8J.
```

Let S=X_c0(D), R=Y_c0(D). Base transfer and base-one reduction give
`S=U mod H` and `R=c0 mod 4V`, so all displayed quotient witnesses
are integral. All orientation errors are divisible by A-1, giving the
orientation quotient. This supplies the complete private anchor with
exactly the same number of rows and coordinates as before.

## 5. Removing the derived-label range: the extra theorem required

Anchor replacement alone does not justify deleting the h range test. That
test supplied local label bounds needed for multiplicity recovery. A sound
replacement is a fixed label majorant: assume every local formula label
is between 0 and t^d on local parameter tuples in [0,t-1]^4, for a fixed
integer d. It is enough to choose D0>d+1 and F=t^(D0*t).

The following argument proves the needed replacement uniformly. Omit zero
labels, whose weights are one. Suppose the conclusion side has at most t
nonunit factors; the premise side may initially have at most 2t+1. Let
L=t^d. If factor counts differ and r is the smaller count, then r<=t,
the larger side is at least `(F+1)^(r+1)`, and the smaller is at most
`(1+L F)^r <= L^r*(F+1)^r`. This contradicts
`F+1>L^t>=L^r`. Hence both counts equal m<=t.

The coefficients of each product polynomial in an indeterminate z are
nonnegative, and their sum is at most `(1+L)^m <= (1+t^d)^t`.
For t>=2, `1+t^d<=2t^d<=t^(d+1)` (d>=0). Thus every coefficient has
absolute value at most `t^((d+1)t)<F`. The difference coefficients have
absolute value below F because each lies in the interval [0,F-1]. The
least nonzero coefficient argument modulo F proves that evaluation at F
is injective on these two product polynomials. Unique factorization over
Q recovers label multiplicities from the equality at F. This is exactly
the Horn-flow information formerly extracted using h<t.

For the actual source, the finite positive-DAG ledger must certify a
specific d. One must not guess it from constructor names or omit the
coefficient bound. The removed h condition may also have been used in a
local arithmetic size ledger; that ledger must be rerun with the new
polynomial upper bound, rather than citing the old h<t estimate.

## 6. Expected coordinate balance, before literal emission

Relative to a factorial-free strict-range pooled source, delete the h
numerator output, its private range quotient and normalized remainder,
the h sum wire, and its three principal pair coordinates. This is seven
coordinates. The reused c0 pair already exists. Add the three coordinates
for the new independent nominal index D0*t (if not already present).
The net expectation is four fewer coordinates and typically four fewer
quadratic residuals. These are structural expectations only: the emitter
must recheck liveness, degree, every frame atom, pool membership, all
coordinate shifts, and the final collected counts.

The cap bound now excludes c0 from the nonanchor sum and includes the new
D0*t pair. Its pooled orientation includes c0 and D0*t. The output
`(q+1)^c0`, the exact c0 range test and the congruence B|c0+F+1 MUST remain.

## 7. Balanced variable-index variant used in the frozen construction

The proof also applies with a positive polynomial index K in place of
D0*t, provided the frame includes K and the first power is F=t^K.
The selected coefficient-preserving instance is

```
t=128+4z^2,  T=t^2,  K=T^2=t^4.
```

The constructor-depth calculation in CONSTRUCTOR_DEPTH.md gives
`label<t^ell`, ell=2^20. Since `t^3>=2^21>ell+1`, the same multiplicity
proof has `(1+t^ell)^t<F=t^K`. All sign, oddness, CRT-radius and beta
completeness estimates used above require only F>=t^t, which holds.
The oddness proof becomes `v_2(F)=K*v_2(t)>log_2(t)`.
Choose the even encoded anchor cofinally above K as well as every other
retained index; the argument in Section3 is unchanged. This variant adds
one further coordinate relative to an already materialized affine index
(the t-squared wire), while avoiding its large constant coefficient.

