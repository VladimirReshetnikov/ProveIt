# Independent finalizer and bridge-interface review

Reviewed: `con_zfc_quadratic_packing/code/build.py`, package 31's
`SIGNED10_PROOF.md`, and the primary papers:

- <https://arxiv.org/html/1704.03504v7>, especially Theorems 4.12 and 4.13;
- <https://arxiv.org/html/2609.01594v2>, especially Sections 2--4 and 6.

The local algebra and the interface composition have no identified
obstruction. This is a mathematical review, not a new proof-assistant
certificate or an independent reconstruction of the full upstream theory.

## 1. Source properties needed by the bridge

The changed source uses b=1+3f, B=beta_S*b^2, and

`Ccap=b*B^799=beta_S^799*b^1599`.

Since beta_S is a fixed positive power of two, this has the required fixed
power form. Its exponent of b is odd, though the 2026 statement only needs
fixed positive exponents. As beta_S is an even power of two and b=1 mod 3,
B=1 mod 3, N=4*B^(M+t+2)=1 mod 3, and therefore 3 divides X=(N-1)R.

For f nonzero and b an integer square, b=1+3f forces f>0 and b>=4.
Thus B is a positive integer even before the reverse bridge establishes
that b is a power of two. D(B)>0 and the arbitrary-g bounds hold on this
whole domain. Consequently X>3b and Y>max(b,256) are available before
the use of the reverse Pell/binomial argument. There is no circular use
of binary digit decoding at this stage.

On the positive direction, the new source supplies arbitrarily large f
and b<=g<Ccap, with b a square and a power of two and Y dividing the
central binomial coefficient. The old positive construction is expressed
for arbitrary b,g,X,Y satisfying those conditions. In particular, Sun
2021 Theorem 4.12 constructs h,k,l,w>=b, so A>2 is even and Bsmall>0
is odd. Those are precisely the interpolation theorem's sign and parity
hypotheses.

The new source is not literally the old recipe used in the statement of
Sun 2026 Proposition 2.1. The correct composition is to observe, from
the proofs of Propositions 6.1 and 6.2, that they use only the established
source interface: the two existential directions, the form of b, the
positive coding bound, and the stated off-language size bounds. Their
proofs therefore apply to the replacement source. This observation should
be stated rather than treating the changed source as a verbatim instance
of the original recipe.

## 2. Positivity and the shared Pell witness

The positive binomial bridge yields Delta>0, and its displayed formula
makes Delta a multiple of the positive integer g. Thus Delta>=g>=b>=4.
As f and l are nonzero, O=f^2*l^2*Delta>=4.

Let d=3O-4. It is positive and is 2 modulo 3, hence is not a square.
The Pell equation u^2-dv^2=1 has a positive solution with b dividing v:
raise a positive Pell unit to the finite order of its unit class modulo
b. This works even when d and b are not coprime because the unit has norm
one. Put z=v/b>0. The positivity radicand is then a square, as is

`r0=b*(1+(3O-4)*b^2*z^2)`

because b is already a square.

Now apply Sun 2026 Theorem 4.1 with its divisibility parameter N=z. It
first supplies a positive xi divisible by z and then permits an arbitrary
residue class for y modulo xi. Hence x=xi/z is an integer, and the
subsequent congruence condition on y is legitimate. There is no inversion
of the quantifiers and no extra witness.

For the reverse direction, z!=0 and r0 square force b to be a positive
square: b and its other factor are coprime; a negative square cannot be
1 modulo 3. The zero-factor possibility similarly forces b=1 and is
excluded by the actual formula O=f^2*l^2*Delta. Once b>0, the bracket is
a square. If O<=0, that bracket is at most 1-4*(bz)^2<=-3, a contradiction.
Thus O>0. This last implication is elementary and need not invoke a
separate positivity theorem.

## 3. Quintic divisibility merger

The fixed polynomial `(v^3-v-1)*(v^2+23)` has no rational zero. It has
a root modulo every positive modulus: for odd primes away from 23,
either the cubic has a simple root or its irreducibility makes its
discriminant -23 a nonzero square; at 23 the cubic has the simple root
3; at powers of two, -23 is a square because it is 1 modulo 8. Hensel
lifting and the Chinese remainder theorem give the assertion.

Write S=2A-5, so S is always a nonzero odd integer. The homogeneous
quintic Theta is consequently nonzero for every integer assignment.
When S divides T, writing T=S*q reduces the condition
`xi*S^5 | Theta` to a root condition for the fixed quintic at q+y
modulo xi. This is exactly the residue class permitted by interpolation.

Conversely, if a prime has valuation alpha in S and beta<alpha in T,
then T+S*y has valuation beta. The cubic homogeneous factor of Theta
has valuation 3*beta, and the quadratic factor has valuation 2*beta.
Thus S^5 cannot divide Theta. This proves the required reverse merger.

## 4. Separation and the final norm

If z!=0, the actual r0 cannot be 0 or +/-1. The latter cases force
b=1, hence f=O=0, whereas r0=1-4z^2<=-3; the zero case is equally
incompatible. Therefore |r0|>1.

For r1=(Pn^2-4)K^2+4, one has

`sqrt(abs(r1)) <= Pn^2+K^2+2`.

It follows that the signed weights

`1, r0, r0*(Pn^2+K^2+3)`

have strict successive magnitude separation. In any multiquadratic field,
an automorphism that changes at least one weighted radical has a largest
changed index. Its magnitude exceeds the sum of all earlier changed
terms, so a rational signed sum is impossible unless every radical is
rational. This remains valid for negative radicands using complex
absolute value; zero radicands are already squares.

The displayed radical-free norm equals the product of the eight signed
linear radical factors. When Sigma=xi*S^5 is zero it reduces to Theta^8,
which is nonzero. Hence a final zero has xi!=0 and z!=0. Dividing a
vanishing factor by Sigma and applying separation gives all three square
conditions and Sigma|Theta. The reverse merger and coprime-square step
therefore give every hypothesis needed by the reverse bridge.

## 5. Remaining dependency boundary

The review checked that the new source preserves the required hypotheses
and that the inherited finalizer's local arguments compose correctly.
The reverse Lucas and approximation results remain dependencies on the
cited primary papers, especially the 2026 preprint. The machine-to-parent
equivalence remains a dependency on the pinned K215/compiler development.
Finite circuit and coefficient audits do not replace those theorems.

The new circuit retains ten unrestricted integer variables. Its source
and finalizer contain only fixed integer powers and integer arithmetic;
the radicals, divisibility predicates, and quantified coding witnesses
occur only in the proof.
