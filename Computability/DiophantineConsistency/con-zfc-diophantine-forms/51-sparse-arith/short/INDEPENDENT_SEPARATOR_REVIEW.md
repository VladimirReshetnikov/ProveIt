# Independent review of the arithmetic separator (1,b,bK)

Reviewed against the literal definitions in package 40's `code/build.py` and
package 31's `signed10/SIGNED10_PROOF.md`, at repository commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`.  This review checks the local
arithmetic replacement of the three norm weights.  It does not independently
reprove Sun's bridge or the native-window compiler.

## Verdict

The replacement weights `(1,b,bK)` suffice.  The proof works over arbitrary
integer assignments before invoking source-size bounds, digit decoding or
Lucas interpolation.  In particular neither a large-|K| bootstrap nor a
sign assertion about the third radicand is necessary.

## Exact hypotheses used

The source definitions imply:

1. `b=1+3f`, hence b is nonzero and b=-1 is impossible.
2. `r0=b J`, where `J=1+(3O-4)b^2 z^2`, so gcd(b,J)=1.
3. `O=f^2 l^2 Delta`; if b=1, then f=O=0.
4. `Pn=U^2 V` is even and `A=U(V+1)` is even, because U=2lYX.
5. `r1=(Pn^2-4)K^2+4` and `r2=D F I`, with
   `D=(A^2-4)C^2+4`; therefore both r1 and r2 are divisible by four.
6. The coding cap is positive once b>0.
7. At K=0, `Delta=-32 g^2 C^2 cap^3<=0` once cap>0.
8. `Sigma=zx S^5`, S=2A-5 is nonzero, and the homogeneous quintic Theta
   never vanishes.  Thus a zero of the final norm has Sigma!=0 and z!=0.

Every item is either an identity in the literal source or the inherited
elementary rational-root obstruction for the fixed intersective quintic.

## 1. Extracting the first square without magnitude bounds

Suppose a signed radical sum

    +/-sqrt(r0) +/- b sqrt(r1) +/- bK sqrt(r2)

is rational.  Work in a multiquadratic extension of Q; negative radicands
cause no difficulty.  Distinct signed square classes have linearly independent
radical basis elements.  If r0 is nonsquare, write r0=d a^2 for signed
squarefree integer d!=1 and positive integer a.  Terms sharing the square
class d have integer coefficients on sqrt(d).

Vanishing of the sqrt(d) coefficient gives `+/-a+b lambda=0` for an integer
lambda.  Hence b divides a and b^2 divides r0=bJ.  Therefore b divides J.
Together with gcd(b,J)=1 this forces |b|=1, hence b=1.

At b=1 one has r0=1-4z^2, an odd negative integer because z!=0.  Its
squarefree representative d and square coefficient a are odd.  Any term
from r1 or r2 in that same square class has an even coefficient, since r1
and r2 are divisible by four.  Therefore the sqrt(d) coefficient is odd and
cannot vanish.  This contradiction proves r0 is a square.

This parity argument covers imaginary radicals as well as real ones and
also covers zero r1 or r2 (which simply have coefficient zero).  It avoids
an unnecessary sign analysis of DFI.

## 2. From the first square to positive parameters

The value r0 cannot be zero.  Since b!=0, a zero would give J=0, forcing
b^2z^2 to divide 1.  Thus b=1, z=+/-1, f=O=0, but then J=-3, a
contradiction.  Since r0=bJ is a nonzero square and gcd(b,J)=1, either
b,J are both positive squares or both negative squares.  The latter is
impossible because a negative square is 0 or 2 modulo three, whereas
b=1 mod3.  Hence b>0 and J>0 are squares.

If O<=0, then J<=1-4b^2z^2<0.  Thus O>0; in particular f,l are nonzero,
Delta>0 and b>=4.  The cap is positive.  If K=0, item 7 gives Delta<=0,
a contradiction.  Consequently K!=0.

## 3. Extracting the remaining two squares

Since sqrt(r0) is now integral and b is a nonzero integer, a signed sum of
sqrt(r1) and K sqrt(r2) is rational.  Absorb the signs into these two
radicals and call their rational sum t.  If t!=0, squaring once gives

    2 t sqrt(r1)=t^2+r1-K^2 r2

after a possible sign change in sqrt(r1).  Thus sqrt(r1) is rational;
K!=0 then makes sqrt(r2) rational.  Rational square roots of integers are
integers, so both radicands are nonnegative integer squares.

If t=0, then r1=K^2 r2.  The identity defining r1 implies K^2 divides 4,
so K=+/-1 or +/-2.  For K=+/-1, r1=r2=Pn^2, already squares.  For
K=+/-2, the equality gives r2=Pn^2-3=1 mod4, contradicting 4|r2.  Thus
the zero-sum case also forces both radicands to be squares.

This handles the potential zero-sum exception that is missed by a bare
"two radicals with rational sum are individually rational" assertion.

## 4. Divisibility and the final norm

The scaled final norm is the product of the eight signed factors centered
at `Sigma*m-Theta` with scaled radicands

    Sigma^2 r0, Sigma^2 b^2 r1, Sigma^2 b^2 K^2 r2.

When Sigma=0 the output is Theta^8, nonzero.  Otherwise a vanishing factor
gives a rational signed sum of the unscaled weighted radicals.  The preceding
argument proves they are integer radicals, hence Sigma divides Theta.

There is also an independent argument for the latter implication: the
unscaled norm is monic with integer coefficients in its center variable,
and the rational center `m-Theta/Sigma` is a root.  The rational-root theorem
makes it an integer.  This argument does not need the separate-radicand
conclusion and is useful for ordering any later bootstrap argument.

For completeness, when the inherited construction makes all three radicands
squares and Sigma divides Theta, choose the integer m from any signed sum.
The reduced weights introduce no new existential restriction or witness.

## Practical boundary

This is a proof of a local replacement for the literal Sun-style finalizer.
The full fixed polynomial still requires the source packing theorem, the
interpolation/bridge theorem, the coefficient specialization and the K215
calibration.  No claim of a new universal ten-variable theorem is warranted.
