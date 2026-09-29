# Excluded route: recovering a free exponent from congruences

This note concerns the proposal to delete the fixed-exponent Pell equations
and instead require that q divide the already proved power of two bw, and
that `q=Z^L+u(B-Z)` for a positive quotient u. Choosing the fixed scale
H with odd binary exponent does ensure `q=B^j` for some integer j, but
the two congruences do not force j=L or preserve the intended coefficient
code. The following is an exact counterexample for the retained coding
equations and their no-carry/binomial condition. No full auxiliary-Pell
instantiation is claimed here.

## The period can be much larger than the intended exponent

Write

    B=2^d,  Z=2^a,  theta=B-Z=2^a(2^(d-a)-1),
    P=(d-a)/gcd(d-a,a).

The admissible-index bound `H>2Z^(2L+1)`, together with `B=Hb^2`, gives
`d-a>2La`, and hence `P>2L`. On the odd part of theta,

    B^P = Z^P = 1.

Here congruences are modulo `2^(d-a)-1`. Consequently, for any integer
`r>=1`,

    theta divides B^r(B^P-1).

Set `j=L+P` and `q=B^j`. Then `j>L` but

    q = B^j = Z^L modulo theta.

Indeed the odd part follows from the period, and both q and Z^L are
divisible by the factor `2^a`. The required positive quotient
`(q-Z^L)/theta` therefore exists. If d is odd, this example also meets
the intended parity condition on the radix exponent.

## Moving a failed coefficient outside every target

Choose a fixed quadratic encoding with an ordinary residual `1=0`.
After homogenization it is `delta^2=0`, and the ordinary coefficient
rule makes its target value `2delta^2`. Let t be this row's target
position and let

    r=t-2>=1.

The corresponding term of the signed coefficient polynomial is
`2B^r`, since delta has weight one. Choose z a power of two greater
than 2 and all other coefficient magnitudes, and put Z=2z as usual.
The intended coefficient code is

    e_0(B)=z sum_{k=0}^{K-1}B^k+D(B).

Change only that code value to

    e'(B)=e_0(B)-2B^r+2B^(r+P).

At the old position the digit changes from z+2 to z; at the new
position it becomes 2. All digits remain in `[0,Z)`, and the value is
positive. Since `r<K<L`, its degree `r+P` is smaller than `j=L+P`, so
`e'<q`. The shift also preserves its residue modulo theta.

Keep the intended short indicator mask `ell_0(B)`. Set the encoded
unit coordinate to 1, choose positive input x=1, take u=1 for the guard
`u delta-x^2`, and take all other coordinates zero. The special target
and the guard pass. The originally impossible ordinary row now also
passes: its low coefficient term was removed. The replacement term
starts above P>2L, hence above every target position. No target can
see it.

With the fixed packed index

    V=ell_0(Z)+e_0(Z)Z^L,

the new packed code obeys

    Y'=ell_0(B)+e'(B)q = V modulo theta.

This follows from the two congruences just proved and from evaluation
of the fixed code polynomials at B=Z modulo theta. Its quotient is
positive. All its base-B digits are less than Z and it is smaller than
q^2, so the middle no-carry mask of length 2j accepts it.

## Positivity and the remaining masks

Use `lambda=(q^2-1)/(B-1)` and the same positive bound, coordinate code,
and third-mask formulas as in the 107-operation construction. The chosen
C has bounded low degree. The shifted term in `e' C^2` has degree at
most `P+3K`, which is smaller than `P+L=j` by the fixed support margin.
The admissible coefficient and radix bounds ensure `2e'C^2<q` after
choosing the power-of-two digit bound sufficiently large.

In particular `Omega=Zlambda-2e'>0`, and
`S_3=Blambda(1+q)-Omega C^2>0`. The first mask accepts the allowed
coordinate code; the third mask sees zero at every ordinary target
and one at the special delta-squared target. Its low coefficient
bounds are unchanged. The extra high coefficient lies outside all
indicator-mask positions.

Thus all three packed blocks have their intended ranges and no-carry
values, with the larger exponent j. The resulting r therefore satisfies
the central-binomial divisibility condition. In particular the failure
is not limited to an arbitrary long base-Z expansion: a single explicit
coefficient shift already defeats the zero-target interpretation.

The proposed extra divisibility q | bw is compatible with the intended
power relation `bw=2^(2r+1)`: both b and q are powers of two and r>=q^8,
so `log_2(bq)<2r+1`. It does not rule out this exponent or coefficient
shift. This observation does not replace a full construction of every
remaining auxiliary Pell witness, which is outside the stated scope
of this exclusion note.

## Scope

The missing inference is `Y(Z)=V`. Digit bounds alone give only
`Y(Z)=V modulo theta` when the number of digits is unbounded. Using
the fixed H bound to turn that congruence into equality would already
require an upper bound on j. The explicit periodic example above shows
that this cannot be repaired by the proposed q congruence or by the
existing coefficient and third-block positivity constraints.
