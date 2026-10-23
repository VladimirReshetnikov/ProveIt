# Independent review of the twelve-positive-variable degree-1065 construction

## Scope and conclusion

Reviewed `../sections/positive.tex`, including the new
weight, weighted carrier, radical recovery, saturation lemma, completeness,
and exact degree argument. The underlying compiler dependency was compared
with the frozen package-25 `HYBRID12_PROOF.md` and package-30
`POSITIVE12_PROOF.md`. I found no mathematical defect in the new local
reduction. The end-to-end claim still depends on the stated inherited
normalized signed-quotient compiler/Pell interface and K215 calibration.

This is an independent mathematical review, not a proof-assistant certificate
or an assertion that ZFC is consistent. The arithmetic circuit audit is
separate from this note.

## Checks of the pre-recovery bounds

The weak bootstrap is invoked only after the product parity argument has
given `N=0` and `Nk=Nt=epsilon`, or directly for the three-equation system.
It requires only `Cw>=0`, not the stronger `Cw>0`. Thus the exceptional
transport boundary is not silently excluded.

The quantities needed for the new bound are positive at every tuple to
which the bootstrap applies, although the carrier need not have any
particular sign at arbitrary inputs off the solution set. In particular
`R>0`, `Delta>R+2`, `Q=(Delta I)^2>1`, and `M>0` hold at this stage.

The step `Q-b>0` follows from

```
Q-b = Delta*I^2*(Delta-R)-c-R,
```

with `Delta-R>2`, `I^2>=c^4` and the large positive bootstrap bounds.
It gives `b<=Q-1=d`. Also `sqrt(D)<Delta*I<d`.
Writing `Z1=v*sqrt(D)+b`, the claimed inequality

```
(Q*Z1^2+1)/d < [Z1*(1+1/d)]^2
```

has difference `(Q*Z1^2-d)/d^2>0`. Since all conjugates of f are
`+sqrt(D)` or `-sqrt(D)`, it bounds all conjugates of y, including
imaginary ones. It yields `|y|<Z1+v+1` without having recovered a root.

The rational identity for the sharp weight is correct:

```
(a+2)^2*(1+1/Y)/E
 = E+2Y+X+6+Y/X+5/X+4/Y+8/E+4/(E*Y).
```

Here `Y/X=s*q^2/w<=s*q^2`, while `X>=16` and `Y>=q^3` make
`5/X+4/Y+8/E+4/(EY)<1`. Thus its right side is strictly smaller
than `C_*-2`. Together with `(a+3)*(1+1/Y)/E<2`, the stated
bound `|y|<M*sqrt(A)` follows. The final absorption of the small `+2`
term uses `R*i^2*c^3>=1`, which is available from positivity.

The independent inequalities `G>A` and `b0>sqrt(A)` are valid before
recovering any radical. For the latter, the displayed difference

```
a^2*k^2*Y^2-A = k^2*(E*Y*(2Y^2-1)+Y^4)-1
```

is strictly positive. No main-Pell equation has been assumed in deriving it.

## Why the smaller carrier works

For `W=L*b0+H*t` and `L=1+H*M`, the negative-g argument has input

```
(W+L*sqrt(G))/H = t+(L/H)*(b0+sqrt(G)) > 2*M*sqrt(A).
```

Every root of the inner polynomial has modulus strictly smaller than
`2*M*sqrt(A)`, so this branch cannot vanish. If G were nonsquare,
its rational quadratic conjugacy would force both main-root factors
to vanish whenever either does. Hence G must be a square, and the
selected g is positive. This correctly replaces the source construction's
larger generic carrier; it is not merely a formal rescaling of that carrier.

Once g is rational, any automorphism sending an irrational tau to its
negative would send y to another conjugate a distance `2*M*sqrt(A)`
away. Both are strictly inside the disk of radius `M*sqrt(A)`, a
contradiction. Thus tau is rational and integral. The linear relation
then makes y rational, and `f=(e-d*y^2)/B_a` makes f rational because
`B_a>0`. Since `f^2=D` is integral, f is integral.

## Rational auxiliary Pell saturation

The supplied saturation lemma is sound. With `y=u/v0` in lowest terms,
`v0^2` divides `S^2-1`, and `D0=(S^2-1)/v0^2` is a positive
nonsquare integer. If D0 were a square, factoring
`S^2-D0*v0^2=1` would contradict `S>=2`.

The integer-coordinate norm-one Pell solutions `(S,v0)` and
`(S*|V|,|u|)` are powers with indices j and l of the fundamental
integer-coordinate positive unit. The first-coordinate congruences
under translation by 2j and reflection about j reduce the divisibility
`chi_j | chi_l` to an index in `[0,j]`. Strict growth forces that
index to equal j, so l is an odd multiple of j. The second-coordinate
divisibility then yields `v0|u`; coprimality gives `v0=1`.
Using integer-coordinate units is essential and is stated explicitly.

After saturation, `L=1 mod H` and `W=b0 mod H` give the main
congruence. The positivity estimate
`g-b0>(a+1)c-ac-X=c-X>0` is valid because `c>k>E>X`.

If the recovered f is negative, the simultaneous sign change of f and T
preserves their product. The required signed-T compiler interface is
explicitly present in both compared source proofs; the new reduction does
not invent that extension. The canonical completion formula
`t=L*gamma+M*tau+y` is positive and satisfies the coherent factor identity.

## Exact degree review

The Laurent expansions have integer orders because the leading forms of
the relevant radicands are nonzero squares in the rational function field.
All their conjugate branches are included. The exact identity

```
C_*ell-Delta*c
 = (2EX+E*s*q^2-Y^2-4E-4Y-3)*c-E*C_*eta
```

has unique degree-14 leading term `E0*(s*q0^2)*c0`. It therefore gives
the stated degree-35 cancellation term in `M*sqrt(A)-b`.

The positive quotient `gamma_+=(sqrt(G)-b0)/H` has order -1:
`sqrt(G)=a*c+2c+O(lambda^-1)`, whereas `H` has degree six.
Thus `L*gamma_+` has order 32 and does not affect degree-35 terms.
Also `sqrt(G)+b0-2sqrt(A)` has degree-nine leader `2*Y0*c0`,
giving the degree-36 secondary cancellation for the negative main branch.

The sixteen factors divide as follows:

| Main branch | Sign relation | Number | Degree | Leading form |
|---|---|---:|---:|---|
| Positive | Opposite leading tau/y signs | 4 | 35 | plus/minus C |
| Positive | Matching leading tau/y signs | 4 | 38 | plus/minus 2B |
| Negative | Both selected positive signs | 2 | 36 | 2D |
| Negative | One selected negative sign | 4 | 38 | 2B |
| Negative | Both selected negative signs | 2 | 38 | 4B |

Here B, C and D are the three nonzero leading forms defined in the proof.
The coefficient from the factors is `2^14*B^10*C^4*D^2`.
With the prefactor `d^8*H^16`, the degree is exactly

```
8*46 + 16*6 + 4*35 + 2*36 + 10*38 = 1056.
```

Expanding only these leading forms gives precisely

```
2^46 * i^48 * k0^96 * w^74 * s^176 * q0^646 * (q0-F)^16.
```

Multiplication by the index and transport factors raises the degree to
1065. Selecting their displayed terms gives the stated monomial with
coefficient `2^46*beta^667`, nonzero for every authentic tuple. The
argument proves both an upper degree bound and a nonzero top form;
it does not rely on a generic numerical degree estimate.

## No further correction requested

The reviewed local proof handles its new branch exclusion and degree
cancellations explicitly. No additional assumption about a special
canonical strong rank is used for positive completeness. The main
remaining dependency is the already identified compiler/Pell interface,
which should stay visible in the report and artifact metadata.
