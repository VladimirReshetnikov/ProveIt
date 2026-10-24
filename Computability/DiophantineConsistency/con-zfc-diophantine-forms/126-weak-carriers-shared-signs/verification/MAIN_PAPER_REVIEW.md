# Independent review of the main manuscript

Reviewed file:
`ConZFC_Weak_Carriers_and_Shared_Signs_2026-10-24/report.tex`

Comparison files: `norm/MIXED_PROOF.md`, `norm/PROOF.md`, the copied
`inherited/norm/source/centered11-proof.md`, and the supported-modulus
argument in `inherited/norm/powered_saturation_proof.tex`.

## Assessment

The mixed eleven-integer formulas in the manuscript match the delivered
ordinary proof. In particular `I=rc^2`, `Dg=1+(3B-4)Dt*s^2`, the
three-adic weights 1,3,9, carrier `M=2q^2`, `D=MH`,
`z*=DT+MK+H(v-q^2)`, scale `S=sr*M^5*H`, and center `3QV` are
transcribed consistently. The cubic specialization also matches its
separate proof.

The zero-case order is correct and important. First `S!=0` follows from
the rational-root-free intersective polynomial. This proves `s,r!=0`
but does not assume `c!=0`. The auxiliary radicand is positive even
when `c=0`, because that branch gives `Da=1`. The imaginary-root argument
and parity then force a positive budget. Three-adic separation gives
the integral roots and `S|A*` before auxiliary descent. Only after the
mixed carrier restores `Y=(2v0+1)q^3` is the `c=0` branch contradicted.
Thus the eventual use of `Q>1` is licensed.

The strong/weak carrier lemma is valid at every prime, including 3 and
19; extra divisibility of nonleading coefficients only strengthens the
unique least-valuation argument. Coprimality of `M` and `H` is correct:
`H` is odd, `H=3 mod q`, and `q=2 mod3`. No invalid cancellation of
prime multiplicities occurs in the weak `H|K^5` step.

The adjacent-coefficient denominator descent is complete: `b^2|Q-1`
ensures the descended first coordinate is integral; `2Q-1=1 mod b`
preserves the reduced denominator; the norm makes its positive absolute
value strictly decrease until one.

The supported-modulus interpolation is applied with a fixed strong pair
chosen after `s`. Since `4sc^2|I` and `r=I/c^2`, every prime of `sr`
divides `I`. Its valuation-isometry argument permits arbitrary powers
of those primes, so it legitimately addresses a modulus that need not
divide `I`. The final residue is selected only after `I,f,r` are fixed.

I independently recomputed the leading-form arithmetic. For the mixed
chart the top form is

    2^64 3^14 s^12 r^24 c^32 q0^84 X0^40 Y0^52 R0^4 k0^12.

Selecting the `h^12` term of `k0^12` and the `z^4` term of `R0^4`
gives exactly

    [j^216 w^52 v^64 h^12 z^4 s^12 r^24 c^32] P
      =2^384 3^282 beta^216.

The cubic version gives the stated coefficient
`2^456 3^330 beta^264` at total degree 464. Thus the two displayed
nonzero specialization certificates are consistent with the formulas,
not merely their claimed degree counts.

The manuscript distinguishes new composition from inherited individual
ideas, ordinary calibration from finite algebraic tests, and eleven
variables from the existing ten-variable frontier. These novelty and
formalization boundaries are appropriate. The coefficient port `A0`
and the Pell base `A=a+2` are distinct and not ambiguously used in the
new proof.

## Requested editorial corrections

These were sent to the root agent; this reviewer did not edit the paper.

1. The display labelled `eq:budgetpositive` has three literal `,quad`
   tokens. Replace them by `,\quad`.
2. At the start of completeness explicitly recall that the canonical
   source supplies even `A=a+2`, `R=3 mod4`, and `c=R mod4`. These are
   hypotheses of the interpolation theorem; the copied centered source
   states them in Section 7, but their availability should not remain
   implicit in this manuscript.
3. In the supported-modulus proof, specify `h>=0` in `nu0+d*h`, and
   nonnegative distinct `h1,h2` in its isometry. This is the domain used
   by the source proof and keeps every Pell index nonnegative. CRT can
   choose a nonnegative representative, so it causes no restriction.

## Scope

This is a mathematical and transcription review of the new small-variable
construction and its stated inherited interfaces. It does not rerun the
full native/compiler or object-ZFC calibration. The separate direct
construction review and exact source checker cover the 478-integer
local guard and frame changes.

## Integration resolution

The manuscript editor applied all three requested corrections before the
released PDF was compiled: the budget display uses the proper LaTeX spacing,
the canonical parity hypotheses are stated at the start of completeness, and
the interpolation parameters have their nonnegative domains explicitly stated.
This resolution note was added by the manuscript editor, not the reviewer.
