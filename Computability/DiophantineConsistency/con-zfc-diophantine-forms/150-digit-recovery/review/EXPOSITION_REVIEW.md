# Independent mathematical exposition review

Reviewed `article.tex` on 25 October 2026, focusing on the fresh factorial
fixed-point argument, the cofinal representative lifts, and the description
of the three-parameter-calculus experiment. This is a review of the ordinary
mathematical argument and reporting boundary, not a new formal verification
of the inherited CRT/Pell or logical calibration developments.

## Outcome

No mathematical correction is required in the reviewed passages.

## Factorial fixed point

The explicit argument is valid. With `T=t!`, positive `F`,
`B=binom(F^2+t,t)`, `V=(F^2+1)^t`, and
`B(F-1)<V<=BF`, the recovered relation is

`F=ceil(V/B)` and `V/B=T*product_(i=1)^t (F^2+1)/(F^2+i)`.

Each factor is nondecreasing in `F^2>=1`; its value at `F^2=1` gives
`V/B>=2^t/(t+1)>t^2` for `t>=16`. The stated induction inequality
`2t^2>(t+1)(t+2)` is sufficient. Consequently `F>t^2`.

The finite product inequality then gives

`V/B > T*(1-t(t-1)/(2F^2)) > T*(1-1/(2F))`.

Together with `V/B<=F`, this yields
`T < F+F/(2F-1) < F+1`; integrality gives `T<=F`. The first product bound
already gives `F<=T`, so equality follows. Strict inequalities and the
`F>1` condition used in the last step are justified. The completeness
direction still explicitly invokes the inherited cofinal construction;
the article does not claim that the displayed uniqueness proof alone is
that complete construction.

## Digit-first chronology

The early divisor `q^(t+1) | q^x` gives `x>=t+1` using `q>=9`, without
factorial or ceiling signs. The endpoint then gives
`x>=2+(t+1)y`. For `F^2>=1`, Bernoulli gives
`V>=1+F^2*t>=F^2+t`, and `V(V-1)>=V`; the `F=0` case is handled
separately. Thus the bound `2^(F^2+t)<=q/2` does not assume `F>0`.

The two remainder intervals have strict total width below `M`, so their
congruence forces equality. The digit comparison then uses both
`|B|<q/2` and `0<binom(F^2+t,t)<q/2`. Only after this positive digit
is recovered is the weak product guard used. The sign bootstrap is
therefore not circular in the reviewed exposition.

## Completeness and representative lifts

The beta moduli are odd because `y=V(V-1)` is even, so their CRT class
contains arbitrarily large even choices of `x`. After `F=t!`, each
`F^2/i` is divisible by 6, and consequently `B,N,N^2` are congruent to
1 modulo 6. Adding multiples of `N^2` therefore preserves local coding
and allows any desired residue modulo 6.

The choices `a=a0+8N^2` or `a0+9N^2` give the required parity relative
to `b`, since `N^2` is odd. The stated literal label parity
`h=1+a+b mod2` makes the anchor even. Adjusting another representative
does not alter that parity. Its six possible lifts arrange `H0=3 mod6`.
The inequalities `h>=2a^2>=128N^4` and all other representatives below
`10N^2` leave substantial room for the inherited anchor domination.
The radix and private frame are chosen after the lifts, so no old
aggregate bound is incorrectly retained.

For positive even `x`, `(BH0)^(x/2)` remains an odd multiple of 3.
Hence it is congruent to 3 modulo 6 and supplies the asserted integer
square parameter. No exact 3-adic valuation is accidentally imposed.

## Claims about the experiment and the main theorem

The experiment is correctly reported as a separate quartic over 231
nonnegative integers with 183 residuals, 6,369 monomials, and height
83,899,166. It loses to its 229-variable natural parent. The report
does not equate these domains with the 247 unrestricted integers of
the preferred result. Its standalone checker validates the literal
521-step K/S/Peirce proof and polynomial coefficients; rebuilding its
arithmetic graph needs the separately pinned parent source. These
limitations are stated accurately.

The main theorem explicitly composes the ordinary new argument with
retained arithmetic/calibration proofs and checked finite transformations.
The article does not claim a new end-to-end Lean theorem, global
minimality, literature priority, or a proof of ZFC consistency.

As a small independent check against the literal final polynomial, the
three coefficients quoted in the article are correct: constant 3,494,
`z1^4` coefficient 13, and `z12^2*z14^2` coefficient 8,815.

Bibliographic author/version details are outside this review and remain
subject to the main author's source verification. No article text was
edited by this reviewer.
