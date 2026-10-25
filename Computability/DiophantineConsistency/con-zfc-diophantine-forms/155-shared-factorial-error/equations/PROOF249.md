# Three compatible reductions: 249 unrestricted integers

`equation249/equation.json` is a quartic in249 integer coordinates,
specified as the sum of182 quadratic residual squares. Its fully collected
polynomial has5321 terms and height128446. It composes the common-normalized
remainder construction, the odd-square-radix construction proved in
`PROOF.md`, and the deterministic comparison center proved in the retained
`DETERMINISTIC_CENTER_SOURCE_PROOF.md`. These individual mechanisms are
inherited; this compatible composition is the present finite endpoint.

The deterministic-center source's selected-nine orientation reduction is
NOT used. The full original squared-abscissa orientation pool remains
literally unchanged. This matters because it preserves the signed-power
lemma available before any arithmetic sign assumptions, which the reordered
odd-square bootstrap needs.

## Source mutation

Start with the complete factored common-remainder source in
`parent252/data/factored_source.json`. Change its comparison-constructor
and index-residue rows from

    D = 1+4J(2d+1),        R = h+4Ck

to

    f=(1-A)H,             R = h+Ck.

Keep D=A+Hf, H^2-(A^2-1)J^2=1, J=C^2(2e+1), both comparison-norm and
abscissa-congruence rows, the squared cap and every principal norm. The
coordinate d becomes unused. At the same source stage replace

    q=B+o+1,        o=a^2+b^2+c(c+1)

by q=(2z+1)^2. Its old four private coordinates become unused. All eleven
normalized remainders, the three ratio rows, single common norm bound,
all source/Horn residuals and the entire squared orientation pool are
retained. `source_delta.json` records these four changed/deleted rows and
the new row. `projection_certificate.json` records every subsequent monic
integral elimination, with a complete inverse; fixed translations are then
applied by the stated convention old=new+shift. These finite coordinate
maps do not change existence of integer zeros.

## Why the new center is compatible

Let a=|A|. The inherited square frame gives W>=258, a>W^W, every requested
index and power atom below W in absolute value, and |A-1|>4W^3. The cap
gives C!=0, |h|<|C| and every other principal ordinate smaller than |C|.
Since J=C^2(2e+1), J!=0. The new center satisfies

    D=A+(1-A)H^2=1-(A-1)(A^2-1)J^2.

Thus |D|>1, D=A modulo H and D=1 modulo C, with no sign or parity
assumption about A. Classify the anchor and common Pell pairs as
|C|=Y_i(a), |J|=Y_l(a). For i>=2, squared divisibility implies |C| divides l,
and l>i. Abscissa separation, transferred through D=A modulo H, gives
the comparison index j=+-i modulo2l. The new ordinate residue and D=1
modulo C give j=+-h modulo|C|. Hence i=+-h modulo|C|. Pell growth gives
Y_i(a)>=i+2a-2, so i+|h|<|C|. The congruence forces i=|h|<W.

At the exceptional i=1, |C|=1. The squared cap then forces h=0 and all
other actual indices zero. All actual indices are still bounded by W.
The retained squared orientation pool, reduced modulo A-1, is a sum of
nonnegative small squared errors. The anchor ordinate contributes1.
The full sum is strictly between0 and|A-1|, contradicting its divisibility.
Thus the exceptional branch has no solution.

The same bounded-error argument now orients every one of the fourteen
principal pairs at its signed requested index, exactly as required by
`PROOF.md`. That proof's acyclic bootstrap recovers B>=2, then x>=2,
then nonnegative representatives at base q+1, and finally q=(BH0)^x>B.
The common-remainder magnitude and digit arguments therefore retain their
premises and decode a finite C222 refutation. One does not need to
reconstruct the OLD private comparison center from an arbitrary zero:
the new center directly establishes the same index theorem, after which
the unchanged semantic front is decoded.

For completeness the parity choices in `PROOF.md` preserve an even,
dominant semantic anchor h, hence C=Y_h(A) is even and U=X_h(A) is odd.
Choose the common index l=hC. Pell composition gives
J=Y_l(A)=C Y_C(U), and the binomial expansion gives
Y_C(U)/C=U^(C-1) modulo C. Thus J/C^2 is an odd integer, so the unchanged
odd-auxiliary row has an integer solution. Set H=X_l(A),
f=(1-A)H, D=A+Hf, S=X_h(D), R=Y_h(D). Polynomial transfer supplies
S=U modulo H and R=h modulo C. All comparison rows hold with integer
quotients, even when D is negative. The full squared orientation pool
also has an integer quotient. The common normalized remainders and the
odd-square radix are supplied as in `PROOF.md`.

Composing with the retained named C222/ZF/ZFC refutation calibrations
proves in ZFC that integer unsolvability of the literal249-variable
polynomial is equivalent to Con(ZFC). This is an ordinary proof with
reproducible finite algebra, not a newly completed formal-kernel proof,
and none of the three component mechanisms is claimed as a new general
number-theoretic discovery.
