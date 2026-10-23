# Further directions and rejected shortcuts

This file contains **no additional claimed construction**. The proved
results are exactly those listed in `RESULTS.json` and `report.pdf`.

## Direct binary disjointness

For nonnegative integers S,T, absence of binary carries in S+T is
equivalent to the binomial coefficient `binomial(S+T,S)` being odd.
The current nine-variable route realizes disjointness through a larger
central-binomial index and a divisibility threshold. An explicit small
Diophantine interface for the direct oddness condition could remove a
major source of degree inflation. The carry identity alone does not
provide that interface. No replacement polynomial is supplied here.

## More sign recovery

The Q42 common-sign proof is noncircular because it recovers the main
Pell rank before invoking the predecessor's whole-system theorem.
Additional positivity guards might be removable if a similar rank or
congruence argument recovers their signs. Simply dropping a guard and
appealing to a theorem that assumes it would be invalid. Letting both
scale coordinates become negative changes the binomial decoding; the
needed converse has not been proved.

## Rational roots and divisibility

A norm can imply rationality without the required integrality or quotient
congruence. The example

    63*((4/3)^2-1) = 7^2

disproves the local claim that the strong Pell-looking equation by itself
forces a rational f to be integral. It does not disprove a full system
with all additional source constraints. Likewise, replacing X,Y by
apparently free coordinates loses q|X, q^3|Y, and related scale conditions
unless each is independently recovered.

The P13 norm avoids this issue: one recovered root has an integer square
and is rational, hence integer; the second is literally the difference
of two integers. Additional root mergers need comparably explicit
integrality and divisibility arguments.

## Source-level changes

A direct primitive-recursive proof-certificate checker, a different
register-machine language or a smaller calibrated tiling compiler may
reduce coefficients or equations more substantially. Such a proposal
must include both compiler directions and a precise fixed source.
Invoking MRDP without producing its instance does not close this task.
The present artifact retains K215; it does not assert a K215-free result.

## Scope of the advance

The current changes improve several exact points in the pinned repository
frontier, with two useful mathematical mechanisms and reproducible data.
They establish no absolute simplest equation, no new universal
variable-count record, and no independent literature priority. Formalizing
the new literal equations and their entire ordinary compiler chain is a
separate, still-uncompleted task.
