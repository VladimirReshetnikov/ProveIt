# Proposed editorial synchronization (not an automatic patch)

Source pin: `446dca9bd65c20e409d1d2561d4ffad408103e2a`.
Target: `Analysis/Polylogarithms/docs/manuscript/chapters/10-discovery.tex`.

The general J(p/q) formal symbol-classification question is still described
as open, while the report at
`Analysis/Polylogarithms/docs/reports/herglotz-rational-classification/sections/04-classification.tex`
contains a complete formal-classification theorem and argument.

Suggested replacement, after the normal review of that existing report:

> The general rational J(p/q) classification in the stated five-term formal
> calculus is supplied by the Herglotz rational-classification report. For
> coprime mixed-parity entries e (even) and o (odd), its logarithmic and
> rational-dilogarithmic conditions coincide: e² ≡ ±1 (mod o) and o² ≡ 1
> (mod 2e). For odd entries, the rational-dilogarithmic cases have p,q in
> {1,3,5}, while the logarithmic case is p=q=1. Constructing short explicit
> evaluations throughout the positive classification and deciding numerical
> period relations remain separate research tasks.

Do not cite the quadratic-spectrum report as the original source of that
classification. The current contribution inspected its statement and argument
section, but did not independently re-audit every prerequisite symbol lemma.
Retain the distinction between formal nonmembership and numerical independence.
Do not change the S6 status or replace the rejection of a particular frozen
S8 vector by a rejection of every possible S8 relation.
