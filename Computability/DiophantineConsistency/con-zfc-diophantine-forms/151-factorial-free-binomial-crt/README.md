# Removing factorial authenticity from Diophantine consistency

**Research contribution for Vladimir Reshetnikov and ProveIt — 25 October 2026**

This packet gives a completely specified ordinary polynomial

\[
P(x_0,\ldots,x_{241})=\sum_{j=0}^{177}R_j(x_0,\ldots,x_{241})^2
\]

over **242 unrestricted integer variables**, with the ordinary mathematical
proof that

\[
\mathrm{ZFC}\vdash
\left(\neg\exists \boldsymbol x\in\mathbb Z^{242}\;P(\boldsymbol x)=0\right)
\longleftrightarrow \operatorname{Con}(\mathrm{ZFC}).
\]

Every quadratic residual is printed in **report/main.pdf** and supplied as
exact data in **direct/principal/equation.json**. The fully collected quartic
is also supplied. No coefficient is specified by an undecidable search, a
machine index, or a mere existence theorem.

The proof composes the new arithmetic results with the pinned ProveIt
numerical calculus C222, its calibration to syntactic ZFC refutation, and
its unchanged Pell power certificates. It is an ordinary mathematical
proof with exact finite artifact audits. It is not a fresh end-to-end
proof-assistant formalization or a proof of Con(ZFC).

## Result and comparison

| Equation over unrestricted integers | Variables | Quadratic residuals | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Matched common-remainder parent | 252 | 182 | 4 | 5,340 | 128,446 |
| **Principal equation** | **242** | **178** | **4** | **5,018** | **7,968** |
| Dense companion | 241 | 177 | 4 | 12,774 | 7,968 |

Height means the largest absolute coefficient after complete collection.
Both new equations have maximum residual coefficient 64. The principal
saves ten variables, four residuals, and 322 collected monomials relative
to its matched parent; its coefficient height falls by approximately
93.80%. The companion trades increased support for one fewer coordinate.

This is an improvement to the direct small-coefficient quartic family.
Other representations in the repository have fewer unknowns and different
degree, coefficient, or circuit costs. No global minimum or literature-wide
priority is claimed.

## The mathematical contribution

The old direct construction used an authenticated factorial F = t! for
both proof-label multiplicities and CRT row separation. This release
removes that requirement.

Let

\[
\Lambda_t=\operatorname{lcm}(1,\ldots,t),\qquad
R\ge\Lambda_t^2,\qquad B=\binom{R+t}{t}.
\]

The report proves two complementary facts:

1. For every row i in 1,...,t, some full prime power p^e in B divides
   R+i and satisfies p^e > t.
2. For every prime power p^e exactly dividing B, at least one row i
   satisfies p^e | R+i.

The first gives row-by-row soundness. The second makes the reverse CRT
construction work at **every** prime of B, including unused selectors.
The argument does not require pairwise coprimality of the consecutive
factors, or that R be the square of a factorial.

Separately, a bounded product of label weights 1+jF can be recovered as
an identity in an indeterminate. First equality forces equal nonunit
factor counts; then the coefficient bound (t+1)^t < F prevents carrying
at the integer evaluation point F. Unique factorization recovers the
label multiplicities.

These arguments permit the final semantic choices

\[
t=16+h^2,\qquad F=[2(t+1)]^t,\qquad
y=F(2v+1)^2,\qquad q=(2z+1)^2,
\]

with H = 2 + the sum of the nine actual CRT representatives. The first
power output is reused directly for F, so the inherited eighteen power
requests suffice. These formulas describe polynomially certified registers;
there is no variable-exponent operation in the delivered quartic.

The report proves the signed bootstrap in the order needed to avoid
assuming B > 0 before its binomial value is authenticated. It also treats
the possible algebraic boundary y = F explicitly: that branch would make
the first beta accumulator zero, propagate zero through the local rows,
and contradict the final accumulator one.

Factorials occur only in the completeness proof when choosing a suitably
divisible beta parameter. No unknown is constrained to equal t!.

## Contents

| Path | Purpose |
|---|---|
| report/main.tex, report/main.pdf | Complete mathematical report and principal residual appendix |
| report/results.tex, comparison.tex, verification.tex, residuals.tex | Generated report inputs, checked against the literal data |
| direct/principal/ | 242-variable equation, full expansion, exact metrics, residuals, variable metadata |
| direct/companion/ | 241-variable equation with the same kinds of exact artifacts |
| direct/factorial_free_affine/ | Changed raw source and complete factoring/projection/translation certificates |
| direct/factorial_free_affine242_balanced/, direct/factorial_free_affine241_balanced/ | Final reversible coordinate and row certificates |
| direct/parent/ | Pinned parent compiler, ordinary proof sources, logical interface excerpts, attribution |
| direct/sources/ | Credited odd-square and affine-exposure predecessors |
| direct/review/ | Exact normal and optimized-interpreter audit receipts and fresh rebuild receipt |
| review/ | Independent mathematical reviews and root verification receipt |
| code/check_new_lemmas.py | Small-case arithmetic regressions and explicit missing-hypothesis counterexample |
| code/report_inputs.py | Deterministic report data generation/checking |
| verify.py | Release verification driver |
| build_report.sh | LaTeX rebuild |
| SOURCE_LEDGER.json, MANIFEST.sha256 | Pinned sources and release integrity |
| INTEGRATION.md, NOTICE.md, LICENSE | Incorporation notes and attribution |

The labels in the variable metadata preserve historical provenance through
translations and shears. They do not, by themselves, identify unchanged
semantic values. The restoration certificates supply those interpretations;
the numerical coefficient lists and integer domain define the equation.

## Reproduction

From this directory, with Python 3.10 or later and its standard library:

~~~sh
python3 -B verify.py
~~~

This performs a fresh byte-identical reconstruction, independently replays
the source edits and all integral transformations, collects every quartic
coefficient, audits all eighteen power requests, checks readable exports,
runs the new arithmetic regressions normally and with Python -O, checks
the generated report inputs, and verifies the checksum manifest.

The audit includes 18 Horn factoring edits, 202 monic projections, six
coordinate shears, five affine-exposure row operations, three/four final
affine projections, and 34/36 final row operations. Seven deliberate
corruptions are rejected. The independent coefficient checker imports no
producer modules.

For a concise integrity-only check:

~~~sh
python3 -B verify.py --manifest-only
~~~

To rebuild the PDF, with a standard LaTeX installation:

~~~sh
bash build_report.sh
~~~

The LaTeX sources use standard packages: amsmath, amssymb, amsthm,
mathtools, lmodern, microtype, geometry, booktabs, longtable, array,
multicol, xcolor, fancyhdr, enumitem, hyperref, and url. Different TeX
versions can change PDF bytes without changing the equation. After an
intentional edit or rebuild, use --skip-manifest for semantic/data checks
until the manifest is regenerated.

To evaluate, supply a JSON list of 242 integers:

~~~sh
python3 -B direct/evaluate.py point.json
~~~

Add --companion and provide 241 integers for the dense companion. This
is an exact evaluator, not a root search.

## Source and verification boundary

The comparison snapshot is ProveIt commit
**3ecd6a6cf53d47519228328567f45fb7ee9781d9**. Eight incoming archives were
surveyed; the precise inherited components come principally from the
Common Remainders, Centered Residues, and Residual Bases submissions.
Their source hashes and roles are recorded in the ledgers.

The new unbounded proofs are in the report and mathematical review notes.
The inherited calibration interfaces are
**KEndpoint.c222_iff_zf_refutation** and
**ConstructibleChoice.zf_refutation_iff_zfc_refutation**. Their full
transitive proof-assistant closure was not rebuilt in this task.

Finite regression tests do not prove statements for all integers.
Conversely, the explicit arithmetic proofs are not replaced by empirical
testing. The archive preserves that distinction.
