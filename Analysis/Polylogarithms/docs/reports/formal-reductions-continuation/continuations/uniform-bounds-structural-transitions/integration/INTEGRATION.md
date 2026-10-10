# Proposed integration into ProveIt

Baseline: **3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f**.
The source repository has not been changed.

## Preferred first integration

Place this package, preserving its internal paths, under a new
report directory such as:

~~~text
Analysis/Polylogarithms/docs/reports/uniform-bounds-structural-transitions/
~~~

The standalone article compiles there without depending on the
manuscript's preamble. This preserves a reviewable research record
while the individual results are integrated into the book.

## Chapter map

| Package section | Manuscript destination | Integration decision |
|---|---|---|
| sections/euler.tex: kernel and uniform enclosure | chapters/05-real-euler.tex and 05-subcritical-stieltjes.tex | Add the two-measure representation and kernel lemma before the global error corollary. Retain sharper restricted-domain bounds. |
| sections/euler.tex: moment theorem and positive gamma series | Real-order computation / Euler continuation | Add as reusable general results with definitions of sigma_s and J_N. |
| sections/euler.tex: moving-order phase, C_N limit, and lower rate | End of Euler error section or a new asymptotic subsection | Keep the distinction between the all-index constant C* and the limit of the index-specific constant C_N. |
| sections/depth.tex | chapters/04-depth.tex or a new formal-depth subsection | Retain the full binary relation space, formal-versus-analytic distinction, and Nielsen literature attribution. |
| sections/radial.tex | After chapters/05-real-turning.tex | Preserve the prior existence argument, then add exact isolation, the sixth coefficient, the fold, and the explicit two-extremum example. |
| sections/reflection.tex and sections/proportional.tex | After chapters/07-reflected-moments.tex / 07-sharp-moments.tex | Keep the growing coefficient and growing remainder ranges separate. |
| sections/audit.tex | Editorial ledger and verification notes | Apply the scoped wording correction; record the new proof statuses. |
| sections/research.tex | Research agenda / discovery ledger | Replace closed questions with the remaining global or effective versions. |

The new article cites the pinned manuscript for already established
facts, including the unique Gaussian axis maximum and angular-zero
uniqueness. On book integration, convert these citations to the
book's existing theorem references.

## Wording patch

**non_elementarity_wording.patch** changes only the prose surrounding
the vertical trilogarithm formulas in chapters/03-algebraic.tex.
It scopes “does not close” to the calculation at hand and replaces
the unsupported non-elementarity claim with a statement about the
representation actually proved. The displayed formulas are unchanged.

The patch was constructed against, and checked for applicability to,
the pinned baseline. To review it from the repository root:

~~~bash
git apply --check /path/to/non_elementarity_wording.patch
git apply --stat /path/to/non_elementarity_wording.patch
~~~

Both commands are read-only. No patch was applied in preparing
this package.

## Proof-status changes

1. **Closed:** a finite Euler error constant uniform over all
   positive orders. The sharp all-index constant is C*, and 57/50
   is an exact certified rational budget.
2. **Closed:** the missing inference from the axis magnitude
   maximum to a bound for every Euler remainder. The new kernel
   comparison is the required argument; it does not follow from
   monotonicity of the scaled remainders.
3. **New proved refinement:** the positive gamma-series remainder
   identity, the logarithmically growing-order phase law, and
   the asymptotic optimal global constant C_N → 1, with an explicit
   lower asymptotic for C_N−1. The matching upper rate is conjectural.
4. **Closed locally:** exact isolation and sixth-order behavior
   at the previously diagnostic quartic transition. Global
   uniqueness on 0<b<1 remains open.
5. **New proved example:** a rational parameter pair with exactly
   two small-radius extrema of the actual normalized angular zero.
6. **Extended:** fixed-reflected-exponent coefficient asymptotics
   and half-term estimates to their stated growing ranges.
   A further small proportional coefficient range is proved.
7. **Attribution update:** the concrete height-one weight-seven
   relation is Charlton–Gangl–Radchenko Proposition 28, not an
   original relation of this package. The full-binary rank formula
   and explicit verification artifacts have their own stated scope.
8. **Unchanged:** S6 and the revised S8 evaluations, global radial
   classification, and numerical period-independence questions.

## Label and notation requirements

The standalone preamble defines theorem, lemma, proposition,
corollary, conjecture, definition, remark, and example environments.
Its few convenience macros are all visible in article.tex.

The section label families are:

| Topic | Prefix |
|---|---|
| Euler bounds | sec:euler, thm:Euler-uniform, thm:kernel, eq:Euler-*, thm:euler-*, prop:gamma-* |
| Full binary depth | gorbit: |
| Radial geometry | rd: |
| Reflected asymptotics | moderate: |

The Euler section contains some shorter generic labels; prefix them
consistently during a direct chapter merge if they collide with the
book. The report can be kept unchanged and cited first.

The symbol rho has two separate local uses: disk radius in the radial
section, and inverse-gamma singularity radius in the reflected section.
Each section explicitly introduces its own notation. The scalar b in
the reflected constants is also local and is unrelated to the inner
polylogarithm order. If merging closely adjacent material, renaming
these local constants may improve readability.

Keep the standard normal CDF notation Phi_G distinct from the radial
function Phi(t). Keep the Dirichlet eta function distinct from the
normalized radial eta; both are already context-specific in the
manuscript.

## Certificates and their dependencies

The four exact verifiers use only the Python standard library. Keep
certify_two_extrema.py and certify_radial_degeneracy.py in the same
directory, or adjust the former's import explicitly. The scripts
resolve their certificate output paths relative to the report root.

The depth verifier writes its two companion files in the directory
containing the requested output JSON. The optional weight-seven
numerical script reads the product correction from data/ and imports
the shuffle expansion routine from the adjacent verifier.

The exact radial certificate establishes the function's implicit
root strip and derivative tails. Do not replace it by the plotting
script, by a truncated Taylor polynomial, or by a list of decimal
roots. The figure is explanatory.

The numerical reflection data record a small number of independent
Cauchy comparisons and precision repetitions. They do not certify a
finite threshold for the uniform big-O theorems or a numerical lower
bound for the small proportional constant c0.

## Suggested editorial sequence

First integrate the two-measure Euler theorem and its exact budget,
then the radial certificate and explicit example. These directly
resolve active open statements and have compact dependency chains.
Next integrate the full-binary rank theorem with the literature
crosswalk. Finally add the reflected growing-parameter theorems,
including the shifted-saddle subsection, with their distinct ranges.

After any direct merge, replay the exact certificates and recompile
the manuscript. Check cross-references and equation numbering,
especially the signs in the Euler finite differences and the
factor -k relating reflected coefficients to meromorphic residues.
