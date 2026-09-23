# Definable Surreal Numbers and Omnific Integers

This directory contains base manuscript 04, placed in `a4dcb91` as
[article.tex](article.tex). Companion 07, on the initial core, is assigned
here but not yet integrated. A maintained PDF is not supplied yet. The base
text has 36 standard statements; this counts cited results as well as the
source's proposed contributions. Proof review and Lean coverage are pending.

The source manuscripts' delivered file names differ from this layout:

| Maintained path | Contents |
|---|---|
| [article.tex](article.tex) | Base 04, with its bibliography |
| [04-hod-transcendence-AUDIT.md](04-hod-transcendence-AUDIT.md) | Source 04's delivered proof and provenance boundaries |
| [07-initial-core-SOURCE_AND_PROOF_AUDIT.md](07-initial-core-SOURCE_AND_PROOF_AUDIT.md) | Companion 07's delivered audit |
| `code/04-hod-transcendence-verify_finite.py` | Base 04's finite regression suite |
| `code/07-initial-core-verify_finite.py` | Companion 07's finite suite |
| `data/04-hod-transcendence-verification_results.json` | Delivered base run |
| `data/07-initial-core-verification.json` | Delivered companion run |

## Main reading route

The ambient definitions are in Section 3. The definable field and integer
part theorem is Theorem 4.2 (page 7), and the HOD identification is Theorem
5.1 (page 9). The reversible fixed-leading-term omnific code is Theorem
6.2 (page 10); Proposition 6.5 supplies a complementary two-term code.
The universe and pointwise-definability tests are in Section 7.

The strongest proposed contribution is Theorem 8.3 (page 14), preceded by
the general support-subfield amplification theorem. With

    K = No intersect HOD = No^HOD,

if V is not HOD and 0 < t < 1 lies outside K, then

    z_alpha = omega + omega^(t * omega^(-(alpha+1)))

is an ordinal-indexed algebraically independent family over K. Every
z_alpha is an omnific integer strictly between omega and omega+sqrt(omega),
with zero constant term and exactly two normal-form terms of coefficient 1.
All powers of omega in this statement are Conway monomials, not general
exponential powers. The class-family assertion means finite polynomial
independence and provides no set-sized bound on the size of independent
subfamilies; it does not posit a proper-class sum or a transcendence basis.

Sections 9–13 treat uniform versus termwise definitions, the first
non-HOD birthday, bounded-complexity escape ordinals, forcing without
new reals, relative ordinal parameters, and canonical surcomplex pairs.

## Build and finite checks

From this directory, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` three times, or use `latexmk -pdf article.tex`. The delivered
build claims in the source audit concern the source's original package.

The base suite needs Python 3.10 or later and only the standard library:

```sh
python code/04-hod-transcendence-verify_finite.py --output /tmp/hod-finite-checks.json
```

It tests finite sign codes, rational normalization, formal infinitesimal
floors and support-coset examples. These checks neither compute HOD nor
prove the definability and transfinite claims. Keep rerun output separate
from the delivered files in `data/`. Companion 07's Makefile retains its
original names and does not build this maintained layout.

Both manuscripts are AI-assisted drafts, not refereed or formally verified.
The delivered audits record their own inspection scopes; placement does not
certify priority, the proofs, or equivalence between the two manuscripts.
