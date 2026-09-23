# The First-kappa Coefficients
## Omitted Types, Singular Compression, and Completion in Surreal and Surcomplex Hahn Fields

Research manuscript prepared for Vladimir Reshetnikov, dated 22 September 2026.

## Files

- `article.tex`: complete, self-contained LaTeX source with an internal bibliography.
- `article.pdf`: compiled article.
- `research_audit.md`: source-inspection boundary, novelty qualifications, and proof-risk review.
- `verify.py`: reproducible finite checks using exact rational arithmetic.
- `verification.json`: the delivered run's actual counts and scope.
- `build.sh`: rebuilds the PDF and reruns the finite checks.
- `build_audit.json`: delivered PDF's layout/log checks, separate from mathematical testing.

## Mathematical content

For an uncountable cardinal kappa, a nonzero divisible ordered abelian group
Gamma, and real or complex coefficients, let K consist of the Hahn series
with fewer than kappa nonzero terms, inside the full Hahn field F.

The paper gives the exact approximation-value cut of a missing series and
classifies its ordered real or valued complex one-type by its first kappa
nonzero terms. It computes the least size of a subfamily of that type which
is omitted in K: cf(kappa), including at singular cardinals. In the pure
complex field language the analogous number is |K|, and all missing elements
have the same one-type.

For proper K, the first empty nests of closed valuation balls have size
cf(kappa), whereas K is valuation-complete exactly when cf(Gamma) differs
from cf(kappa). The completion has an explicit locally small support
condition. A further theorem calculates every possible valuation-loss bound
for a linear retraction from K+Kx to K and gives a zero-or-two-dimensional
continuous-dual dichotomy.

Explicit examples include kappa=aleph_omega and the surreal normal form
sum_{alpha<kappa} omega^(-omega^alpha). A regular-cardinal example separates
sequential completeness from completeness. Another example gives a strict
chain K < completion(K) < F.

## Proof and novelty status

The article supplies written proofs, with standard Hahn-field closedness,
Conway normal-form arithmetic, and classical quantifier elimination explicitly
identified as inputs. General approximation-type theory and the construction
of cardinally bounded Hahn fields are not claimed as new.

The joint first-kappa classification, exact omission calculation, and linked
completion/linear consequences are proposed contributions. The reviewed
material did not identify this whole package, but the priority search was
limited. This is not a claim to settle a named longstanding conjecture, not
an exhaustive repository audit, and not a Lean-certified development.

All topology is intrinsic to the chosen set-sized Hahn workspace. It is not
the subspace topology induced from the full proper class of surreal numbers.
All support bounds are cardinality bounds, not order bounds on exponents.

## Rebuilding

Run `bash build.sh` in this directory with Python 3.10 or later and a standard
TeX Live installation providing pdfLaTeX, newtx, amsthm, mathtools, microtype,
geometry, enumitem, booktabs, fancyhdr, hyperref, cleveref, bookmark, and xurl.
The source does not require shell escape, BibTeX, network access, or external
figures. The bibliography is inside `article.tex`.

The finite check script uses only Python's standard library. Its 9,622 passing
assertions test local finite algebraic identities; they do not prove any
transfinite, cardinal, model-theoretic, or publication-priority claim.
