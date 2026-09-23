# Notations for Omnific Integers

The placed base manuscript 08, on exact holonomic towers and the complexity
of equality, is [article.tex](article.tex). Placement `a4dcb91` also assigns
manuscript 05 on hereditary shielding and 09 on rational omega notations
here. Those companions are not yet integrated. No maintained PDF is
supplied yet; proof review and formalization remain pending.

The preserved [base provenance](08-holonomic-towers-PROVENANCE.md) and
[source 09 claims](09-rational-omega-CLAIMS.md) concern the delivered
packages. Supplements under `code/` and `data/` carry source prefixes
`05-hereditary-shielding-`, `08-holonomic-towers-` and `09-rational-omega-`.

The principal results are:

- **Theorems 6.2, 7.2, 7.4, and 9.2:** effective holonomic fraction towers;
  their triangular omnific-integer parts; exact floor and truncation; and a
  decidable ordinal-labelled union with ordinal trace exactly the ordinals
  below epsilon-zero.
- **Theorems 11.2 and 11.4:** co-c.e.-complete equality for raw
  primitive-recursive positive-block names, even on a one-monomial family;
  no uniform translation of those raw names into an equality-decidable
  representation, although all their values already have rational names.
- **Theorem 12.2:** positivity in d raw dominance blocks is many-one complete
  for the d-c.e. sets. The hardness uses at most d nonzero monomials.
- **Theorem 13.3:** semantic support validity is Pi^1_1-complete even with
  coefficient one and exponents in one fixed computable dyadic subset of
  (1,2). Checked equality and equality under a validity promise differ.

These are proved as mathematical theorems under the explicit representation
contracts in the article. Their standard ingredients, repository precedents,
and proposed original combined formulations are separated in Section 15.
No claim of exhaustive priority verification, peer review, or Lean
formalization is made.

## Build the PDF

Build `article.tex` with three passes of
`pdflatex -interaction=nonstopmode -halt-on-error article.tex`, or use
`latexmk -pdf article.tex`. No external figures or bibliography are needed.
Delivery build claims refer to the original source package.

## Run the finite prototype

The base prototype uses Python 3.10 or later and SymPy, with the version
specified in `data/08-holonomic-towers-requirements.txt`. The delivered
script imports `holonomic` and `ordinals` by their original names, so
reconstruct that small layout in scratch space before running it:

```sh
check_dir=$(mktemp -d)
mkdir -p "$check_dir/code" "$check_dir/data"
for module in holonomic ordinals verify demo; do
  cp "code/08-holonomic-towers-$module.py" "$check_dir/code/$module.py"
done
python "$check_dir/code/verify.py"
```

The suite writes its report under the scratch `data/` directory. The
delivered report is `data/08-holonomic-towers-verification.json`; it records
41 finite test groups. The companion Makefiles also retain original names
and do not directly build this renamed repository layout.

### What the prototype does not implement

It is not a general surreal computer algebra system. It does not implement
arbitrary exact real coefficient backends, operators over higher-rank
coefficient fields, the entire R_2 ring, the general tower floor or
recognition procedures, or all finite-label field embeddings. These are
mathematical algorithms in the article, not software capabilities claimed
for the delivered code.

Tests of infinite-series identities use generated differential certificates
and the proven finite-jet rule, not merely matching a fixed number of terms.
Nevertheless, the code is not formally verified. Finite test cases do not
prove the mathematical impossibility or completeness results.

The Python constructors accept trusted Python/SymPy objects and are not a
hardened parser for untrusted serialized input. They reject malformed
mathematical data in the documented interface, but callers can still mutate
Python objects; this package is not a security boundary.
