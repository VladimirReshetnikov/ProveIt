# Prescribed coefficient-lattice minima

**Main result.** For every finite nondecreasing list `2 <= h1 <= ... <= hr`,
`A = {0, 1, h1, h1*h2, ..., h1*...*hr}` has coefficient-lattice successive
L1-minima exactly `(2*h1, ..., 2*hr)`. There are exactly `r+2` distinct elements.
More generally the radices may be in any order: the minimum list is twice their
sorted list.

The target is the unnumbered full-list realization conjecture after Lemma 1,
Section 1.1, page 2, in Kevin O'Bryant, *On Nathanson's Triangular Number
Phenomenon*, arXiv:2506.20836v2. Its printed endpoint `h1=1` is impossible for
distinct integers; the article proves this obstruction and gives a full
constructive affirmative answer on the admissible domain `h1>=2`.

Read `article.pdf` for the complete proofs. This is an AI-assisted draft,
not independently refereed or checked in a proof assistant. No later solution
was located in the recorded search, but this is not a guarantee of priority.

## Main additional results

The carry vectors are an integral basis. Every relation of degree <= H has
zero carry coordinates at radices > H, giving the exact subgroup filtration.
All successive minimizing bases are the signed carries, permuted only among
equal radices. Unique digit normal forms give every iterated sumset and the
rational generating function

    sum_{h>=0} |hA| z^h = product_j(1+z+...+z^(hj-1)) / (1-z)^2.

If `P=product(hj)` and `D=sum(hj-1)`, then `|hA|=P*(h+1)-P*D/2` begins
permanently at `h=D-1` for nonempty radix lists. A separate proof gives a
complete-intersection presentation of the associated binomial ideal.

## Reproduce

Python 3.10 or later, standard library only (tested with Python 3.13.5):

```sh
python3 code/verify.py
python3 code/select_area.py
```

The first command regenerates the finite-check outputs. The second only
shows the recorded original random selection and **does not redraw**.

To compile the PDF:

```sh
latexmk -pdf article.tex
```

Alternatively run `pdflatex article.tex` twice. The `data/areas.tex` file
must remain alongside the article source in the indicated directory.

## Example API use

```python
import sys
sys.path.insert(0, "code")
from mixed_radix import construct, carry_basis, sumset_size
from mixed_radix import canonical_representation

q = (2, 3, 5)
assert construct(q) == (0, 1, 2, 6, 30)
assert sumset_size(q, 6) == 105
assert canonical_representation(q, 4, 35) == (0, 1, 2, 0, 1)
print(carry_basis(q))
```

The function `eventual_size` evaluates the eventual affine polynomial; below
its stated onset that polynomial need not equal the actual sumset size.
Use `sumset_size` for every nonnegative index. The function `short_vectors`
is an exact ball enumerator based on the proved coefficient bounds, not an
independent proof of those bounds.

## Files

- `article.tex`, `article.pdf`: source and 16-page article.
- `code/mixed_radix.py`: exact construction, lattice, normal-form, and counting tools.
- `code/verify.py`: independent multiset-collision ranks and explicit sumset checks.
- `code/select_area.py`: original 96-area catalogue; preserved-draw viewer and
  an explicit new-file-only option for unrelated future draws.
- `data/area_selection.json`: actual single original draw, including the full catalogue.
- `data/verification_summary.json`: exact test totals and PASS status.
- `data/rank_checks.csv`: all 754 ordered-profile rank checks.
- `data/examples.json`: representative witnesses, bases, rank profiles, and sumset sizes.
- `data/vector_ball_checks.json`: exhaustive all-pair checks of five complete balls.
- `data/equal_minima_different_sumsets.json`: a warning against an invalid generalization.
- `notes/sources.md`, `notes/proof_audit.md`, `notes/exclusion_audit.md`: source,
  logical, and exclusion audits.
- `STATUS.md`: exact scope and remaining validation/priority limits.

Ordered and arbitrary-order test collections overlap intentionally. Finite tests
are not the all-parameter proof. No source-paper PDFs or font files are included.
