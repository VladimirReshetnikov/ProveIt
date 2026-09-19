# Exact maximal order types below omega squared

Research draft prepared with ChatGPT for Vladimir Reshetnikov, September 19, 2026.

## Main result

Let P be a finite poset, n its cardinality, and j(P) the number of its downsets,
**including the empty downset**. The article presents a complete proposed proof
that, for n >= 2,

    o(s^F_{omega^2}(P)) = omega^(omega^(n + j(P) - 2)).

Words have ordinal length **strictly less than omega^2**. Their embedding is a
strictly increasing map of positions that may weakly increase labels in P.
Mutual embeddability is quotiented out. Finite image is automatic here.

For the empty alphabet the answer is 1. For a singleton it is omega^2, not the
value obtained by substituting into the displayed n >= 2 formula.

The binary antichain value omega^(omega^4) addresses the sharpness question in
Harry Altman's *Bounding finite-image sequences of length omega^k*,
arXiv:2409.03199v2, Example 3.15, printed page 10. The binary chain value is
omega^(omega^3). The article also classifies arbitrary selected families of
periodic tail types, including the exceptional universal-only family.

**Status:** proposed solution; unrefereed and not proof-assistant verified.
The proof is complete relative to the explicitly cited classical finite-word
and Cartesian-product maximal-order-type theorems. The computation supports
embedding lemmas, not the infinite ordinal-rank conclusion.

## Contents

- `article.pdf`: complete mathematical article.
- `article.tex`: editable LaTeX source, with its bibliography included.
- `references.bib`: bibliographic records for reuse.
- `code/omega2.py`: exact symbolic embedding library and product-map constructors.
- `code/verify.py`: deterministic and seeded-random verification suite.
- `data/verification.json`, `data/verification.txt`: executed test report.
- `data/test_summary.tex`: test-count macros, with fallback values in the article.
- `data/examples.csv`: computed finite-poset examples.
- `data/ideal_counts.csv`: downset-count distribution for naturally labelled
  posets of size at most five.
- `notes/proof_audit.md`: hypotheses, critical steps, and known false shortcuts.
- `notes/literature_audit.md`: source/version and literature-search scope.

## Reproduction

Requirements for code: Python 3.10+; standard library only.

From this directory:

```sh
python3 code/verify.py
python3 code/omega2.py
```

The supplied run passed **1,710,857 assertions** with seed 20260919.
Of these, 1,580,460 compare the product maps against componentwise embeddings.
The two decision procedures agreed in 47,907 comparisons.
Running the suite overwrites the generated data files; wall-clock timing and
Python-version fields will naturally depend on the environment.

To rebuild the article with a sufficiently complete TeX Live distribution:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex article.tex` until references stabilize. No BibTeX
run is required. New PX, AMS packages, geometry, microtype, tcolorbox, listings,
booktabs, enumitem, and hyperref are used. Fonts are not separately distributed.

## Library use

Put `code/` on the import path, or start Python from that directory:

```python
from omega2 import FinitePoset, letter, omega, embeds, theorem_value

P = FinitePoset.antichain(2)
a = letter(0)
A = omega(1)  # downset bitmask 01: {0}
U = omega(3)  # downset bitmask 11: {0,1}
assert embeds(P, (a, U), (U,))
assert not embeds(P, (A, A), (U,))
print(theorem_value(P))  # omega^(omega^4)
```

`embeds` treats periodic omega tails exactly. It does **not** expand them into
long finite words. `embeds_reference` independently explores all symbolic
endpoint choices but shares the same mathematically proved tail semantics.

`proper_marker_map` and `full_marker_map` construct the maps in the proofs;
the caller must satisfy the family-level preconditions stated in the article
and their docstrings. They do not check all preconditions automatically.

`naturally_labelled_posets` includes every isomorphism class but generally
includes several representatives of a class. It is not an enumeration of all
possible labelings and is not isomorphism-free. Its counts must not be
interpreted as unlabeled-poset counts.

No third-party paper PDFs, font files, checksum files, or build intermediates
are included.
