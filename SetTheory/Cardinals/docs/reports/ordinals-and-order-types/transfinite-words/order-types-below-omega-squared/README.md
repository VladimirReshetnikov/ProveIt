# Guarded periodic blocks and exact maximal order types below omega squared

Research report prepared with ChatGPT for Vladimir Reshetnikov, September 19, 2026.

**Provenance.** This report merges two independently produced research reports on
the same question, `order-types-below-omega-squared` and `guarded-periodic-blocks`.
Both reached the same formula by the same core mechanism, and that shared core is
proved exactly once here. The two reports diverged at one step, the passage from
the Cartesian-power embeddings to the ordinal lower bound, and **both proofs are
kept**: the classical natural-product route in the main line, and an elementary
hand-built linear extension as a clearly marked alternative. Two different
justifications of the monotone-surjection principle are likewise both recorded.

## Main result

Let P be a finite poset, n its cardinality, and j(P) the number of its downsets,
**including the empty downset**. The article presents a complete proposed proof
that

    o(s^F_{omega^2}(P)) = 1                           for n = 0,
                        = omega^2                     for n = 1,
                        = omega^(omega^(n + j(P) - 2)) for n >= 2.

Words have ordinal length **strictly less than omega^2**. Their embedding is a
strictly increasing map of positions that may weakly increase labels in P.
Mutual embeddability is quotiented out. Finite image is automatic here. The
displayed n >= 2 formula must **not** be applied to the two exceptions.

The binary antichain value omega^(omega^4) addresses the sharpness question in
Harry Altman's *Bounding finite-image sequences of length omega^k*,
arXiv:2409.03199v2, Example 3.15, printed page 10. The binary chain value is
omega^(omega^3).

## What the article establishes

- The finite-poset formula above, for every finite poset alphabet.
- A classification of arbitrary selected families of periodic tail types,
  including the essential exceptional family in which only the universal block
  is allowed and the type drops to H_n * omega.
- A unified guarded product theorem covering both guard cases in one statement,
  plus a one-page quick reference for the whole construction.
- **Two preserved proofs of the amplification step.** The main line imports the
  de Jongh-Parikh natural-product theorem. The alternative route proves
  o(X^r) >= o(X)^r by hand, ordering r-tuples on their last unequal coordinate
  and using only ordinary ordinal exponentiation. What it buys: with that route
  the main theorem needs no product-theorem import at all.
- **Two preserved proofs of the monotone-surjection principle**, one by
  injecting the target bad-sequence tree into the source tree, one by ordering
  the fibres along a maximal linear extension of the target.
- Exact maximal order types of the individual length strata, in closed Cantor
  normal form, and the resulting warning that the supremum over lengths is
  omega^(omega^n), strictly below the answer. The main theorem therefore cannot
  be obtained stratum by stratum.
- Canonical finite representatives: a stack-based normalization under which two
  token expressions are mutually embeddable exactly when they are identical.
- An exact linear-time symbolic embedding algorithm with its correctness proof
  and its full four-case matching table.
- Worked negative controls for three invalid shortcuts: omitting the guards,
  using a finite guard at the universal block, and inserting a downset after one
  that contains it. Each is also executed in the test suite as a required
  failure.

**Status:** proposed solution; unrefereed, not peer reviewed, and not verified in
a proof assistant. The proof is complete relative to the explicitly cited
classical finite-word and maximal-order-type theorems. The specific unresolved
question was checked in the cited source; the claim of a solution rests on the
argument given here and not on a claim of exhaustive literature coverage. The
computation supports embedding lemmas, not the infinite ordinal-rank conclusion.

## Contents

- `article.pdf`: complete mathematical article.
- `article.tex`: editable LaTeX source, with its bibliography included.
- `references.bib`: bibliographic records for reuse.
- `build.sh`: three-pass `pdflatex` build script.
- `code/omega2.py`: exact symbolic embedding library, normalization, guard maps,
  and product-map constructors.
- `code/verify.py`: deterministic, exhaustive, and seeded-random verification
  suite, including the negative controls.
- `data/verification.json`, `data/verification.txt`: executed test report.
- `data/test_summary.tex`: test-count macros, with fallback values in the article.
- `data/examples.csv`: computed finite-poset examples.
- `data/finite_posets.csv`: the 50 naturally labelled posets of sizes one through
  four, individually, with predecessor and successor masks, downset counts, and
  the exponent predicted by the main formula. The n = 1 row carries the literal
  entry `exception: omega^2`.
- `data/ideal_counts.csv`: downset-count distribution for naturally labelled
  posets of size at most five.
- `notes/proof_audit.md`: hypotheses, the four critical boundaries, the two
  preserved alternative arguments, and known false shortcuts.
- `notes/literature_audit.md`: source/version, related work, merge provenance,
  and literature-search scope.

## Reproduction

Requirements for code: Python 3.10+; standard library only.

From this directory:

```sh
python3 code/verify.py
python3 code/omega2.py
```

The supplied run passed **3,240,040 assertions** with seed 20260919. This is a
single combined run, not the sum of two separately reported runs. Of those
assertions, 1,625,127 compare product maps against componentwise embeddings and
774,149 compare the two decision procedures; 726,242 of the latter come from the
exhaustive two-letter domain, in which every ordered pair of token expressions of
length at most four is tested (781 expressions for the antichain, 341 for the
chain). There are 355 marker stages across small posets and 14 activation stages
across all binary support subfamilies. Three negative controls are required to
fail and do.

`code/verify.py` accepts options:

```sh
python3 code/verify.py --seed 17 --samples 1000 --pair-bound 4 --output-dir rerun
```

The defaults are `20260919`, `250`, `4`, and `data/`. Raising `--pair-bound`
enlarges the exhaustive binary enumeration very quickly. Running the suite with
the default output directory overwrites the generated data files; wall-clock
timing and Python-version fields will naturally depend on the environment.

To rebuild the article with a sufficiently complete TeX Live or MiKTeX
distribution:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `sh build.sh`, or `pdflatex article.tex` until references
stabilize. No BibTeX run is required. New PX, AMS packages, geometry, microtype,
tcolorbox, listings, booktabs, enumitem, and hyperref are used. Fonts are not
separately distributed.

## Library use

Put `code/` on the import path, or start Python from that directory:

```python
from omega2 import FinitePoset, letter, omega, embeds, normalize, theorem_value

P = FinitePoset.antichain(2)
a = letter(0)
A = omega(1)  # downset bitmask 01: {0}
U = omega(3)  # downset bitmask 11: {0,1}
assert embeds(P, (a, U), (U,))
assert not embeds(P, (A, A), (U,))
assert normalize((a, U)) == (U,)      # the canonical representative
print(theorem_value(P))  # omega^(omega^4)
```

`embeds` treats periodic omega tails exactly. It does **not** expand them into
long finite words. `embeds_reference` independently explores all symbolic
endpoint choices but shares the same mathematically proved tail semantics.

`normalize` implements the stack-based canonical form: two normalized
expressions are mutually embeddable exactly when they are equal.

`proper_marker_map` and `full_marker_map` construct the maps used in the main
text, which leave the final component unguarded; the caller must satisfy the
family-level preconditions stated in the article and their docstrings.
`guard` and `encode_product` implement the unified all-guarded variant and do
check the family-level precondition that no old downset contains the new one.

`FinitePoset.maximal_elements` returns the generators of a downset. The periodic
block repeating only those is equivalent to the block repeating all of the
downset; the all-elements block is the convention used throughout the code.

`naturally_labelled_posets` includes every isomorphism class but generally
includes several representatives of a class. It is not an enumeration of all
possible labelings and is not isomorphism-free. Its counts must not be
interpreted as unlabeled-poset counts.

No third-party paper PDFs, font files, checksum files, or build intermediates
are included.
