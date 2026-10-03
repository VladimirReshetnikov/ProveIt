# Source audit and research status

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned revision: `109aaca1505c12d70ae169bdc2011f40bd476f7d`

The repository was accessed read-only. No changes or repository-wide build were made.

### Inspected report guide

`Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md`

The guide identifies the merged report's constituent manuscripts, its unrefereed and
unformalized status, its scope, and the locations of existing results. Its full 116-page
merged article was not independently re-audited theorem by theorem for this project.
Existing results are attributed as predecessor work; relevant elementary mechanisms
are reproved when used in the new development.

### Inspected Lean source

`Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean`

Git blob: `3bf0fb22cb5a5c50b05360fd8e5dbeafb104e959`

This file was read. Actual declarations include:

- `isPrefix_of_minimum_birthday`
- `existsUnique_prefix_of_ordConnected`
- `existsUnique_minimum_birthday_of_ordConnected`
- `ordConnected_separators`
- `existsUnique_simplest_separator`

The last theorem assumes the existence of a separator. It is not, by itself, an
unrestricted cut-realization theorem. The inspected signature also exposes the
universe distinction in `SmallCutData.{u, u + 1}`. No newly proposed module names
in the article are represented as existing or compiled declarations.

## Available predecessor manuscripts consulted

The prior Library drafts were used to identify already-developed results and avoid
presenting them again as the main advance:

1. `surreal_well_orders_II.tex`: *Exact cut spectra, branch recognition, optimal support
   reserves, and automorphism-extension obstructions*. Its explicit question concerning
   complete metrizability when the relevant cofinality is countable motivated the new
   countable result. The uncountable singular case remains separate.
2. `Surreal_Well_Orders_Further_Study.tex`: *Cut reconstruction, asymmetric products,
   prefix non-rigidity, and size-safe foundations*.
3. The continuation *Cut classification, support thresholds, and class-model absoluteness*.

These are research drafts dated 3 October 2026, not asserted to be refereed publications
or to have been incorporated into the pinned repository.

## Public primary sources

- Kanovei–Shelah: https://shelah.logic.at/papers/825/ and
  https://arxiv.org/abs/math/0311165
- Friedman–Hyttinen–Kulikov: https://arxiv.org/abs/1207.4311
- Gitman–Hamkins: https://arxiv.org/abs/1509.01099
- Ehrlich: https://doi.org/10.2178/bsl/1327328438

The Kanovei–Shelah indexing construction was checked rather than being identified
with all well-orders of the reals. Its range-ultrafilter functions need not be injective.
The generalized-descriptive-set-theory source supplies context for bounded topology.
The class-game source verifies that unrestricted elementary class recursion must not
be silently assumed in GBC. These sources are not being cited as proofs of this
article's new propositions.

## What was verified locally

- The standard-library finite regression script ran and returned PASS.
- The LaTeX article compiled with resolved cross-references and no overfull boxes.
- The PDF was rendered and inspected, including contact sheets of every page and
  full-size samples of the title, main theorem, formalization section, and appendices.
- PDF text-block bounds were checked for page-edge spill.

These are document and finite-mechanism checks, not transfinite proof verification.
No claim of historical priority, peer review, or Lean kernel certification is made.
