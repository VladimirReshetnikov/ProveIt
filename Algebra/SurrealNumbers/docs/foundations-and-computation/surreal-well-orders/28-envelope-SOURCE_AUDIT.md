# Source audit and proof status

## Repository snapshot

Repository: VladimirReshetnikov/ProveIt
Pinned revision: `7ff7736ecf3a0adc8536b2d083cf819e1ba39ace`

The GitHub connector was used to inspect the repository tree and retrieve known
files. The recursive tree was too large to inspect exhaustively. This was a
focused inspection, not a repository-wide audit.

Inspected files:

1. `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md`
   - Merged research report scope, provenance, and unformalized status.
   - Describes its 116-page merged article and scoped review history.
   - The complete merged article was not re-audited theorem by theorem.
2. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean`
   - Full source read.
   - Git blob: `3bf0fb22cb5a5c50b05360fd8e5dbeafb104e959`.
   - Includes minimum-birthday/prefix uniqueness and simplest cut separator
     theorems; the cut separator theorem explicitly assumes existence.

No repository edits, commits, or builds were performed.

## Prior user manuscripts

`Surreal_Lexicographic_Orders_Prefix_Completions.tex`, 3 October 2026:
substantial source ranges covering definitions, prefix and order topology,
forward completion, regular Baire models, singular continuity criteria,
the bounded subgroup, global prefix schemes, and further questions were read.
The normalizer and full singular complete-metrizability questions were checked
directly. The new article answers the former in the natural permutation action
and leaves the latter explicitly open within this report.

`Surreal_Well_Orders_Further_Study.tex`, 3 October 2026:
the available abstract and continuation context identify cut reconstruction,
asymmetric products, and prefix non-rigidity. The full manuscript was not
independently audited. Its structural context is attributed, not claimed new.

The prior drafts are not asserted to be journal publications or all merged into
the pinned repository.

## Primary external literature

The source bibliography records the checked primary sources:

- Kanovei--Shelah, *A definable nonstandard model of the reals* (2004),
  arXiv:math/0311165. The actual lexicographic index definition in its PDF
  allows repetitions and is not literally a space of well-order relations.
- Ehrlich, *The absolute arithmetic continuum and the unification of all
  numbers great and small* (2012), DOI 10.2178/bsl/1327328438.
- Friedman--Hyttinen--Kulikov, *Generalized Descriptive Set Theory and
  Classification Theory* (2014), arXiv:1207.4311.
- Dimonte--Motto Ros, *Generalized Descriptive Set Theory at Singular
  Cardinals of Countable Cofinality* (2025), arXiv:2511.16188.
- Gitman--Hamkins, *Open determinacy for class games*, arXiv:1509.01099v2.

These provide context or foundational distinctions. They are not cited as
having proved this manuscript's new subgroup or group-envelope results.

## Proof and validation boundaries

New assertions have detailed written mathematical proofs. No historical
priority claim is made and no new Lean kernel verification is asserted.
The finite test program checks composition conventions and finite combinatorial
mechanisms only. Its output names the excluded infinitary claims explicitly.
The final PDF was rendered for visual inspection; references and TeX overflow
warnings were checked during production.
