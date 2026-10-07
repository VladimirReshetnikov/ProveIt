# Targeted source audit

Inspection date: 6 October 2026.

## Pinned statement comparison

Repository: `VladimirReshetnikov/ProveIt`.

Pin established by reading `git/ref/heads/main`:

    8d65d3c9febe4d0e9efe945e11b53af5f19d1435

Paths below are relative to
`Combinatorics/Ramsey/Lean/GowersSzemeredi/`.

| Source | Blob | Relevant inspected content |
|---|---|---|
| `Definitions.lean` | `97113b7afa6925a2dd4b76641eeaeff09597ab6a` | Pinned reads of lines 170–285 and 280–307. `centeredAbs` and `bohr`, especially lines 280–286. |
| `Section10.lean` | `302e8a223f56dcdabf29f30ca3c80ac62a7adbfc` | Pinned read of lines 350–405. An earlier moving-branch read of lines 350–570 returned the same blob. `InducesDifferenceMap`, Lemma 10.10, Corollary 10.11, Lemma 10.12, and Theorem 10.13's parameter interface. |

Pinned source URLs:

https://github.com/VladimirReshetnikov/ProveIt/blob/8d65d3c9febe4d0e9efe945e11b53af5f19d1435/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean

https://github.com/VladimirReshetnikov/ProveIt/blob/8d65d3c9febe4d0e9efe945e11b53af5f19d1435/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean

Key comparison facts:

1. The angular convention is `centeredAbs (r*d) <= delta*N`.
2. The old Lemma 10.10 coefficient is `2^(k+1) delta^(-k) k zeta`.
3. Corrected Corollary 10.11 uses division by k:
   `zeta = 2^(-(k+4)) delta^k / k`.
4. Lemma 10.12 uses `sqrt theta < 5/16` and explicitly requires relevant
   target fibres to be nonempty. The manuscript's `5/14` comparison is under
   the fully stated nonnegative-error and finite-fibre hypotheses.
5. Theorem 10.13 records other corrections, including the integer ceiling for
   its spectrum parameter and a corrected density conclusion. This package
   does not assert a stronger full Theorem 10.13 or change those corrections.

No fresh build of the repository was run. This audit does not report the
current count of formalized lemmas or the current status of each companion.
The inspected `Section10.lean` is a proposition-valued statement catalogue;
its contents alone do not establish that any proposition is kernel proved.

## Existing research context: moving-branch reads, not the pin above

Inspected:

`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md`

Blob `85f58734e6c8951dc5b5b4f81c5787449b48119a`, lines 1–230 and 400–650.
The recursive research listing and the following integration note were also read:

`07-transport-rigidity-FORMALIZATION.md`

Blob `93a9369c1171b77c725520354157202c9fa409f4`.

These sources document prior local work on density transfer, phase partitions,
energies, restriction, cube expansions, floor patterns, and transport rigidity.
They motivated selecting fixed-radius Bohr boundary estimates rather than
repeating those headline topics. The full combined article and all pending
source manuscripts were NOT exhaustively compared. No exhaustive absence or
priority claim follows from this audit.

## Published primary sources

W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.

https://www.cs.umd.edu/~gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf

The public PDF was read as parsed text and inspected as page images, including
printed pages 529–530 (PDF indices 64–65). The printed Corollary 10.11 has a
factor k where the corrected repository uses division by k. Comparisons in the
article use the corrected version. No source PDF is redistributed.

Ben Green, *A Szemerédi-type regularity lemma in abelian groups, with applications*,
arXiv:math/0310476v2 (21 October 2004).

https://arxiv.org/abs/math/0310476
https://arxiv.org/pdf/math/0310476

Sections 3–4 discuss fixed-radius boundary difficulties, Bourgain's
regular-radius approach, smoothing, and finite Bohr enlargement estimates.
They supply background and attribution, not an external premise needed for
any main theorem of this article.

The literature search was targeted. It does not establish that the escape-tube
bound or every auxiliary consequence is absent from the wider literature.
