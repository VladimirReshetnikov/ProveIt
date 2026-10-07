# Source audit and novelty boundary

Inspection date: 7 October 2026.

## Established repository heads

- `openai/math`: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
- `VladimirReshetnikov/ProveIt`: `a41aa448d67395387593f1931cda142836afccdc`.

Both were returned by the GitHub `git/ref/heads/main` endpoint. The source
manifest gives URLs and explicitly distinguishes pinned reads from earlier
moving-branch reads. This was a targeted review, not an audit of every
manuscript, proof, or prior research companion.

## OpenAI mathematics collection

The repository overview/catalogue was consulted to choose a topic. The
relevant entry describes a claimed Sidorenko/forcing counterexample. This
report does not accept all catalogue claims as independently verified facts.

The complete finite-complex section of the Sidorenko manuscript was read,
including at the explicit commit above:

`preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/build/sections/complex.tex`

Blob: `178b0e9da21867a727ea847dae8e537b9d719a70`.

The 22 triples, 13 points, and 66 incidences are used. We independently
recomputed pair multiplicities, connectedness, point degrees, the point-graph
triangles, and short-cycle counts from those data. The coloring, exposure,
transversality, and singular-tail arguments were not audited as part of this
paper. The source's full theorem is not an input to any new proof.

The leading portion of `build/sections/kernel.tex` was read from the main
branch. Blob: `bbe11be8fffe968012060ec43e6aff597e922831`.
It describes rank-layer kernels on symmetric finite-field matrices and a
typed activation construction with potentially nonuniform type measures.
The full rank-layer proof and all later coefficient estimates were not
verified. We did not establish a scalar Cayley representation of that kernel.
The new typed theorem is only a sufficient criterion with explicit extra
hypotheses; it has not been applied to certify the source kernel.

## ProveIt

The Fourier/uniformity portion of the following file was read at the pinned
ProveIt head:

`Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean`

It defines the unnormalized DFT, correlation, iterated differences, cube
forms, and related language. The manuscript's normalized Fourier and U2
conventions are stated explicitly rather than silently reusing those names.
No claim was made that an inspected definition itself proves a theorem.

The following source audit was also read from the moving branch:

`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/30-fixed-radius-bohr-SOURCE_AUDIT.md`

Blob: `ea818e377eaf18b512c40e0081674ed78e5197ad`.

It discusses source normalizations and distinguishes statement catalogues
from formal proof status. Its own older pin is not substituted for the
current ProveIt head. Its local Bohr estimates are context, not premises
of the present proofs. The entire existing local-refinements corpus was
not exhaustively compared for overlap.

## Primary external literature

- Yuqi Zhao, *Sidorenko-Type Inequalities for Even Subdivisions over Finite
  Abelian Groups*, arXiv:2507.15723v1 (21 July 2025).
  https://arxiv.org/html/2507.15723v1
  The Fourier/subdivision argument and the concluding forcing discussion
  were inspected. The underlying even-subdivision positivity is treated
  as an established baseline, not claimed as a new theorem here. Our
  vertex-orthogonality proof does not require arbitrary integer-matrix
  rank claims over finite groups. The paper separately handles forests,
  nonprincipal characters, and adjacency normalization.
- David Conlon, Joonkyung Lee, and Leo Versteegen, *Around the positive
  graph conjecture*, arXiv:2404.17467 (2024).
  https://arxiv.org/abs/2404.17467
  The abstract was consulted for the broader positivity context, not as
  an imported theorem or an exhaustive comparison of all its arguments.

No third-party paper or font file is bundled.

## What is and is not claimed as a contribution

Written proofs are supplied for the local sign-threshold equivalence, the
binary relation-code formulation and finite cutoffs, the local-moment
negative-mass bound, the complete cycle-inventory inequality, sharp
weighted scalar forcing, blockwise certification, the concrete incidence
application, and the sufficient typed sign-gauge criterion.

The familiar Fourier expansion, cycle-space reasoning, binary linear
algebra, character-extension fact, and even-subdivision positivity are not
claimed inventions. The candidate contributions are their precise combined
refinements and the explicit quantitative incidence application. A limited
literature review does not establish that every formulation is globally
new. Independent expert review and a wider priority search are still needed.

No unrestricted Sidorenko theorem or counterexample, general quantitative
Szemerédi improvement, verification of all repository headline claims,
independent peer review, or Lean-kernel certification is asserted.
