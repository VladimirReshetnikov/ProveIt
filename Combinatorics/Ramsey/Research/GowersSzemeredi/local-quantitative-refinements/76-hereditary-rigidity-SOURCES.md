# Public source inventory and attribution for Report 288

Prepared 7 October 2026. The report is self-contained at the stated classical-algebra level. The mathematical article supplies its proofs; the companion performs finite exact diagnostics. No upstream program or Lean source is executed during reproduction.

## Exact authored-source inventory

The builder's literal allowlist contains these ten files:

1. `Report288.tex`: mathematical article
2. `README.md`: overview and entry points
3. `REPRODUCING.md`: reproduction contract and limits
4. `SOURCES.md`: this inventory and attribution
5. `build.py`: guarded builder and deterministic packager
6. `companion/__init__.py`: package initializer
7. `companion/README.md`: diagnostic inventory and bounded API
8. `companion/exact_checks.py`: exact standard-library diagnostic
9. `tests/test_companion.py`: mathematical and API regressions
10. `tests/test_build.py`: build and refusal regressions

A public distribution adds only `Report288.pdf` and `MANIFEST.sha256`. The manifest lists the eleven public files other than itself using sorted SHA-256 entries. The archive has exactly these twelve members, under `Report288/`. Private working notes, source audits, prior reports, raw Lean snapshots, original archives, build logs and release receipts are not public package members.

## Immediate report lineage

- Report 286, **Sparse Defects and Local Cover Obstructions**, 7 October 2026: earlier local-cover and repair-obstruction context
- Report 287, **Global Deletion Costs and Hereditary Energy Rigidity**, 7 October 2026: immediate finite-cyclic hereditary-energy predecessor; includes the arbitrary-abelian-target cyclic extension and the division-free even-cycle normal form
- Report 288, **Sharp Hereditary Energy Rigidity on Arbitrary Abelian Groups**: the arbitrary-domain theorem, finite-support quantifier distinction, conditional Jensen gap, and quantitative indicator and weighted witnesses

Reports 1–287 are separate, unchanged works and are not bundled. The Report288 builder adapts the guarded Report287 architecture with a new literal inventory, report identity, diagnostics and tests. Prior report contents are not needed as byte dependencies for replay.

## Source 56 and the relative statistic

Source 56 is **Nearly Sharp Relative Affine Repair on Fourier-Uniform Domains**, dated 6 October 2026. Its fixed-weight relative quadruple statistic is the statistic inside the hereditary infimum used here. The difference is the hypotheses and conclusion: Source 56 restricts the weights by Fourier-uniformity and small-error conditions and gives approximate affine repair; this report varies all finite indicators or weights and proves exact affinity from a uniform margin above 3/4.

Original archive, cited as historical source metadata rather than a build input:

https://github.com/VladimirReshetnikov/ProveIt/blob/aa1d86f6f5db46a5a4b6a99735587b31cbbafb54/docs/incoming/gowers_relative_affine_repair.zip

The introduction and four-query sampler subsection of the original archive were directly read for this comparison. Its SHA-256 is `b91af0ca58a62dfa223be44dcd5e95916dfb90edf0ac24443dd79823b4cb2896`. This does not claim a fresh audit of the entire predecessor proof or verification suite. No original archive or internal source-audit document is copied into this distribution. Offline replay does not refetch or execute those sources. This is a targeted attribution, not a comprehensive priority search or a claim that the relative denominator is new.

## Classical ingredients

### Jensen functional equations

Henrik Stetkær, **On Jensen's functional equation on groups**, Aarhus preprint, 2001, introduction and Theorem 2.2(a):

https://data.math.au.dk/publications/pp/2001/imf-pp-2001-3.pdf

This is context for classical normalization, oddness and recurrence arguments. That paper's target is complex-valued. It is not cited as permission to discard target-torsion hypotheses. Report288 proves the arbitrary-target identities and the finitely generated decomposition needed here without dividing by two in the target.

### The target-torsion boundary

Kh. Sabour and S. Kabbaj, **Jensen's and the quadratic functional equations with an endomorphism**, Proyecciones 36 (2017), 187–194, especially Theorem 3.3:

https://www.scielo.cl/pdf/proy/v36n1/art10.pdf

The pertinent affine-solution theorem explicitly assumes a 2-torsion-free target. Report288 retains the 2-torsion remainder for arbitrary targets and does not import that torsion-free conclusion without its hypothesis.

### Finitely generated abelian groups

Anthony W. Knapp, **Basic Algebra**, digital second edition, 2016, Theorem 4.56:

https://www.math.stonybrook.edu/~aknapp/download/b2-alg-clickable.pdf

The structure theorem is applied only to finitely generated subgroups, in particular the two-generated subgroup witnessing nonadditivity. The arbitrary ambient group is not assumed to split as a direct sum of cyclic groups.

### Interval averaging and amenability context

Terence Tao, **Some notes on amenability**, 14 April 2009:

https://terrytao.wordpress.com/2009/04/14/some-notes-on-amenability/

Intervals and boxes are classical averaging constructions. The article proves its particular additive-quadruple lifting limits by exact parity counts. It does not infer those limits merely because a sequence is Følner, nor assert them for every Følner sequence.

## Scope of source and integrity claims

Links and historical comparisons provide attribution; they are not executable dependencies. No public repository, full-module or theorem-prover audit is claimed. The finite exact checks are not a Lean kernel certificate. Checksums describe byte identity only and do not establish correctness, authorship, priority, or authenticity in the absence of a trusted external pin.
