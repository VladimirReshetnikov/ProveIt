# Semantic transfer review: clock spectra and polynomial witness histories

One small editorial degree error was found. The original displayed formulas, labelled statements and proofs are preserved under the documented namespace and layout changes; the new summaries retain their natural/polynomial witness domains and external-horizon limits. No new arithmetic-operation improvement or ordinary fixed-arity representation follows from these typesetting commits.

This is a bounded transfer audit of `c5f6a3219ead858c46e3552cbc0cb1745f512a20` (clock spectra added to *Liveness beyond halting*) and `c03d95fe62333986d306f353c66dd7cee42d0743` (three manuscripts collected in *Polynomial witness histories*). It inherits the earlier complete manuscript reviews, reads the new editorial passages and READMEs, and compares the inserted originals. It does not repeat the full historical collections, author code suites, PDF builds or literature-priority review. Smooth quartic typesetting `83abbd7fa` is a separate review.

## Actionable finding

At the pinned `c03d95fe6`, `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/polynomial-witness-histories/article.tex:3546` says the univariate quartic is the counterpart of Part I's quadratic, **“one degree higher because the identities are quadratic.”** The final polynomial's unknown-degree rises from two to four, not two to three. Replace “one degree higher” with “twice the degree” or “degree four instead of two.” Both theorem statements, equations and domain tables already give the correct degrees. This is an editorial note, not a mathematical defect in the original construction.

A narrow suggested correction is saved as `review_typesetting_c03d95fe6.patch`. No repository file was edited. The receipt continues to pin the original revision, including this wording; applying the correction does not retroactively change the scope of this receipt.

Root independently applied the patch to a private copy and confirmed that it makes exactly that wording replacement. Rebuild the report PDF when applying the text correction; the delivered PDF remains unmodified. Root also repeated the full portable comparison and matched the saved receipt.

## Reproducible comparison

`review_typesetting_c03d95fe6.py` exposes `verify(repo)` and reads only pinned Git blobs. It opens ZIPs in memory, rejects unsafe/duplicate/symlink members, executes no archived program, and verifies the renamed delivered files against their archive bytes. Its CLI compares the deterministic receipt with exact Python types by default; `--write` regenerates it. A fresh default replay from a different working directory passed.

```sh
python /path/to/review_typesetting_c03d95fe6.py --repo /path/to/Proofs
```

Each typesetting commit changes only its `article.tex`, `article.pdf` and `README.md`. All 44 placed code/data/audit members from the four source archives are byte-identical to their originals. The receipt inventories all 61 original archive members and pins the original and typeset articles, READMEs, PDFs, and four prior review notes.

| Source | Original labels preserved | Display blocks matched | Labelled statements exact | Proofs exact | Mathematical macro definitions preserved |
|---|---:|---:|---:|---:|---:|
| Clock spectra (source 12) | 55 | 42/42 | 19/19 | 13/16 | 13 |
| Unique polynomial histories (06) | 76 | 64/64 | 19/19 | 19/19 | 15 |
| One-coordinate certificates (15) | 75 | 55/55 | 23/25 | 24/24 | 10 |
| Linear boundary transport (01) | 65 | 53/53 | 16/16 | 13/13 | 17 |
| Total | 271 | 214/214 | 77/79 | 69/72 | 55 |

“Exact” here means normalized source text: whitespace/comments, labels and citation namespaces, the documented clock-macro and boundary `\F` renamings, and harmless display directives are removed or mapped. Matching is restricted to the corresponding new Part. No original statement or proof text is deleted by the remaining differences. The two statement changes insert explicit pointers to the earlier ray lemma and bivariate theorem; the three proof changes insert explicit clock-relation notes. Those five insertions are recorded verbatim in normalized form in the JSON and were read. This regex census is reproducible textual evidence, not a TeX parser or formal proof checker; it does not certify every prose sentence or PDF rendering.

## Semantic classification of added passages

**Supported summaries and cross-references.** The clock opening and README correctly distinguish first-matching stages from settling times, least from merely minimal degrees, and each construction's own fixed interpreter. The self-modulus conclusion remains nonuniform and does not assert a complete classification. The comparison between the quartic and quadratic two-stack certificates explicitly preserves the different rule formats/stack codes, initial-coordinate convention, natural-only zero bijection, and external horizon. The new `3+T+4mT+k` figure counts grouped summands, not arithmetic operations: three initial squares, one selector square per step, four guard gadgets per rule and step, and one deadline square per requested deadline. The reported `3(T+1)+9mT+k` coordinates and the cubic alternative's `3(T+1)+mT+k` agree with the archived construction. The resource comparison applies to a common primitive machine format, as the accompanying table makes explicit.

The polynomial collection keeps three distinct witness settings: nonnegative finite polynomials in two indeterminates; the quadratic one-indeterminate compiler with a computed stride; and boundary transport over a **nonzero** commutative ring with prescribed omitted-variable sorts. It retains first singleton acceptance, the full-witness uniqueness statements, the finite-support requirement, and the absence of a computable input-only degree bound. The ring theorem still allows zero divisors and signed coefficients; it does not silently extend the nonnegative cellular proof to signed coefficients. The new front-matter tables distinguish witness degree from degree in the unknowns and do not count polynomial unknowns as integer coordinates. The integer/rational energy gap and Hilbert-space nonclosed-range claims remain separate from finite-dimensional optimization and from the later coercive Green-operator setting.

The ten-row projection note at `article.tex:4033` accurately summarizes the already reviewed map `S=XS0`, `E=XE0`, `D=S0B`: ten quadratic identities and `s^3+s+6` unknowns, with coordinate shifts up to `X^3`. It claims a complete natural-polynomial zero bijection, **not** an off-zero polynomial identity or a paid scalar-operation saving. The source states explicitly that its typesetting author did not rerun that earlier review. The earlier review's graph correction remains relevant; no such correction was silently replaced by all-value equality.

The READMEs accurately identify all four shipped compilers as the unpatched originals where relevant, describe the established type/aliasing defects, and link their isolated repairs. Since code bytes are unchanged, these typesetting commits neither install those repairs nor invalidate the earlier valid-domain proofs.

**New derived observations, independently checked here.** These are not verbatim archived theorem statements, and the typeset text identifies them as editorial.

1. At clock `article.tex:5562`, for a singleton explorer tree, a recurrent accepting schedule computes the unique path by decoding its completed unary guesses. Conversely the path computes the exact guesses and an accepting schedule. Hence the least scheduler degree equals that singleton path degree. This concerns successful recurrent schedules, and it does not identify different interpreters without a simulation argument.
2. At polynomial `article.tex:5544`, the bounded-height univariate finite-state argument extends to `Z[X]` with coefficient alphabet `[-B0,B0]^n`, and to every finite coefficient ring with alphabet `R^n`. For `A(X)u(X)=b(X)`, each coefficient equation reads a finite window of coefficient vectors of `u`. After the finitely many nonzero coefficients of `b`, one finite automaton handles the homogeneous tail; a zero-padding drain of length at least the coefficient degree enforces finite support. Its transition tests use exact ring arithmetic and need no positivity. Therefore bounded-height integer solvability and unrestricted finite-ring solvability are decidable. A computable reduction of an undecidable c.e. set cannot have even one Boolean integer-polynomial solution on every accepted instance, since bound one would decide it. The stated at-least-two-indeterminate conclusion for that precise linear, finite-alphabet/Boolean syntax follows, including ordinary omitted-coordinate sorts. It is not an impossibility theorem for nonlinear univariate systems, unrestricted-height `N[X]`, or arbitrary stronger witness predicates. The gap between two indeterminates and the four of the displayed row-tagged construction is correctly left open.

**Not independently rerun in this bounded audit.** The typesetter's Windows timings, LF/CRLF regeneration observations, scratch PDF build/no-warning assertions, and its additional worked-example packing experiment are provenance statements. The mathematical packing bijection itself is inherited from the previously reviewed unchanged proof. No claim of independent confirmation of those platform/build experiments is made here. Neither historic literature-wide priority nor future typesetting revisions is covered.

## Principal pins

| Archive | Arrival | SHA256 |
|---|---|---|
| `clock_spectra_research.zip` | `060e08a07` | `dbbcc5ed44b2a1b87da14ab863c32a5b125484480652fa9a04c5e0340082fb22` |
| `unique_polynomial_histories.zip` | `060e08a07` | `0f0f52d5c6617a22cdd0820386eb378c700e5f5c36bfee810ae13818137465e4` |
| `one_coordinate_certificates.zip` | `ef2fc7990` | `453ae5f3b3726a288ae30325cbf8e1b6aa15bf6495fb5f23f4e8e8985f713829` |
| `Linear_Boundary_Transport_Research.zip` | `060e08a07` | `7b2b3505fe36d9f01777bd198742cc1206f1232e0951964d1ee30681c6c5e096` |

New clock article SHA256 `c0779e7d5ff51efc0b1c290279680688d8f7179223840cdc7f0ca2c65bc34d1a`; README `6c71c6fe63829f88dac2f7ccfc4fa1d6da60a55542785360f3b3a90f9d341494`.

New polynomial article SHA256 `2f601be5c8cfce4a5fb0ce057c7e9e8579e2859d268cb3fc6e5394fcc8adc385`; README `1c5369df44bd856e3f9b30b805cdde21a063c4918f57c39526d8ebb49f28acf9`.

The full review dependencies pinned in the JSON are `review_spectral_060e08a07.md` at `2c311e525`, `review_unique_polynomial_histories.md` at `e5497072e`, `review_one_coordinate_aebfa.md` at `a21c86070`, and `review_boundary_sandpile_060e08a07.md` at `49bc4c654`.
