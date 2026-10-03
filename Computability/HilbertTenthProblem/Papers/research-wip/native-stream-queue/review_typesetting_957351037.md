# Semantic transfer review: mixing and coercive Green operators

The inserted manuscripts preserve their original formulas and proofs. **One new comparison paragraph incorrectly attributes a finite-support point-source column to the connected operator; it needs the path/dipole distinction restored.** A second, minor README error counts six Parts instead of five. A narrow suggested correction is provided separately; no archived theorem, compiler or export needs alteration.

This review is pinned to `95735103756a49922094a76bd74f24cf4f24c101`, parent `f97814421444abae15b469eb30c7343d03c65394`. It covers the added Parts IV–V, their editorial comparisons and README summaries: Mixing (source 11), Coercive Green (12), and Well-Conditioned Computation (13). It inherits the full earlier manuscript reviews, rather than rereading all historic Parts I–III or rerunning unchanged author code. It covers neither later typesetting nor a rebuilt/rendered PDF.

## Findings and narrow correction

1. **Connected point-source versus dipole conflation.** At `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/stochastic-and-thermal-exactness/article.tex:5479`, the new “common theorem” paragraph identifies source 13's operator as `mI−J`, then says its Green column at an initial source has finite support exactly when the computation halts. In source 13, `J` denotes the connected adjacency, whereas the common path operator is `mI−J_P`. For the connected operator, every point-source inverse column is strictly positive at every vertex and therefore has infinite support, even for immediately halting inputs. The relevant finite-support connected response is `(mI−J)^−1(δ_s+−δ_s−)`. This is precisely the distinction already proved by the preserved antisymmetric-decoupling lemma and positivity obstruction (`article.tex:7210`, `:7683`).

   The proposed patch first states the common path-column theorem for `α,m≥3`, then its realization by a signed dipole on the connected operator for `m≥5`. It preserves the two-terminal resistance `2D_(L−1)/D_L`, the nonhalting value `m−sqrt(m²−4)`, and the no-cutoff conclusion. It explicitly distinguishes an initial-history root (source 12 starts history at zero, source 13 at one). No formula of either original manuscript changes.

2. **Part count.** `README.md:49` says “All six Parts share one pattern.” There are five Parts containing six manuscripts. The proposed patch changes this to “All five Parts.”

Both changes are in `review_typesetting_957351037.patch`, SHA256 `103c1d9aba1d427a992423dcd5a7a6db3d96e25ed457a42c8aaa298fe9d773c6`. The resulting article SHA256 would be `da1c5b65f031dc9e1ac40116137f2ba7c47414792e2ebda822ce31b5f71a1ebf`, and README `ad701262db6380fee711819e14d5b9f0966a61a80696833b8d19f1d01ccfc7b8`. The patch touches only that paragraph and that README word; it does not alter `article.pdf`. A private-copy application was checked. The nearest README gives the build command `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`; rebuilding the PDF is a separate integration action.

No second instance of the point-source conflation was found in the other new comparison notes or README. In particular, the connected-question answer at `article.tex:6750`, the resistance note at `:7355`, the convention table and the README all correctly retain the signed dipole and factor of two.

## Independent counterexample and correction proof

For a connected graph of maximum degree three and `m≥5`,

```
(mI−J)^−1 = Σ_(k≥0) J^k / m^(k+1).
```

All entries are nonnegative. For any source `s` and vertex `v`, a connecting walk of length `k` contributes a strictly positive term to entry `(v,s)`. Thus every point-source column has infinite support on this infinite connected graph, independently of halting. Conversely the rail-swap involution sends a dipole source to its negative. Uniqueness forces the solution to be antisymmetric, so all fixed hubs and backbone vertices have voltage zero; its positive-rail restriction is the path solution. The voltage difference between the two source terminals is consequently twice the path root value.

The portable helper includes a literal immediate-HALT fixture from the actual attachment definition, without importing an author program. With no computational path edges, take `s=v_0` and `m=5`. The dipole solution has only `u(v_0+)=1/5` and `u(v_0−)=−1/5`; every potentially nonzero row, including the common hub, is checked exactly. All other rows vanish by support-neighbor closure. Its resistance is `2/5` and its primitive integer charge is five. The walk

```
v_0+ → c_0 → d_0 → ... → d_n
```

exists for every `n≥0`, so the point-source column at `d_n` is at least `5^(−n−3)>0`. The receipt checks 32 explicit walks; the infinite conclusion follows from this symbolic family and the Neumann argument, not from a truncated matrix or finite census.

## Preserved original material

`review_typesetting_957351037.py` exposes `verify(repo)`. It reads fixed Git blobs, checks archive hashes before opening ZIPs in memory, rejects unsafe/duplicate/symlink entries, and executes no archived code. It restricts comparisons to each manuscript's inserted main text and its own appended appendices. Its deterministic receipt records every archive member, original/typeset article and README, the typeset PDF, unchanged placed members, prior review dependencies and the suggested correction hashes. Exact recursive types are required when replaying the saved receipt.

| Source | Original labels retained | Display blocks matched | Labelled statements matched | Proofs matched | Mathematical macros |
|---|---:|---:|---:|---:|---:|
| Mixing, source 11 | 62 | 62/62 | 19/19 | 18/18 | 15 |
| Coercive Green, source 12 | 85 | 54/54 | 21/21 | 21/21 | 17 |
| Well-Conditioned, source 13 | 75 | 60/60 | 18/18 | 18/18 | 14 |
| Total | 222 | 176/176 | 58/58 | 57/57 | 46 |

Matching removes whitespace/comments, label and citation namespaces, harmless display directives, and the written-out expansions of source 13's `cref` references. Without the last normalization, source 13 has 16/18 exact labelled statements and 10/18 exact proofs; the remaining differences were read and change only reference spelling, with the same targets and statement kinds. Mathematical macro definitions are also compared, allowing `DeclareMathOperator` versus an equivalent `operatorname` definition and delimiter-sizing differences. Every original displayed formula matches without an algebraic rewrite.

This is a bounded textual census, not a TeX parser or formal proof checker. It establishes preservation of the listed source blocks, not independently all sentences, literature claims or page-layout assertions. All 37 placed code/data/audit members from these three sources are byte-identical to the 49-member archived corpus. The commit modifies only `article.tex`, `README.md`, and `article.pdf`.

## Added claims and retained qualifications

**Mixing comparisons are supported.** The row-distribution lift is the corresponding mass-zero positive stochastic construction, with row/column conventions and rational scaling explicitly distinguished. The new text correctly separates a rank-one erasing product from a single coordinate attaining equilibrium: all products in the new alphabet are invertible, although exact coordinate reachability can remain c.e.-complete. The fixed-alphabet result remains an MRDP existence construction with a rational input curve/line, not a printed numerical universal alphabet or autonomous Turing simulation by a finite Markov chain.

The `r(P)+1` state lower bound remains about the exact centered series, not the zero set or gate complexity. The source's quartic/quintic state budgets are unchanged. The line filter is correctly restricted to natural coordinates and integral nonnegative error; the new note even repeats the real and signed counterexamples. Its cost comparison is also accurate: given `S`, the quadratic loader costs one multiplication and two additions, whereas the line filter costs one multiplication and three additions. The separated-target cutoff retains the strict inequality `theta^H < |c−1/s|`; it provides no cutoff at the equilibrium target. The new Part I notes answer only the corresponding exact-hit question and expressly leave rank-one fixed-alphabet erasure open.

**Green comparisons are supported after the correction above.** The convention table retains path versus connected coercivity constants, `m≥5` for the connected interpretation, odd `m` for the localization theorem, different history origins, reversed test-destination conventions and the two-terminal factor of two. The full integral fibre consists of positive multiples of a primitive certificate; the normalized source-12 slice and the connected source-13 fibre are not silently identified as the same unnormalized tuple. The text preserves torsion-free coefficient-ring scope and the positive-characteristic obstruction. Polynomial-time approximation is attributed to the path forest, while only computable exploration is claimed for the connected graph. The finite-prime decision theorem remains specific to the unit dipole solution of this family. The row-three theorem concerns each fixed connected scalar operator with a nonzero diagonal; it is not a uniform graph-type algorithm or an arithmetic-circuit lower bound.

**The new paid-routing reference is accurate.** At `article.tex:7864` and README lines 118–124, the complete transfer-program evaluator at external horizon three is reported as `245→206` operations. This agrees with the already independently reviewed `connected_cross_routing_slp` source/note: `92M+153A→65M+141A`, including all affine rows, residual squares, shared sums, routing and final addition. The displayed identity `C_t=Σ_r(B−b_r)A*_r` is an all-integer polynomial identity; it does not substitute the zero-set constraint `B=1`. The natural zero theorem, ordinary inputs and external horizon stay unchanged. The typeset text correctly disclaims a fixed-arity universal equation or optimality claim and keeps the author's separate slack-projection observation unimplemented.

**API status is accurately reported.** The reference source-13 compiler remains unpatched. The new note accurately records export aliasing that can erase input binding and prime deduplication that hides inexact values, and links the isolated snapshot repair. The mathematical theorems and valid original exports are unchanged. Mixing's prior full-review PASS is not expanded into a hostile JSON-parser guarantee.

**Not independently established here.** Platform-specific suite timings, the typesetter's extra example/basis experiments, its 8-gram overlap statistic, historical-priority claims, and PDF build/page/numbering/no-warning claims are reported provenance. They were not repeated. The original full reviews, preserved code and existing routing packet are the mathematical/source dependencies. This audit does not extend to future commits or apply the suggested patch automatically.

## Pins and replay

All original archives are read from `ef2fc7990:docs/incoming/`:

| Archive | SHA256 |
|---|---|
| `Mixing_Does_Not_Remove_Arithmetic.zip` | `8c3543f514df39f26f5668d5434ddaa50580aab0303ef84dc6c286731c50c1ca` |
| `Coercive_Green_Diophantine.zip` | `8e2830036ad0a465f729d4729835b350ea288f758fd8bac8a3ac179ebe368d7a` |
| `Well_Conditioned_Diophantine_Computation.zip` | `9cd194e2d3b1cd7814ad465c1c4abae8966b6c7bb0b5a13d1955d17aba159258` |

Typeset article SHA256 `6533bb6e13149da0ae41eb010166ef42d32d6996794e76fb3dae56f632a707a8`; README `8c651e99a35eedd1b52dfd0387e694fb3520e13dcd58b2c263a2a3e6911e9780`.

The JSON pins `review_mixing_aebfa386e.md` at `5b633fcf9`, `review_coercive_connected_aebfa386e.md` at `899391bde`, and both `connected_cross_routing_slp.md` and `review_connected_cross_routing_slp.md` at `9bc875b6a`.

```sh
python /path/to/review_typesetting_957351037.py --repo /path/to/Proofs
# Optional deterministic receipt regeneration:
python /path/to/review_typesetting_957351037.py --repo /path/to/Proofs --write
```

The default is read-only receipt replay. Writer and fresh replay from a different working directory both passed. No author suite or repository mutation was performed.

Root regenerated the portable receipt and matched its exact bytes, then applied the published patch to fresh private copies of the two pinned source files. Both corrected hashes matched the receipt. The maintained manuscript and PDF are unchanged; applying this patch to the report requires rebuilding its PDF.
