# Source provenance and inspection boundary

## Pinned repository state

This continuation was prepared against
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt),
commit
[`e0d9463bdee9685dfb1dddb819059cc738540c57`](https://github.com/VladimirReshetnikov/ProveIt/tree/e0d9463bdee9685dfb1dddb819059cc738540c57).
The two user-specified entry points were the polylogarithm manuscript and
the incoming-report directory. All repository paths and mathematical
status statements in this package refer to that pinned state unless an
external publication is explicitly named.

`source_manifest.json` records the exact repository-relative path,
commit-specific URL, expected and computed Git blob SHA-1, SHA-256, and
byte count for each authenticated source. It contains metadata only;
the delivery does not redistribute the source repository or the prior
incoming archive.

| Source category | Authenticated files | Inspection role |
|---|---:|---|
| Manuscript chapter texts | 72 | Corpus search, conjecture/status checks, and detailed reading of passages relevant to the present identities |
| Manuscript support texts | 8 | Main TeX, references, README, source inventory, editorial plan and ledger, validation, and work log |
| Incoming intake ledger | 1 | Intake conventions, placement history, and provenance guidance |
| Pending incoming archive | 1 | Predecessor research package and its stated results/questions |
| Supplementary archived report texts | 5 | Targeted checks for already established results and methodological antecedents |
| **Total repository files** | **87** | **All computed Git blob hashes match the pinned originals** |

The 72 chapter hashes and eight support hashes were checked against the
saved Git tree/contents metadata for the pinned source snapshot. The five
additional report hashes and the incoming directory hashes were verified
against pinned GitHub file metadata. This inventory does not include the
repository's prebuilt manuscript PDF, the complete figures/verification
trees, or every historical research report.

Authentication establishes which bytes were inspected. It does not assert
that every line in this large source corpus was independently proved.
Detailed mathematical inspection focused on the harmonic, Stieltjes,
Gamma/polygamma, polylogarithmic, and source-status claims used in the
article. In particular, no exhaustive audit of all historical reports or
all literature is claimed.

## The pending incoming archive

The pinned archive is

`docs/incoming/ProveIt_Polylogarithm_Stieltjes_Continuation_2026-10-10.zip`.

- Git blob SHA-1: `2b19b137342f68561fe7bca55da16caa2291baf1`.
- SHA-256: `1d5185658181b7e62b9122f638b3f1232ae2247901f1ec1e898b11ff028fd33f`.
- Size: 1,096,405 bytes.

The manifest records SHA-256 hashes and sizes for all 64 original archive
members. The 46 members made available as local inspection copies match
the ZIP member bytes exactly. The other 18 members were not extracted in
the source-reading workflow; they remain authenticated as members of the
unchanged ZIP. Those omitted members are recorded explicitly, rather than
represented as inspected local files.

The predecessor package develops translation/Stieltjes and Gamma
identities, Euler/Lerch transition results, critical-cutoff finite parts,
and Cayley-depth results. Its relevant mathematical sections, audit, and
research agenda were consulted for overlap. The present package neither
promotes its remaining conjectures solely on the strength of saved
diagnostics nor treats an earlier agenda item as still open after a later
archived report already resolves it. No supplied numerical output is used
as a substitute for a proof in this article.

## Supplementary report texts and established results

These additional files are important because the canonical chapters do
not contain every result already present in the report collection.

1. `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/convolution-calculus/Stieltjes_Convolution_Calculus.tex`

   Git blob `674f9a5a7400bb8f2471e25699ef27f253d2a17b`.
   This report already contains distributional convolution identities and
   the symmetric first-Stieltjes identity in order-zero polylogarithm jets
   (`eq:Li0identity`).

2. `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/convolution-algebra/article.tex`

   Git blob `c7c11cab257d1cb45626d87e3262aae2d208d12c`.
   This report already proves the one-generator Stieltjes Bell algebra,
   bivariate Gamma multiplication, contact corrections, polygamma
   convolution collapse, and the reflected two-parameter polylogarithm
   kernel. Relevant labels include `thm:Bell`, `eq:BellG`, `thm:product`,
   `eq:Gproduct`, and `thm:reflected`.

3. `Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/shifted-hurwitz-jets/sections.tex`

   Git blob `990369336bdf2794aae3057c3231eed4ecadbef3`.
   This continuation already contains the repeated-primitive formula,
   periodic endpoint regularity, canonical distributional residues,
   reflected all-index closure, and derivative contact laws. The primitive
   comparison includes `shj:Uformula` and `shj:Ulemma`.

4. `Analysis/Polylogarithms/docs/reports/alternating-harmonic-polylogarithms/article.tex`

   Git blob `48b47e1e6800cfd0d6062f62745b3f70c98484d5`.
   Its elementary harmonic coefficients, shifted alternating beta
   reflection, and cyclotomic residue filters are antecedents. The present
   harmonic section does not claim these methods as new. Its SHA-256 and
   byte count also agree with the pinned manuscript source inventory.

5. `Analysis/Polylogarithms/docs/reports/lerch-global-phase/continuations/harmonic-order-geometry/sections/harmonic_order.tex`

   Git blob `6e8df6ec065e775a63d9865b89444b25ce93e104`.
   Its `sorder:prop:entire` and `sorder:cor:negative-values` already apply
   Mellin subtraction and reciprocal-Gamma zeros to an alternating
   depth-one odd-denominator harmonic interpolation. That function is
   entire. The present nonalternating family has a logarithmically singular
   local kernel, and its residual Laurent poles require the different
   all-depth coefficient extraction proved here. This file's SHA-256 and
   byte count also agree with the pinned manuscript source inventory.

Consequently, the untwisted periodic Stieltjes/Bell/polylogarithmic part of the
article is a consolidation with independent proofs and checks. It is not
presented as a new-to-repository solution merely because older material
once asked the underlying question.

The same `convolution-algebra/article.tex` explicitly asks, under
“Twists, characters, and alternate endpoint normalizations,” for a
nonintegral-frequency Stieltjes normal form and an all-index half-twist
multiplication table including its point-supported counterterms. The new
`03_twisted.tex` section answers this specified target with a singular
normalization, convolution unit `delta_0`, covariant contact and primitive
formulas, and the exact zero-mode correction in the untwisted limit. The
Lerch function itself is classical; the modified Stieltjes constants of
[Hu and Kim](https://doi.org/10.1016/j.jmaa.2021.125930) and the nonsingular
alternating Hurwitz convolution of
[Zhu, Hu, and Kim](https://doi.org/10.1016/j.bulsci.2025.103724) are credited
antecedents. The resolved repository target concerns their singular
extension and normalization, not first discovery of those functions or
the nonsingular alternating identity.

The second principal continuation candidate is the arbitrary outer-shift,
all-depth rule for nonpositive
Laurent principal and constant coefficients, together with reflection,
multiplication, and finite-part antiderivatives. No exhaustive global
priority claim is made for either continuation.

## External literature boundary

The article cites primary sources for its classical foundations and
external antecedents. The supplementary harmonic literature check includes:

- Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic
  Numbers*, Integers 26 (2026), A81,
  [DOI 10.5281/zenodo.20931235](https://doi.org/10.5281/zenodo.20931235).
  The primary full paper was inspected. Its beta-derivative evaluations
  cover the positive-integer baseline, which is not claimed as new.
- Young, *Series of Height One Multiple Zeta Functions*, Integers 24
  (2024), A43,
  [DOI 10.5281/zenodo.11221606](https://doi.org/10.5281/zenodo.11221606).
  The primary full paper was inspected for the complex Barnes-order and
  height-one framework.
- Young, *Global series for height 1 multiple zeta functions*, European
  Journal of Mathematics 9 (2023), article 99,
  [DOI 10.1007/s40879-023-00695-0](https://doi.org/10.1007/s40879-023-00695-0).
  The primary publisher abstract and metadata were verified. Its
  subscription full text was not obtained in this audit. Its unshifted
  Laurent work is explicitly credited; this limitation prevents an
  exhaustive comparison with every formula in that paper.
- Kargin, Dil, Cenkci, and Can, *On the Stieltjes constants with respect to
  harmonic zeta functions*, J. Math. Anal. Appl. 525 (2023), 127302,
  [DOI 10.1016/j.jmaa.2023.127302](https://doi.org/10.1016/j.jmaa.2023.127302).
  This literature is credited while distinguishing its harmonic Hurwitz
  conventions from a shift in only the outer denominator.

See the article bibliography for the remaining classical references, and
`verification/harmonic_source_overlap.md` for the focused mathematical
overlap discussion. A search failing to locate an equivalent formula is
not evidence of global originality. Correctness rests on the proofs and
their stated domains, independently of the priority assessment.

## Byte normalization and repository effects

All 80 manuscript/support downloads matched their expected Git blob hashes
when this final integrity audit began. All five archived TEX files and the
ZIP also matched. The local downloaded copy of `docs/incoming/README.md`
contained one additional trailing LF: 137,576 bytes rather than the
original 137,575. Removing exactly that byte reproduced the pinned Git
blob `9956ad83c5ddfa3c75e5f2946481a83082bc81e8`, and only that downloaded
copy was restored. The before/after hashes and the hash guard are recorded
in the manifest. No mathematical source text was rewritten during this
provenance operation.

The package contains proposed integration material; this work did not
modify or publish the upstream repository. The source-correction patch is
a reviewable proposal. This package's reproduction checks concern the new
article's exact polynomial identities and independent numerical
diagnostics, and are separated from the authentication of predecessor
source files.
