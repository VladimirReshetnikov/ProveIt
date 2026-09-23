# Critical-Point Defects in Surreal Arithmetic

**Large-cardinal embeddings, exact support thresholds, descent to the target model, omnific independence, surcomplex fields, and omnific integers**
Merged research report, 23 September 2026, built from three manuscripts of
batch 30 (manuscripts 06, 07 and 09, placed in `21375f8`; they keep those
numbers here). Each was prepared for Vladimir Reshetnikov (07 and 09 with
ChatGPT) and pinned to repository commit `0865f04`. Manuscript 07 is the base
text.

Independent proof review and formalization are pending. No statement of this
report has a Lean implementation mapping, and the report was not refereed.

```
article.tex                                 the report, standalone LaTeX with an internal bibliography
article.pdf                                 the compiled report, 80 pages (unnumbered title page,
                                            front matter i–iii, then pages 1–76)
README.md                                   this guide
06-critical-supports-PROOF_STATUS.md        source 06's proof status and source audit, as delivered
07-critical-point-defects-PROOF_STATUS.md   source 07's proof, provenance and verification status, as delivered
09-support-geometry-PROOF_STATUS.md         source 09's proof status and assumptions, as delivered
code/
  06-critical-supports-build.sh             source 06's build helper, as delivered (does not run here)
  07-critical-point-defects-build.sh        source 07's build helper, as delivered (does not run here)
  07-critical-point-defects-finite_regression.py
                                            source 07's exact finite checks (standard library only)
  09-support-geometry-build.sh              source 09's build helper, as delivered (does not run here)
data/
  07-critical-point-defects-build_validation.json         07's record of its delivered PDF build
  07-critical-point-defects-finite_regression_results.json  07's recorded run of the finite checks
  07-critical-point-defects-finite_regression_console.txt   the same run's console output
```

Every label in `article.tex` carries the prefix `lce:` (254 labels). The 120
labels delivered with 07 are kept, unchanged after the prefix. The merge added
134: 56 for 06's material (`lce:cs:`, "critical supports"), 59 for 09's
(`lce:sg:`, "support geometry"), 11 on 07's previously unlabelled questions
(`lce:q:classification` … `lce:q:formal`), and 8 for merge text
(`lce:sub:headlines`, `lce:sub:nonasserted`, `lce:sec:conventions`,
`lce:rem:dsnsupport`, `lce:rem:opa`, `lce:sub:collection`,
`lce:app:nonclaims`, `lce:app:provenance`). The
[formalization ledger](../../FORMALIZATION.md) indexed the placed base under
its unprefixed delivered labels (`lem:index`, `thm:defect`, …); those labels
are now `lce:lem:index`, `lce:thm:defect`, and so on.

Delivered files under `code/` and `data/` and the three proof-status files are
byte-identical to the delivery. Not shipped: the three manuscripts' PDFs, the
`.tex` and README of 06 and 09, and 07's delivered README (replaced by this
one). `article.pdf` is a build of this text.

## Three sources, one report

| | Archive (in `190d301`) | Manuscript | Contributes |
|---|---|---|---|
| **07** | `Surreal_Large_Cardinals_Research.zip` | *Critical-Point Defects in Surreal Arithmetic: Large-cardinal embeddings, exact support thresholds, surcomplex fields, and omnific integers* (32-page PDF) | The base text: every untagged section. Exact image intersection and projection isomorphism, positive-family threshold and escape theorem, mask algebra and mask criterion, omnific and surcomplex transfers, logarithmic defect, exponential locus and two closures, the supercompact seed, 12 questions, formalization plan, finite regression. |
| **06** | `Surreal_Large_Cardinals_Critical_Supports.zip` | *Critical Supports and Large Cardinals in Surreal Arithmetic: Ultrapower transport, Hahn lifts, and omnific descent* (27-page PDF) | Proof of the critical-point facts; descent of `H_j(x)` to `M`, landing spectrum, seed–closure lemma, cover obstruction and normal-measure trichotomy (Section 9); bounded and omnific measure codes; formal evaluation and the exponential scale corollary; support covers and exact descent (Section 17); the fixed class of `H_j`; 9 questions; audit checklist. |
| **09** | `surreal_large_cardinals_article.zip` | *Large Cardinals and the Support Geometry of Surreal Embeddings: Exact equalizers, additional normal-form terms, and omnific algebraic independence* (30-page PDF) | A second proof of the absoluteness lemma; the short-support field at every uncountable cardinal (Section 3); omnific monomial witnesses and the omega-map incompatibility; order continuity; almost-disjoint omnific independence and the `2^κ` family (Section 13); the compatible-field-embedding criterion; seed coefficients over arbitrary index sets; weak compactness as a prefix principle (Section 18); the visibility hierarchy; 13 questions. |

All three pin `0865f043aec113c14c69ef45006bbc7546a4e75a`, 55 commits before the
placement. Each archive was matched to its number by the `git hash-object` of
its proof status against the staged prefixed files.

**Why one report.** The three manuscripts study the same pair of maps and
prove the same spine independently: an elementary embedding `j : V → M` with
critical point `κ` gives `J` (apply `j` to sign sequences) and its strong
companion `H_j` (apply `J` to the exponents of the Conway normal form); the
difference `J(x) − H_j(x)` is the subseries of the transformed normal form
indexed by `j(θ) \ j″θ`; the equalizer is the field of surreals with fewer than
`κ` normal-form terms; and one coefficient recovers the derived normal measure.
07 is the base: on the shared theorems 06 and 07 have the weakest stated
hypotheses (09's headline assumes a normal-measure ultrapower, though its
arguments need no more) and 07 is the broader of the two. No contradiction
between the sources, and no false theorem, was found.

**Printed once**, with all proving sources named at the statement: the first
missing index, the absoluteness lemma, the induced embedding, the strong
companion, the defect formula and equalizer, the leading-term corollary, the
omega-map locus, the small-family threshold and first failure cardinal, the
derived normal measure, the distinguishing corollary, the zero-probe warning,
the character theorem, the omnific equalizer and constant terms, the
surcomplex transfer, the twisted product law, exponential transfer and the
exponential locus.

**Second routes**, marked in the text: 09's proof of the absoluteness lemma
(limit cylinders and truncation simplicity); 09's embedding-free real
closedness of the short field beside 07's proof through the embeddings; 06's
direct support counting; 09's fiber argument for weighted evaluation; 06's
formal-evaluation proposition for the infinitesimal factor.

**Kept separately** because they are different statements: the three measure
codes (07's `h_A`, 06's `h̃_A = h_κ + h_A`, 09's omnific `Y_A`) and their
omnific shifts; 07's mask criterion and 09's compatible-field-embedding
criterion; 07's supercompact seed coefficient, 06's exact-descent and cover
characterizations and 09's covering and exact seeds; the 34 questions.

**Marking.** `[06]`, `[07]`, `[09]` tag statements by source; `[merge]` marks
text written for the merge. 06's and 09's headline theorems are printed in
Section 1.3 with proof pointers. Section 1.5 has the sources table, the
hypotheses of each source, and the full renaming table; Appendix C lists every
non-claim by source; Appendix D records provenance and every merge decision.

**Notation.** 07's symbols are kept. Renamed from the other sources (no
normalization changed):

- 09's `T`, `D` are `H_j`, `D_j`; 06's `K_{<κ}` and 09's `F_κ` are `𝒮_{<κ}`;
  06's `K_{≤κ}` is `𝒮_{≤κ}`; 09's `I_κ` is `𝓘_{<κ}`; 06's `sc(x)` is `|supp(x)|`;
  06's `ℓ_nf` and 09's `len_NF` are `len`.
- 06's detector `u_λ` and 09's `Q_θ` are 07's `h_λ`; 06's code `c_A` is
  `h̃_A = h_κ + h_A` and its `z_A` is `z̃_A`; 06's `v_λ = ω^λ u_λ` is
  `ζ_λ = ω^λ h_λ` (`v` is 07's valuation); 06's `x^↑` is `p(x)`; 06's binary
  series `Q`, `Q⁺` are `B̂`, `B̂⁺`; 06's `W_s` is `U_s`.
- 09's `e_α` and `q_α` (two names for `ω^{−α}`) are `q_α`; its `u_α = ω^{e_α}`
  is `τ_α`; its masks `Z_θ`, `Z_A`, `W_f`, `Z_{A,h}` are `Y_θ`, `Y_A`, `Y_f`,
  `Y_{A,e}`; its coefficient functional `c_γ` is `[ω^{q_γ}]`; its bijection `h`
  is `e`; its group `E` is `G_κ` and subspace `H` is `Ξ`; its polynomial `P` is
  `Φ`; its `χ(A)` is `χ_E(A)`; in the weak-compactness proof its strings `s`,
  tree `S`, injections `q_α`, lengths `D_α` are `σ`, `ℛ`, `ι_α`, `Δ_α`; its
  index `j` in `⋃_{j≠i} A_j` is `k`.
- Tempting false readings, excluded in the text: the equalizer is not a fixed
  field (`J(κ) = H_j(κ) = j(κ) ≠ κ`); short support is not a birthday bound;
  the Hadamard product `⊙` is not surreal multiplication; `ω^a` is Conway's
  omega-map, never `exp(a log ω)`; `z_A` and `Y_A` are different numbers; the
  landing spectrum `𝓛(j)` is not the logarithmic defect `L_j`.

## What the report claims

Numbers are those of `article.pdf`. Hypotheses: an elementary class embedding
`j : V → M` into a transitive class containing all ordinals, with critical
point `κ`, and class-parameter Separation and Replacement (a normal-measure
ultrapower is an instance); where stated, more.

- **Defect and equalizer (Theorem 5.1; 06, 07, 09).** For `x` of length `θ`,
  `D_j(x) = J(x) − H_j(x)` is exactly the subseries of `J(x)` indexed by
  `j(θ) \ j″θ`; its exponents lie outside `J(No)`; `D_j(x) = 0` iff
  `|supp x| < κ`; for `θ ≥ κ` the leading term sits at index `κ`.
  **Corollary 5.3** (09): the first `κ` terms agree. **Corollary 5.6,
  Theorem 5.7**: `H_j(ω^x) = ω^{H_j x}` iff `x ∈ 𝒮_{<κ}`, and no embedding with
  `J`'s monomial action is both omega-equivariant and `κ`-strong (09).
  **Proposition 5.5** (06): the fixed class of `H_j`.
- **The short field without an embedding (Section 3; 09, 06).** `𝒮_{<κ}` is real
  closed for every uncountable `κ`, regular or singular (Theorem 3.1); closed
  and nowhere dense and not definable in the ordered field (Proposition 3.5);
  `Oz ∩ 𝒮_{<κ}` is an integer part (Proposition 3.6); `𝒮_{≤κ}` is also a
  field (Corollary 3.2).
- **Image geometry (Theorems 6.1, 6.4, 7.1; 07).** Exact intersection
  `J(No) ∩ H_j(No) = J(𝒮_{<κ})`; coefficient projection is an isomorphism of
  the two incomparable immediate image fields; `J` and `H_j` are proper
  (Proposition 7.4, 06).
- **Summation (Theorems 8.1, 8.4, 8.6; 06, 07, 09).** `J` preserves strong
  sums of fewer than `κ` terms; for positive families exactly those; the
  omnific family `τ_α = ω^{ω^{−α}}` also fails at `κ` (09); positive strong sums
  of `≥ κ` image elements escape `J(No)` (07). Both maps are order-continuous
  (Proposition 8.5, 09).
- **Descent (Section 9; 06).** `H_j(x) ∈ No^M` iff `j″λ ∈ M`, `λ` the length of
  `x` (Theorem 9.1), independent of coefficients; in a set-ultrapower iff
  `M` is closed under `λ`-sequences (Lemma 9.3, Corollary 9.4); for a
  normal-measure ultrapower iff `|supp x| ≤ κ` (Theorem 9.7), giving the
  trichotomy `< κ` (equal, lands), `= κ` (unequal, lands), `> κ` (unequal, does
  not land), with no GCH. The counting also works for any ultrapower on an
  index set of size `κ`.
- **Measures (Section 10).** One coefficient of `D_j(h_A)` is `1` iff
  `A ∈ U_j` (Theorem 10.1; 06, 07, 09), also with 06's bounded code and a
  standard-part reading (Theorem 10.2) and 09's omnific code (Theorem 10.3);
  distinct normal measures give distinct functionals (Corollaries 10.4,
  10.5). Evaluation is a character of the Hadamard mask algebra (Theorem
  10.7, Proposition 10.8). Measurability is equivalent to a small-union
  character of the mask algebra (Theorem 10.9, 07) and to an ordered field
  embedding of `No` compatible with `⊙` on masks, small strong sums and the
  omega-map (Theorem 10.10, 09). Both criteria keep the coefficient algebra.
- **Omnific and surcomplex (Sections 11, 12).** Preservation and reflection of
  `Oz`, equalizer, intersection, fractions and constant terms (Theorem 11.1);
  purely infinite measure codes (Theorem 11.2, Corollary 11.3); all three
  support regimes occur in `Oz` (Theorem 11.4, 06); transfer to `No(i)` and
  `Oz[i]` (Theorem 12.1) with descent (Theorem 12.3, 06).
- **`Oz`-reflecting, not strong (Remark 11.6, merge).** Given a measurable
  cardinal, `J` is a field embedding of `No` with `J^{−1}(Oz) = Oz` that fixes
  `R`, preserves `ct`, and is not strongly additive; it is not onto. This
  answers the first two clauses of `opa:as:q:embeddingstrong` negatively under
  that hypothesis, as the omnific-preserving-automorphisms report records.
- **Independence without large cardinals (Section 13; 09).** For uncountable
  `κ` and a `κ`-almost-disjoint family, the omnific masks `Y_A` are
  algebraically independent over all of `𝒮_{<κ}` (Theorem 13.3); if
  `2^{<κ} = κ`, one set-sized Hahn field holds `2^κ` of them and
  `trdeg = 2^κ` (Theorem 13.5); also over `𝒮_{<κ}(i)`, and at a measurable
  `κ` all lie outside the equalizer (Corollary 13.6).
- **Logarithm and exponential (Sections 14, 15; 07, 06).** Twisted product law
  (Proposition 14.2); logarithmic defect homomorphism with kernel
  `𝒮_{<κ}^×` (Theorem 14.3); `H_j(exp x)/exp(H_j x) = exp(D_j(p(x)))`, so
  compatibility holds iff the purely infinite part has fewer than `κ` terms
  (Theorem 15.3), and the ratio is `1`, infinitesimal or infinite (Corollary
  15.4); the two closures of the common field (Theorem 15.7).
- **Seeds and compactness (Sections 16–18).** Seed coefficients over any index
  set (Theorem 16.1, 09); the supercompact seed as a missing-index defect
  coefficient (Theorem 16.2, 07); covering and exact seeds (Proposition 16.3,
  09); strong compactness as an internally short binary cover and
  supercompactness as descent of one number, also in `Oz` (Lemma 17.1,
  Theorems 17.2, 17.3, Corollary 17.4, 06); weak compactness at an
  inaccessible as an omnific prefix principle (Theorem 18.2, 09). These are
  credited translations of classical characterizations.
- **Absoluteness (Lemma 2.6; 06, 07, 09)** for transitive inner classes with
  the same ordinals and reals, including normal forms and the omega map; its
  consequence for the definable-surreals report is Remark 2.9 (below).
- **Questions.** 34: 07's twelve (21.1–21.12), 06's nine (21.13–21.21), 09's
  thirteen (21.22–21.34). Only the exponential half of Question 21.30 (09) is
  answered here, by Theorem 15.3; overlaps are cross-referenced.

## What the report does not claim

Appendix C lists every non-claim with its place: 21 from 07, 15 from 06, 16
from 09, and 6 added by the merge. In brief:

- Not refereed, not Lean-verified, no Lean mapping; AI-assisted drafts;
  priority is proposed, not certified; the literature and repository checks
  were targeted; no named published conjecture is claimed solved.
- No existence or consistency of any large cardinal, no new consistency
  result, no nontrivial `V → V`; the compactness statements are translations
  of classical principles; no large cardinal may be inferred from an
  arbitrary non-strong field map.
- The maps are proper embeddings, not automorphisms; the Kaplan–Krapp–Serra
  questions are not answered; no Kunen exception.
- The mask and embedding criteria use a coefficient operation and all subset
  masks; neither is first-order in the bare field or omnific ring; pure field
  sentences cannot detect large cardinals.
- The seed–closure converse is for set-ultrapowers; the no-descent result
  above `κ` needs an index set of size `κ`; `j(κ)` is inaccessible in `M`, not
  asserted in `V`; `H_j(No) ⊄ No^M` and `J(No) ≠ No^M` are not identifications
  (both fail for a normal-measure ultrapower).
- Transcendence, not linear disjointness, between the image fields; the
  independence theorem is over the domain equalizer and does not decide
  Question 21.6.
- The finite checks test finite identities only.
- Merge: Remark 2.9 covers inner models with the same reals only and leaves
  `dsn:q:support` open; Remark 11.6 is conditional on a measurable cardinal and
  leaves open whether a counterexample exists without large cardinals, and the
  clauses on dense images.

## Relation to the neighbouring reports

Section 20.3 gives these with labels.

- [`definable-surreals-and-omnific-integers`](../definable-surreals-and-omnific-integers/)
  (`dsn:`). Its question `dsn:q:support` recorded the inner-model instance of
  support-subfield amplification as unproved: the universes report proves
  absoluteness of arithmetic and cuts only. Lemma 2.6 here supplies omega-map
  and normal-form absoluteness for inner models with the same ordinals and
  reals, so a proper such `No^M` satisfies `dsn:eq:Khyp` and
  `dsn:thm:amplify` applies (Remark 2.9). That report now carries the
  reciprocal `dsn:rem:largecardinal` (its Remark 17.6). Inner models lacking a
  real are not covered, and the classification question stays open.
- [`omnific-preserving-automorphisms`](../../surreal/omnific-preserving-automorphisms/)
  (`opa:`). Written concurrently in batch 30, it cites this report by directory
  (writing `J` as `ĵ`) for a negative answer, given a measurable cardinal, to
  the strongness question `opa:as:q:embeddingstrong`; Remark 11.6 states and
  proves exactly the properties it uses (field embedding fixing `R`,
  preserving and reflecting `Oz`, preserving `ct`, not strongly additive, not
  onto), consistent with its automorphism theorem `opa:as:thm:main`.
- [`birthday-cutoffs-and-hereditary-sets`](../birthday-cutoffs-and-hereditary-sets/)
  (`hset:`). Its embedding correspondence (`hset:thm:embeddings`) acts on sign
  sequences as `J` does, with the same warning that `j(A)` is not `j″A`; its
  Kunen transfer (`hset:thm:kunen`) is the birthday-enriched side of Section
  19. Neither is used in the proofs.
- [`surreal-fields-across-universes`](../surreal-fields-across-universes/)
  (`univ:`). `univ:prop:absolute` is the arithmetic part of Lemma 2.6; its
  forcing themes are Questions 21.11 and 21.20. None of its questions is
  answered.
- [`transcendence-over-bounded-support`](../../surreal/transcendence-over-bounded-support/)
  (`bst:`). Order-bounded supports there, cardinality-bounded here (09's own
  comparison); neither result implies the other.
- [`set-sized-quotients-of-omnific-integers`](../../surreal/set-sized-quotients-of-omnific-integers/)
  (`osq:`). The constant-term discussion is kept apart from its quotients.
- [`independent-surreal-copies`](../../surreal/independent-surreal-copies/)
  (written concurrently in batch 30; cited by directory). It identifies `H_j`
  as its strong exponent lift and relates its linear-disjointness theorem for
  full Hahn fields to Question 21.6 without answering it, since `J(No)` is not
  a full Hahn field (Theorem 8.6). Question 21.6 stays open.

The sources' repository statements were checked at the placement and at the
time of writing: the reports they cite are unchanged since the pin except the
set-sized-quotients report (07 cites only its catalogue entry), and the
statements stand (Section 20.3).

## Provenance and corrections

Appendix D records these.

- 06's proof status records `0865f043…` as a "tree object", not asserted to be
  a commit. It is a commit ("Merge reviewed documentation after angular
  multiplicity validation").
- 07 cited Gonshor's book as Lecture Note Series 124; 06 and 09 give 110, which
  is correct. The bibliography now says 110.
- 06 links the universes and birthday reports on `main`, 07 and 09 at the pin;
  the merged bibliography keeps 07's entries.
- 06 says its short-field counting uses "regularity and uncountability"; only
  uncountability is needed (note after Corollary 3.2). Not a false statement.

**Delivered files that use delivery names or numbering.** All shipped as
delivered:

- The three proof-status files number results as in their own manuscripts.
  Main correspondences to this report: 07's Lemma 2.3/2.4, Theorems 3.3, 4.1,
  5.1, 5.4, 6.1, 7.1, 7.4, 8.1, 8.4–8.5, 9.1–9.2, 10.1, 11.3, 12.2, 12.5, 13.1
  and Section 16 are Lemma 2.5/2.6, Theorems 4.3, 5.1, 6.1, 6.4, 7.1, 8.1, 8.6,
  10.1, 10.7, 10.9, 11.1–11.2, 12.1, 14.3, 15.3, 15.7, 16.2 and Questions
  21.1–21.12. 06's Lemma 2.3 and 5.3, Theorems 3.3, 3.5, 4.2, 4.6, 5.1, 6.3,
  7.1, 8.2–8.3, 9.1–9.2 are Lemma 2.6 and 9.3, Theorems 5.1, 8.1, 5.1, 15.3,
  9.1, 9.7, 10.2, 17.2–17.3, 12.1/12.3 and 11.4. 09's Lemma 2.2 and Theorems
  4.4, 5.1, 5.2, 6.1, 7.3, 7.5, 8.1, 8.4, 9.1, 10.2, Proposition 9.2 and
  Section 12 are Lemma 2.6 (second route), Theorem 5.1, Theorems 8.1/8.4,
  Corollary 5.6 with Theorem 5.7, Theorems 11.1/12.1, 13.3, 13.5, 10.1/10.3,
  10.10, 16.1, 18.2, Proposition 16.3 and Questions 21.22–21.34. 09's proof status writes `T`, `F_κ`; 06's writes the
  snapshot as a tree object (above).
- 07's proof status names `code/finite_regression.py` and its seed; 07's text
  (Appendix B) and delivered README named the delivery layout; the shipped
  paths are prefixed.
- The three build helpers assume the original flat package layout. Each `cd`s
  to its own directory (`code/`) and looks for its manuscript
  (`article.tex`, `critical_point_defects.tex`, `surreal_large_cardinals.tex`),
  which is not there; 07's also runs `code/finite_regression.py` relative to
  `code/`. None builds this report.
- `data/07-critical-point-defects-build_validation.json` describes 07's
  delivered 32-page PDF (120 labels, no warnings), not `article.pdf` here.
- The recorded results JSON and console text are byte-identical: the program
  prints the JSON it writes.
- Run without arguments, the finite regression writes
  `data/finite_regression_results.json`, a delivery name next to the shipped
  prefixed file; run it on a copy with `--output` (below).

## Build and reproduce

TeX Live or MiKTeX with newtxtext/newtxmath, amsmath/amsthm, mathtools,
geometry, microtype, booktabs, array, longtable, enumitem, xurl, xcolor,
fancyhdr, needspace, tcolorbox and hyperref. No external figures or
bibliography file.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch directory; the auxiliary files are not kept here. The
recorded build (MiKTeX) has 80 pages and no errors, undefined references or
citations, multiply defined labels, duplicate destinations, LaTeX or package
warnings, or overfull boxes. It has seven underfull-box notices, all inside
07's two delivered tables (the literature table of Section 20 and the Lean
interface table of Appendix A), identical to a build of the placed text. A
clean compile proves nothing about the proofs.

The finite regression needs Python 3.10 or later and no packages. Run it on a
copy, from this directory:

```sh
T=$(mktemp -d)
cp code/07-critical-point-defects-finite_regression.py "$T"/
(cd "$T" && python 07-critical-point-defects-finite_regression.py --output rerun.json > console.txt)
diff <(tr -d '\r' < "$T/rerun.json") data/07-critical-point-defects-finite_regression_results.json
```

This was run for this report under Python 3.14.4 on Windows: exit code 0,
`"status": "PASS"`, and both the written JSON and the console output agree
with the recorded files except for line endings (CRLF on Windows). The seed is
20260923. The checks are 500 finite exponent-reindexing cases (three identities
each, leading terms for the 432 nonzero inputs), 251 index-deletion and shift
cases, 500 cases of the difference-of-homomorphisms product identity, all
16,384 candidate maps on the four-point Boolean algebra (exactly its 4
principal characters), and one Hadamard-versus-convolution distinction. They
model no elementary embedding, measurability, class recursion, normal-form
absoluteness, transfinite summation or supercompactness. 06 and 09 ship no
programs.
