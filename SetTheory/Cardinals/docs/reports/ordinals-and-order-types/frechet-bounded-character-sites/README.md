# Bounded-Character Fréchet Filter Sites

**Filter complexity, Booleanization, and three cardinal boundaries**

This is a research report built from two manuscripts, both dated
24 September 2026 and both prepared with ChatGPT ("Research manuscript
prepared with ChatGPT"). It continues the neighbouring report
[`frechet-two-valued-obstruction`](../frechet-two-valued-obstruction/).

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 08 (base) | batch 36, manuscript 08 | `filter_complexity_research` (inner `filter_complexity_article/`, main file `article.tex`; *Filter Complexity and Booleanization: Pseudointersection thresholds, ultrafilter atoms, and Fréchet-power sheaves*, 24-page PDF) | `e21766d04` | `1a1396d4d` | Sections 1–5, 7, 9–12, 14, 16 and 18–20, the development and its order; source 10's material is inserted into several of them |
| 10 | batch 36, manuscript 10 | `Frechet_Cardinal_Boundaries` (inner `Frechet_Cardinal_Boundaries/`, main file `Frechet_Cardinal_Boundaries.tex`; *Three Cardinal Boundaries for Fréchet-Power Completions: Pseudointersections, local decisions, and ultrafilter points*, 26-page PDF) | `e21766d04` | `1a1396d4d` | Sections 3.3, 4.2, 6, 8, 13, 15 and 17; Theorem 4.4, Corollary 4.5, Theorem 5.2, Corollary 5.3; parts of Sections 1, 7, 11, 12, 14 and 18; questions R1–R10 in Section 19 |

The archives arrived in `e13affd32`. Every result, proof, example, remark,
limitation and question of both manuscripts is printed. A result proved by
both is printed once, and its heading names both sources with their
delivered numbers (for example `[08 Thm 4.2; 10 Thm 4.3(a),(b)]`). The two
manuscripts were written independently against the same snapshot and do
not contradict each other.

**Status:** AI-assisted and unrefereed. Nothing in this report is
formalized, and placement in a repository that contains Lean and Rocq
developments confers no formal status on it (see *Relation to the
neighbouring report and to formal work* below).

```
article.tex                                    the merged report, standalone LaTeX with an internal bibliography
article.pdf                                    the compiled report, 49 pages (unnumbered title page, then pages 1–48)
README.md                                      this guide
08-filter-complexity-proof_audit.md            source 08's author-side proof audit, as delivered
08-filter-complexity-literature_audit.md       source 08's repository and literature audit, as delivered
10-cardinal-boundaries-PROOF_AUDIT.md          source 10's proof audit and scope ledger, as delivered
10-cardinal-boundaries-SOURCES.md              source 10's sources and provenance notes, as delivered
code/08-filter-complexity-verify_finite.py     source 08's exact finite Boolean checks (Python standard library)
code/08-filter-complexity-build.sh             source 08's build script (checks, then its PDF; see below)
code/10-cardinal-boundaries-build.sh           source 10's build script (its PDF only; see below)
data/08-filter-complexity-verification_results.json   source 08's recorded run of the checks
data/08-filter-complexity-qa_report.json       source 08's build and visual-inspection record
```

Neither manuscript's delivered README or PDF is shipped: this README replaces
them, and `article.pdf` is a build of the merged text. Source 10's manuscript
`Frechet_Cardinal_Boundaries.tex` is not shipped either; it survives only in
the archive committed in `e13affd32`. Source 10 supplied no verification
suite. There were no checksum manifests in either package.

## Labels and numbering

Every label in `article.tex` carries the prefix `fbc:`. Source 08's text, as
staged, had 55 labels; the merged report has **124**. Source 08's keys are
kept after the prefix, except two keys that collided with other texts:
`sec:model` (source 10 used the same key for a different section) is
`fbc:sec:early-atomicity`, and `thm:sheafification` (the neighbouring report
uses that key for its full-site theorem) is `fbc:thm:mix-sheafification`.
Source 10's material, the definitions and remarks that had no label, and the
merge's own lemmas and sections received new `fbc:` labels.

The numbering is new; Appendix A.4 of the report is a concordance from every
numbered item of both delivered PDFs to its number here. The principal ones:

| Result | Source 08 | Source 10 | Here |
|---|---|---|---|
| index shift `F_λ = P_{λ⁺}` | — | — | Lemma 2.2 (merge) |
| representation `C_κ = RO(ω*, τ_κ)` | Thm 3.3 | — | Theorem 3.3 |
| poset side, and agreement of the two descriptions | — | Lemma 2.2 | Lemma 3.4; Lemma 3.6 (merge) |
| general completion criterion | — | Thm 3.2 | Theorem 4.2 |
| marked threshold at p (forward direction) | Thm 4.2 | Thm 4.3(a),(b) | Theorem 4.3 |
| reverse barrier | — | Thm 4.3(c) | Theorem 4.4 |
| two-sided boundary | — | Thm 4.3 | Corollary 4.5 |
| closure; partition distributivity | Prop. 5.5 | Thm 5.1, Cor. 5.2 | Proposition 5.1; Theorem 5.2, Corollary 5.3 |
| h as local-reading boundary; abstract non-isomorphism | — | Thm 6.2, Cor. 6.3 | Theorem 6.2, Corollary 6.3 |
| atoms, points, atomicity | Thm 5.1, Prop. 5.2, Thm 5.3 | Thm 7.3, Cor. 7.4, Lemma 7.5, Cor. 7.6 | Theorem 7.1, Proposition 7.2, Corollary 7.3, Theorem 7.5, Corollary 7.6 |
| forcing reading of the residual part | — | Prop. 8.1 | Proposition 8.1 |
| imported Millán model; three-stage hierarchy | Prop. 6.1, Thm 6.3 | — | Proposition 9.1 (imported), Theorem 9.3 |
| mixing sheafification | Thm 8.5 | Thm 9.2 | Theorem 11.6 |
| product of ultrapowers at atomic stages | Cor. 8.7 | Prop. 12.1 (full site) | Corollary 11.10 |
| transfer; specializations | Thm 9.1 | Thm 10.1, Prop. 10.3 | Theorem 12.1, Proposition 12.3 |
| p-fold infinitary separation | Thm 9.2 | — | Theorem 12.4 |
| localized realization; countable saturation | — | Thm 11.1, 11.2 | Theorems 13.1, 13.2 |
| global rings | Thm 10.1, Cor. 10.2 | Example 11.3 | Theorem 14.1, Corollary 14.2 |
| exact sizes c, 2^c, 2^(2^c) | — | Thm 12.4 | Theorem 15.2 |
| general Boolean algebras | Prop. 11.2, 11.3 | — | Propositions 16.2, 16.3 |
| questions | Q1–Q10 | Research questions 14.1–14.10 | Q1–Q10, R1–R10 (Section 19) |

Paragraphs written for the merge are set as unnumbered *Merge notes*; the
merge also wrote Lemmas 2.2 and 3.6, Sections 1.2, 1.5 and 1.6, Section 5.1
(the closure scope) and Appendix A.

## Setting and notation

Free filters on ω are proper filters containing the cofinite filter Fr, ordered
by strengthening (a larger filter is a stronger condition) with the dense
topology. The report uses **source 08's indexing** throughout:
`P_κ = {F : χ_*(F) < κ}`, where `χ_*` counts generators *modulo Fr*, strictly
below κ, and `C_κ` is the Booleanization. Source 10 bounds the ordinary base
character *weakly*: `F_λ = {F : χ(F) ≤ λ}`. Lemma 2.2 proves
`χ_* ≤ χ ≤ max(χ_*, ℵ0)`, hence **`F_λ = P_{λ⁺}`**: source 10's stages are
the successor stages here, and source 08 has further stages (`P_ω` and the
limit stages, for example `P_{ℵ_ω}`, which is no `F_λ`).

Every statement taken from source 10 is translated. The full dictionary is the
table of Section 1.6; the translations that matter most:

| Source 10 | Here | Note |
|---|---|---|
| `λ < p` (marked completion survives) | `κ = λ⁺ ≤ p` | |
| `λ ≥ p` (barrier) | `κ = λ⁺ > p` | **not** `κ ≥ p`: `P_p` is still stable |
| atoms "at u" | first atoms at `P_{u⁺}` | same statement, two indexings |
| `λ ≥ h` | successor `κ = λ⁺ > h` | |
| `𝔻_λ = RO(F_λ)`, `j_λ` | `C_{λ⁺}`, `e_{λ⁺}` | Lemma 3.6 |
| `ℂ`, `i` (the one completion of `P(ω)/Fin`) | `C_ω`, `e_ω` | a bare `ℂ` is never used |
| cone `⟨F⟩`; `fil(·)` | `↑F` (poset) or `K_F` (in ω*); `⟨·⟩` | `⟨·⟩` is the generated filter here, as in the earlier report |
| `U_λ`, `U` | `S_{λ⁺}`, `ω*` | `S_κ` is a set of ultrafilters here |
| `S_λ(A)`, `S_λ(A;d)` | `Mix_M(1)`, `Mix_M(w)` at stage `λ⁺` | |
| admissible site `P` | `𝒬` | `ℙ` is reserved for stages |

Renamed in source 08's own text: its comparison map `h` is `J` (to keep `𝔥`
free), its field `K` is `𝔽` (to keep `K_F` free), and its abbreviation
`ℂ = ℂ_κ` in the mixing section is written out. No normalization changed.

**Closure-based results are stated only at the successor stages.** Source
10's corollary on local decisions, its forcing reading, simultaneous raw
representatives, localized realization and countable saturation, and the
abstract non-isomorphism above h all use its closure theorem, which holds at
`P_{λ⁺}`. At a singular stage of countable cofinality such as `P_{ℵ_ω}` the
union of a countable chain can need ℵ_ω generators and lie outside the site;
those results are **not** proved there (Section 5.1). They are not claimed at
regular limit stages either. Through the marked isomorphism `C_ω ≅ C_{ℵ1}`
they apply to `C_ω`. The reverse barrier uses no closure; source 10 states it
for `λ ≥ p`, and the report states it for every `κ > p` after re-reading the
proof (merge note after Theorem 4.4). The same is done, and said, for three
other source-10 statements whose proofs use no closure: the cone lemma
(Lemma 3.4), the residual formula of Theorem 7.5 and ordinary
specializations (Proposition 12.3).

## What the report claims

All in ZFC, with ordinary proofs; one application imports a forcing model.

- **Representation (08).** `C_κ` is the regular-open algebra of the topology on
  ω* generated by the sets `K_F`, `F ∈ P_κ`, and
  `Sh(P_κ, dense) ≃ Sh(C_κ)` (Theorem 3.3). `C_ω = RO(ω*)`,
  `C_{c⁺} = P(ω*)`.
- **The p threshold, forward (08; 10 at its stages).** `P(ω)/Fin` stays order
  dense in `C_κ` exactly for `κ ≤ p`; for `κ > p` there is no complete Boolean
  homomorphism `C_ω → C_κ` fixing the original events (Theorem 4.3). The
  first zero-to-positive meet has arity exactly p (Proposition 4.9).
- **The reverse barrier (10).** For `κ > p` there is no complete Boolean
  homomorphism `C_κ → C_ω` fixing the original events either (Theorem 4.4).
  The **two-sided** boundary (Corollary 4.5) is source 10's; source 08's
  barrier is one-sided.
- **h (10).** h is the least size of a family of completed binary events of
  `C_ω` that cannot be decided jointly on a dense set (Theorem 6.2); at every
  successor stage `κ > h`, `C_κ ≇ C_ω` even abstractly, recovering `p ≤ h`
  (Corollary 6.3).
- **Atoms and points (08, 10).** Atoms of `C_κ` are the singletons of
  ultrafilters with fewer than κ generators; `C_κ` is atomless and pointless
  exactly for `κ ≤ u` (Theorem 7.1, Proposition 7.2); full atomicity is an
  extension property, with an atomic/atomless decomposition and a poset-side
  formula for the residual part (Theorem 7.5).
- **Forcing reading (10).** Forcing with `P_{λ⁺}` adds no new λ-sequences; the
  generic ultrafilter is old on the atomic part and new, of character > λ, on
  the residual part (Proposition 8.1).
- **Early atomicity (08), relative to an imported model.** In Millán's model
  (`c = 2^{ℵ1} = ℵ2`), `C_{ℵ1}` is atomless, `C_{ℵ2} ≅ P(c)` and
  `C_{ℵ3} ≅ P(2^c)` (Theorem 9.3). **Millán's forcing construction is
  imported (Proposition 9.1), not reproved.**
- **Mixing sheafification (08, 10).** The associated sheaf of `F ↦ M^ω/F` on
  `P_κ` is given by Boolean mixtures of raw sequences (Theorem 11.6); at every
  atomic stage it is a product of ultrapowers (Corollary 11.10).
- **Model theory.** Finitary transfer with attained existential values (08, 10;
  Theorem 12.1); ordinary specializations (10; Proposition 12.3); a p-fold
  conjunction separates the stages (08; Theorem 12.4); at the successor
  stages, localized countable realization and countable saturation of every
  ultrafilter specialization, ℵ1-saturation in a countable language (10;
  Theorems 13.1, 13.2).
- **Rings (08).** Global rings over a field are von Neumann regular with
  idempotent algebra `C_κ`; for `κ ≤ u` they are not full products of fields
  (Theorem 14.1, Corollary 14.2).
- **Sizes (10).** For `2 ≤ |M| ≤ c`: `c` raw, `2^c` at the countably generated
  stage, `2^(2^c)` at the full site (Theorem 15.2).
- **General Boolean algebras (08).** The forward threshold for any Boolean
  algebra is its centered-family invariant `𝔭(B)` (Proposition 16.2), and
  order density of an inclusion of stages gives a canonical comparison
  (Proposition 16.3).

### Where one source answers the other

- Source 08's Theorem 9.3 answers the second clause of source 10's research
  question 14.2 (R2: can the small-character extension property hold strictly
  below c?) positively, **relative to the imported model**. R2 is re-scoped.
- Source 10's Theorem 11.2 (Theorem 13.2 here) answers the "useful first
  target" of source 08's Q6 (countable types in a countable language). Q6 is
  re-scoped to types of size at least ℵ1, and to the limit stages.
- Source 10's Corollary 6.3 answers source 08's Q4 (marked versus unmarked)
  negatively, for the comparison with `C_ω`, at the successor stages above h;
  Theorem 7.1 (atoms) already does so at every stage `κ > u`. For that
  comparison Q4 is re-scoped to the stages `p < κ ≤ u` that Corollary 6.3
  does not reach: the successor stages `κ ≤ h` (R1) and the limit stages.
  Q4's comparison of two stages other than ω with each other is not addressed
  by source 10 and stays as stated.
- Source 08's Propositions 11.2 and 11.3 partly address source 10's
  questions 14.9 and 14.4 (R9, R4).

## What the report does not claim

- It does not re-claim the neighbouring report's results: the two-valued
  nongluing theorem, the failure on the countably generated site,
  separatedness, finite pasting, the local finite-quotient classification and
  the full-site product sheafification are that report's. Separatedness and
  the full-site product are reproved here only to connect them.
- The p, u and h characterizations translate classical cardinal
  characteristics; no new value, inequality or independence result for them is
  claimed. Recovering `p ≤ h` is a consistency check. The mixing/sheaf method
  is prior work (Pierobon–Viale); the full-site power-set identification is
  Massas's canonical extension; Blass is used for terminology only.
- The comparison barriers are **marked**: they fix the original events. They
  do not exclude an unmarked abstract isomorphism, except where Corollary 6.3
  applies; the finite–cofinite toy model (Proposition 10.1) shows why the
  qualifier matters. They do not assert that the identity on ω* induces a
  locale morphism.
- Atomicity is not deduced from `u < κ`; existence of small ultrafilters is not
  claimed to imply their density.
- Closure is proved only for regular κ; source 10's closure consequences only at
  the successor stages. Nothing is claimed at singular stages (question Q5).
- Transfer is finitary. Saturation is claimed only for countable types, only at
  the successor stages and `C_ω`, and only for these specific models; no
  saturation above ℵ1 is claimed. The p-fold conjunction says nothing about
  realizing types of size p.
- The no-product theorem excludes **full** direct products only, not subdirect
  representations; the global ring is not claimed to be a field; ordinary ring
  homomorphisms are not constrained.
- The sizes are cardinal comparisons, not a chain of complete embeddings. The
  CH section is a conditional example, and the separated-characteristics
  statements are implications, with no consistency results.
- The forcing reading does not assert that intermediate stages are isomorphic
  or identify the residual forcing uniquely.
- The finite checks run on finite Boolean algebras `P(n)`; they are not free
  filters on finite sets and prove nothing about p, u, uncountable character
  or consistency.
- The choice-free guarantees of the neighbouring report are not extended; this
  report works in ZFC.
- Novelty and priority are not certified. Both sources' literature searches
  were targeted, not exhaustive, and the questions are proposals, not
  documented open problems.
- Neither source changed the repository, and source 08 submitted nothing and
  contacted no author.

## Relation to the neighbouring report and to formal work

The report continues the non-claim of
[`frechet-two-valued-obstruction`](../frechet-two-valued-obstruction/) about
other filter sites (its `article.tex`, end of Section 10):

> "It is not an assertion that every sheaf-based construction of nonstandard
> analysis fails, or that every reduced-power presheaf on a different filter
> site has the same behavior."

It answers no question that report names; that report's one question
(whether the infinite-quotient direction of its Theorem 8.5 needs dependent
choice) remains open, and is recorded beside R8. The neighbouring report's
`article.tex` was unchanged from the pin `e21766d04` to the placement commit
`1a1396d4d`; a short remark pointing here was added to it when this report was
written (batch 36 reciprocal notes).

Nothing here is formalized. The `SetTheory/Cardinals` Lean library concerns
exacting and cover-exacting large cardinals and contains no declaration about
filter sites, pseudointersections or reduced powers; no Lean or Rocq file in
ProveIt formalizes any statement of this report. Being filed in the Cardinals
research-report collection, beside that library, confers no formal status.

## Build

MiKTeX or TeX Live with pdfLaTeX, the newtx fonts, amsmath/amssymb/amsthm,
mathtools, geometry, microtype, booktabs, array, longtable, enumitem, xcolor,
titlesec, fancyhdr, tcolorbox, xurl, hyperref, bookmark and needspace. No
external figures, bibliography database or downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Build in a scratch copy so that no auxiliary files land here. The recorded
build (MiKTeX 26.2, pdfTeX 1.40.29) has 49 pages and no errors, LaTeX or
package warnings, undefined references or citations, multiply defined labels,
duplicate destinations, or overfull or underfull boxes. Source 08's delivered
text builds equally cleanly to 24 pages with the same toolchain. Identical PDF
bytes across TeX installations are not promised (source 08's own caveat).

The shipped build scripts are the delivered bytes and do not work under the
shipped names:

- `code/08-filter-complexity-build.sh` runs
  `python3 verify_finite.py --output verification_results.json` and pdflatex
  on `article.tex` in its own directory (`code/`), where neither
  `verify_finite.py` nor `article.tex` exists under that name; run in place it
  would also overwrite evidence. Do not use it.
- `code/10-cardinal-boundaries-build.sh` builds
  `Frechet_Cardinal_Boundaries.tex`, which is not shipped.

## Reproduce the finite checks

Source 08's checks need Python 3.10 or later and no third-party packages. Run
them on a copy, with an explicit output path, so that the shipped evidence is
never overwritten:

```sh
mkdir -p /tmp/fbc-rerun && cp -r code data /tmp/fbc-rerun/ && cd /tmp/fbc-rerun
py code/08-filter-complexity-verify_finite.py --output fresh.json
tr -d '\r' < fresh.json | cmp - data/08-filter-complexity-verification_results.json
```

(`py` is the Windows launcher; use `python3` elsewhere.) A rerun on
2026-09-28 (Python 3.14.4) exited 0 in about 2 s. On Windows the script writes
CRLF line endings (970 bytes against the shipped 932); after stripping CRs the
output is byte-identical to the shipped JSON. The script also prints the same
JSON to standard output. The recorded counts are those of Section 18.3 of the
report: 284 filter pairs, 33,508 relative families, 332 sieves, 189 dense
sieves, 65,812 candidate frame-point maps, 507,348 mixture comparisons, 363
generalized inverses, 1,364 idempotent pairs, 360 existential instances with
22,140 candidate witnesses, and the internal/external `F_3^2` example.

## Delivered files and their delivery names

The audit, provenance and data files are byte-identical to the delivery and
still use delivery names and the delivered PDFs' numbering:

- `08-filter-complexity-proof_audit.md` cites source 08's delivered numbers
  (Lemma 2.2 … Proposition 11.3) and says that numbering "should be read from
  article.tex if the document is edited"; use Appendix A.4 of the report.
- `08-filter-complexity-literature_audit.md` cites delivered numbers
  (Proposition 6.1) and records the neighbouring report's `article.tex` blob
  `adaccd18…`, which is still that file's blob at the placement commit.
- `data/08-filter-complexity-qa_report.json` describes the delivered 24-page
  PDF (TeX Live, Python 3.13.5), which is not shipped.
- The delivered README of source 08 (replaced by this one) pointed to "Section
  12.2" for the check list; that list is Section 18.3 here.
- `10-cardinal-boundaries-PROOF_AUDIT.md` cites source 10's delivered numbers
  (Theorems 4.3, 5.1, 7.3, 9.2, 10.1, 11.1–11.2, 12.4; Corollary 6.3) and
  says all 26 pages of the delivered PDF were rendered; that PDF is not
  shipped. Its statements are in source 10's indexing (`κ < p` there is
  `κ⁺ ≤ p` here).
- `10-cardinal-boundaries-SOURCES.md` describes source 10's own package
  ("Only the new manuscript and its support files are packaged").

## Provenance

- **Manuscripts.** Two, batch 36 manuscripts 08 and 10, both pinned to
  `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9`, arrived in `e13affd32`, placed in
  `1a1396d4d` as a new merged report because both continue the neighbouring
  report's non-claim about other filter sites but answer no question it names.
- **Contributions.** Source 08: the indexing, the representation, the forward
  threshold, arity, atoms/points/atomicity, the Millán application, the toy
  model, the mixing sheaf at every stage, transfer, the infinitary separation,
  rings, general Boolean algebras, the finite checks, Q1–Q10. Source 10: the
  poset-side description, the general criterion, the reverse barrier, closure
  consequences, h, the forcing reading, specializations and countable
  saturation, exact sizes, the consolidated regimes, R1–R10.
- **Where the merge chose.** Source 08 is the base (its indexing strictly
  contains source 10's stages). Source 10's closure-based results are stated
  at successor stages only; its reverse barrier at every `κ > p`. Where both
  proved a result the printed proof is source 08's, except that source 10's
  general criterion, its dense-join proof of the forward failure and its
  poset-side atom proof are kept as second routes; its sheafification proof,
  point lemma, full-site product and independent family repeat source 08's and
  are credited. Appendix A of the report lists every choice.
- **Checks.** At intake both manuscripts were read in full and no error was
  found; the imported Millán properties were compared with Millán's
  Definition 2.1 and the proof of his Theorem 3.14 (he cites an earlier paper
  for them), and Pierobon–Viale arXiv v6 (23 July 2026) was confirmed to
  exist. In the write, the reverse barrier and the residual formula were
  re-read for hidden uses of closure, and the index shift was proved.
