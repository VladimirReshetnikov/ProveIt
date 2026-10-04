# Naming Elementary Embeddings

**Atom components, Replacement and reflection: exact criteria and sharp
cofinality thresholds**

A research report dated October 2026, built from one manuscript on
expanded-language axiom schemes in urelement set theory, prompted by Elliot
Glazer and Bokai Yao's *Reflection Principles in ZFU* (arXiv:2602.21970) and
Glazer's *Global choice is not conservative over local choice for Zermelo set
theory* (arXiv:2312.11902). Its author lines read "Prepared for Vladimir
Reshetnikov" and "Research manuscript prepared with ChatGPT".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 89, manuscript 05 | `Naming_Elementary_Embeddings_Research.zip` (330,868 bytes; inner directory `Naming_Elementary_Embeddings/`, main file `article.tex`, 1041 lines, 27-page US Letter PDF), arrival commit `8ea27d6c0` | `2b7b388ba` (`2b7b388ba81a3355b19a7c2d2fe797e92f572355`, "Catalogue batches 81 to 86", quoted in Section 9.1 and in the repository URLs of the bibliography) | `23adb85f9` | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection, beside the formal projects it continues, confers no formal
status. Its finite checks were executed (by the package and again at the
write); its infinite theorems rest on the written proofs only. **Historical
priority is not established.**

## The question

Let `A` be an external set of atoms, `κ` an infinite cardinal with `|A| ≥ κ`,
and `M_κ(A)` the objects whose transitive closures involve fewer than `κ`
atoms: Yao's kernel-ideal model of urelement set theory with Replacement and
choice (`ZFCU_R`, without Collection). Every injection `f : A → A` lifts to a
canonical amenable elementary self-embedding `j_f` fixing every pure set.
When finitely many such lifts are *named*, so that axiom schemes range over
formulas containing their symbols, which set-existence schemes survive?

## What it proves

- **Theorem 2.4** (Yao's theorem, specialized and credited): `M_κ(A)` satisfies
  `ZFCU_R`; internal and external cardinalities agree.
- **Theorems 3.2, 3.4, Proposition 3.5:** the lifts `j_f` are elementary and
  amenable; the initial elementary self-embeddings are exactly the `j_f`;
  `M_κ(C) ≼ M_κ(A)` iff `|C| ≥ κ`. **Theorem 3.6:** `j_f` is
  parameter-definable iff `f` moves fewer than `κ` atoms.
- **Lemma 4.1:** countably many component types for one injection, continuum
  many for two (already for two permutations).
- **Theorem 5.1 (component-profile criterion, the principal claim):** for
  `κ > ω`, Replacement in the expanded language holds iff the union
  `D_κ(f)` of the small type blocks has size `< κ`; for `κ = ω`, iff every
  component is finite and `D_ω(f)` is finite.
- **Theorem 6.1:** every one-name expansion preserves Replacement iff
  `cf(κ) > ω`; every expansion by `r ≥ 2` names iff `cf(κ) > 2^ℵ0`.
  **Corollary 6.3:** at the cutoff `ℵ2`, universal two-name preservation is
  equivalent, externally, to CH; a characterization, **not a proof or
  refutation of CH**. **Corollary 6.4:** the same threshold for countably many
  names.
- **Lemma 7.2, Corollaries 7.3 and 7.6, Theorem 7.5:** the exact domain-size
  spectrum of Collection, with failure at limit cutoffs already in the
  `Δ0` fragment of the base language; full Collection iff `κ` is an
  uncountable successor and fewer than `κ` component types are realized.
  **Theorem 7.7:** full transitive reflection has the same criterion.
  **Corollary 7.9:** two individually safe automorphisms can be jointly unsafe
  (at `ℵ1`); Example 7.10: joint Replacement can survive while joint
  Collection fails.
- **Proposition 8.1:** two superficially similar partial-reflection schemes
  differ (one is `Δ0` Collection).
- Section 9: a six-layer ProveIt formalization route (a proposal); Section 10:
  twelve research questions; Appendices A (an explicitly bounded
  injection-to-atoms formula), B (dependency audit), C (finite checks).

## What is not claimed

- The kernel-ideal construction is Yao's (Definition 24, Theorems 26–27 of
  arXiv:2303.14274), credited; the lifting idea is not claimed new. The
  component-profile criterion and its consequences are proposed
  contributions, unreviewed, with literature priority unverified.
- No Lean development; Glazer and Yao are cited researchers, not authors or
  endorsers. No open problem of Glazer's is claimed solved, and the
  choiceless separation diagram of Glazer–Yao is neither reproduced nor
  contradicted.
- The models are defined externally over a set of atoms in a well-founded
  ambient universe **with choice**; the atoms are internally a proper class.
  Elementarity and reflection are schemes; no truth predicate and no set of
  all class maps are assumed.
- The classification is local to this model family: not all urelement
  models, all amenable classes, or all elementary embeddings (noninitial
  embeddings are not classified).
- The CH corollary is a characterization only; nothing contradicts results
  about embeddings of pure universes.
- The finite Python checks are regression tests of component swaps and the
  real-marker coding, **not** verification of any infinite-cardinal theorem,
  of Replacement, or of any independence claim. The PDF build is not claimed
  bit-reproducible.

## Checks made at the write

On 3 October 2026:

- **Repository claims.** The three files the manuscript read are
  byte-identical at the pin and at the write:
  `SetTheory/ZF/Lean/ZF/Zf.lean` (blob `b33db57cf`),
  `SetTheory/BoundedConsistency/README.md` (`ebb5d1bfa`) and
  `Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings/README.md`
  (`554357db9`). The manuscript's descriptions of them (Sections 1.1, 8, 9.1)
  are accurate: the declarations `Sep_form`, `Func_form`, `Image_form`,
  `Repl_form`, `ZFax`, `ZFprov`, `ZFax_s` exist; the bounded-consistency
  README states a numeralwise endpoint reached by partial satisfaction
  rather than reflection, and says its quantifier-group rank is strictly
  finer than the Levy hierarchy; the self-embedding report is marked
  unrefereed and not formalized. No repository statement is contradicted;
  nothing needed retraction.
- **arXiv.** arXiv:2602.21970 (Glazer–Yao) lists one version, v1 of
  25 February 2026 (math.LO), with the cited title and authors;
  arXiv:2303.14274 (Yao) lists three versions, the cited v3 of 18 June 2023;
  arXiv:2312.11902 (Glazer) lists three, the last of 7 January 2024. The
  page references to Yao's dissertation were not rechecked.
- **Delivered hashes.** `data/BUILD_AUDIT.json` lists seven delivered files;
  all seven hashes match the delivery, and the four of them shipped
  unchanged (`SOURCE_AUDIT.md`, `code/build.sh`, `code/verify_finite.py`,
  `data/verification_results.json`) still match; the record does not list
  itself.
- **Finite checks** rerun on a scratch copy (Python 3.14.4, under a second):
  125,582 assertions passed; the report equals the recorded one except for
  `python_version` (3.14.4 against the delivered 3.13.5).
- **Personal data.** `SOURCE_AUDIT.md` mentions that "the requested LinkedIn
  page did not provide usable content"; it gives no URL, and no LinkedIn URL
  or e-mail address is in any shipped file.

## Relation to the repository

**Formal status.** No statement is formalized in Lean or Rocq, and no
urelement theory is formalized anywhere in ProveIt. The report continues two
formal projects without adding to them:

- `SetTheory/ZF` formalizes pure first-order ZF:
  `SetTheory/ZF/Lean/ZF/Zf.lean` (a port of `SetTheory/ZF/Coq/Zf.v`, which
  declares `Sep_form`, `Repl_form`, `ZFax` and `ZFax_s` likewise) gives the
  schema constructors above, the bridges `bridge_Sep` and `bridge_Repl`, and,
  inside every model of Extensionality, Separation, Pairing, Union, Infinity
  and Replacement, the closure theorem `ClosureFO_of_ZF`.
- `SetTheory/BoundedConsistency` proves, by partial satisfaction, the
  numeralwise endpoint `BoundedZFCConsistency.Endpoint.zfc_proves_conZFC`
  (`ZFC ⊢ Con_n(ZFC)` for each metatheoretic `n`) for pure ZFC.

Both use the formula type `Form` of
`Logic/FirstOrder/Lean/FirstOrder/Fol.lean`, which has only the atomic
formulas `∈` and `=`: there is no atom predicate and there are no function
symbols, so neither the base language `{∈, At}` nor the expanded languages of
this report exist there. The "first task" and the six layers of Section 9
are proposals, and the report's Questions on bounded consistency with atoms
and on a Lean interface for failed scheme instances are open in ProveIt.

**Review in the Hilbert's-tenth research tree.** Before placement, another
session routed all five batch-89 archives (commit `6aadaa4f2`):
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_topology_surreal_arrivals_20261003.md`,
with the receipt `review_topology_surreal_arrivals_20261003.json` beside it.
For this manuscript it read the delivered README, the source audit, the
recorded finite-check scope and the delivered `article.tex` lines 118–133,
183–211, 807–865, 911–927 and 988–994 (abstract, Section 2.1 through
Remark 2.1, Section 9, the last two questions with the conclusion,
Appendix C). It records that "finitely many names" is a language parameter,
not a bound on Diophantine witnesses, that the finite checks are regression
evidence only, and that the proposed formalization is not an implemented
compiler; the Hilbert's-tenth programme's 84-operation universal polynomial
is unaffected. It claims no theorem audit, literature check or replay, and
made no correctness finding; no scope correction was needed.

**The same Collection theorem in a surreal report.** Batch-89 manuscript 03,
*Surreal Cuts, Replacement, and Atom-Support Spectra*, written against the
same pin and placed in the same commit, became Part VI of
`Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets`
(labels `hset:zr:`, written concurrently with this report). For the same
kernel models (written `M^ker_κ` there, manuscript 03's `M_κ`) it proves, in
its delivered numbering (Part VI numbering in brackets), kernel confinement
(Lemma 9.1 [32.1, `hset:zr:lem:confinement`] = Lemma 2.3 here), the base
model theorem (Theorem 9.2 [32.2, `hset:zr:thm:supportbase`] = Theorem 2.4)
and the Collection spectrum (Lemma 10.1, Theorems 10.2–10.3, Corollary 10.4
[Lemma 33.1, Theorems 33.2–33.3, Corollary 33.4,
`hset:zr:cor:classification`]; that report's Remark 24.6, `hset:zr:rem:nee`,
records the overlap): the unexpanded case (`f = id_A`) of
Lemmas 7.1–7.2, Corollary 7.3 and Theorem 7.5 here. The two proofs are
independent and **both stand**; neither manuscript cites the other or
claims priority for the unexpanded spectrum. They differ in the failing
instance (manuscript 03 collects atom sets of prescribed cardinalities;
this report a `Δ0` injection graph, Appendix A, so its failure is one of
`Δ0` Collection) and in the successor case (this report's reservoir must
consist of whole components so that the permutations commute with the named
maps). Manuscript 03's Theorem 11.2 (Theorem 34.2 there), naming an enumeration `e : κ → A_0` of
`κ` atoms, makes Replacement fail at `cf κ`, even at `ℵ1`, where every
one-lift expansion here keeps full Collection; no conflict, since `e` is not
an elementary lift. The dated note after Corollary 7.6 of the article gives
the details. Part XV of
`Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders`
(batch-89 manuscript 01) finds the same cofinality threshold for class
Replacement in the full-class rank models `(V_λ, P(V_λ))`: different models,
no shared proof.

**Named group actions at the finite cutoff (batch 90).** Part VIII of the
same surreal report (its source 12, batch-90 manuscript 05, *Named Symmetries
and Replacement*, labels `hset:ns:`; pinned to `8dc2592e9`, an ancestor of
this report's placement, so it does not cite this report) proves at the finite
cutoff the Replacement criterion for uniformly named actions of arbitrary pure
set-sized groups; for finitely many named permutations its Theorem 58.1
(`hset:ns:thm:full`) is Theorem 5.1(2) here (independent proofs, neither
claimed first; this report also covers non-surjective injections and every
uncountable cutoff). It adds the graded levels `R_k` (Theorem 59.1), the
observation that the one-cycle-of-each-length example of Example 5.5
satisfies every `R_k` (Theorem 60.1, Example 60.2), two involutions realizing
every finite level (Theorem 61.3, a finite-cutoff counterpart of Corollary
7.9), and the survival of pure-valued Collection under every such naming
(Theorem 63.1). A dated note at the end of Section 5 records this. Its
Questions 65.1, 65.3, 65.6 and 65.12 are the finite-cutoff counterparts of
Questions 10.7, 10.5, 10.9 and 10.12 here, and its Question 65.4 meets
Question 10.4; Theorems 5.1(1) and 6.1 answer its Question 65.2 in part, and
Theorems 7.5 and 7.7 its Question 65.11, for finitely many named injections
(a sentence added to the note "Status of the questions" of Section 10).

**Neighbouring reports.**

- `birthday-cutoffs-and-hereditary-sets`, subsection "Transfer of Kunen's
  inconsistency" (`hset:sub:kunen`, Theorem `hset:thm:kunen`): no nontrivial
  class elementary self-embedding of the birthday-expanded surreal class,
  under Kunen hypotheses that admit the embedding as a class parameter in
  Separation and Replacement. Here nontrivial amenable elementary lifts exist
  and naming them may or may not keep Replacement (Theorem 5.1); no conflict,
  since every `j_f` fixes the whole pure universe. A dated note at the end of
  that subsection (4 October 2026, batch 89) records this report's lifts
  (Theorems 3.2, 3.4, 5.1) there. Part VII of the same
  report (batch-89 manuscript 04) works in choiceless permutation models with
  atoms, on surreal coding and universality; it shares no theorem with this
  report.
- `Algebra/SurrealNumbers/docs/surreal/surreal-self-embeddings` (cited as a
  "control example", Section 1.1; its Remark `sse:pf:rem:kunen` makes the
  analogous point for field self-embeddings; a dated note after that remark,
  4 October 2026, records this report).
- Not to be confused with Part X of
  `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic`
  (batch 89, the same batch), whose "elementary embeddings" are embeddings of
  models of Presburger arithmetic, not of set-theoretic universes; the two
  share no theorem.
- In this category, `../measurable-box-games/` also answers a Glazer paper
  and cites arXiv:2312.11902 but shares no theorem or notation;
  `../lexicographic-well-orderings-of-reals/` concerns pure ZFC. Apart from
  Parts VI–VIII of `birthday-cutoffs-and-hereditary-sets` (above) and Part XII
  of `polish-models-of-omnific-arithmetic` (batch 90, which cites Glazer–Yao
  as context for its class theory without Foundation), no report in ProveIt
  treats urelements or cites Glazer–Yao or Yao's dissertation. (Corrected 4
  October 2026, batch 90: this sentence had said "no other report", which was
  already stale for Parts VI–VII; the article's sentence in Section 1.4 named
  them and gains a dated note for Parts VIII and XII.)

**Stale claims.** None. The manuscript's repository statements are true at
the pin and at the write.

## Notation

`M_κ(A)` (Part VI of `birthday-cutoffs-and-hereditary-sets` writes `M^ker_κ`,
manuscript 03's `M_κ`, for the same class; not the rank models `M_λ` of `surreal-well-orders` Part XV
nor the Presburger models `M_α` of `polish-models-of-omnific-arithmetic`),
`N_{κ,f}`, `ker`, `mov`, `ZFCU_R`/`ZFU_R` (R = Replacement), `B_t`,
`D_κ(f)`, `I(f)`, `H` (a protected set of atoms, not `H_κ`), `V`,
`V_α(C)`, `Collection_{≤μ}` (manuscript 03 writes `Collection_{<τ}`),
`Rob_r`, `RP`, `𝔠`; "limit cardinal" includes `ω`. The table of Section 1.5
fixes each one, with the tempting false reading. No symbol was renamed.

## Labels

Every label carries the prefix `nee:`. The manuscript's 64 labels were
prefixed before anything cited them and every reference updated (38 `\cref`
keys, 13 `\eqref`); the write added two (`nee:sec:provenance`,
`nee:sec:notation`): 66 labels. No section, theorem or equation number of the
manuscript moved (checked against a build of the delivered source); the two
new subsections are 1.4 and 1.5.

The writing step also:

- added dated `[write]` notes: Section 1.4 (provenance, pin and repository
  claims, formal status, the Hilbert's-tenth review, manuscript 03,
  neighbouring reports, the arXiv records), Section 1.5 (notation table),
  after Corollary 7.6 (the second proof of the unexpanded spectrum), at the
  end of Section 9.1 (formal status), after the questions of Section 10
  (their status) and in Appendix C (shipped layout and replay);
- added a one-line `[write]` pointer on the title page;
- wrapped the title page in `\hypersetup{pageanchor=false}` … `=true`: the
  delivered source, rebuilt with MiKTeX, gave a duplicate `page.1`
  destination;
- set the `[write]` notes ragged right, so that the long repository paths
  leave no underfull lines.

No statement, proof, number or non-claim of the manuscript was changed.

## Files

```text
README.md                         this guide (replaces the delivered README.md, staged under this name)
SOURCE_AUDIT.md                   delivered source and proof audit: literature used, pin, files inspected, limits
article.tex                       the report (delivered article.tex; labels prefixed, [write] notes)
article.pdf                       compiled report, 31 pages (unnumbered title page, pages i-ii, then pages 1-28)
code/build.sh                     delivered three-pass pdfLaTeX build of the article.tex in its own directory
code/verify_finite.py             finite regression checks: component swaps and real-marker coding (standard library)
data/verification_results.json    recorded run of verify_finite.py (Python 3.13.5, 125,582 assertions)
data/BUILD_AUDIT.json             delivered build record: engine, PDF checks, visual review, hashes of the seven delivered files
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery; placement moved `build.sh` and
`verify_finite.py` to `code/` and the two JSON files to `data/`. Not shipped:
the delivered 27-page `article.pdf` (300,041 bytes) and the delivered README
(this file replaces it). The package had no checksum manifest, and nothing
was excluded as heavy. Both survive in the archive:
`git show 8ea27d6c0:docs/incoming/Naming_Elementary_Embeddings_Research.zip > <scratch>/Naming_Elementary_Embeddings_Research.zip`.

Delivered text that names the delivery layout or a file not shipped:

- `code/build.sh` changes to its own directory and builds the `article.tex`
  there, then copies `article.pdf` beside it: run in place it fails (there is
  no `code/article.tex`); run it on a copy (below).
- `data/BUILD_AUDIT.json` records the delivered 27-page PDF, the delivered
  `article.tex` (now rewritten), the delivered `README.md` and `article.pdf`
  (not shipped) by their flat names and hashes, and "no final-pass
  warnings" under TeX Live 2025; under MiKTeX the delivered source gives
  one duplicate-destination warning (see Labels).
- `data/verification_results.json` names no paths; its `script_sha256` is
  the hash of the shipped `code/verify_finite.py`.
- The article's Appendix C names `verify_finite.py` and the JSON file by
  their delivered names; a note there gives the shipped paths. The delivered
  README told readers to run `bash build.sh` and
  `python3 verify_finite.py --output verification_results.json` in one flat
  directory.
- `SOURCE_AUDIT.md` says the repository was inspected "through the GitHub
  connector" at the pin; it names repository paths only.

## Rerun the checks

`verify_finite.py` without arguments only prints its report, so it can run
in place; with `--output` it writes the file named, so never point that at
`data/`. Python 3.10 or newer, standard library only. From this directory,
in Git Bash (on a POSIX host use `python3` for `py`):

```sh
py code/verify_finite.py                     # read-only; prints "status": "passed"
T=$(mktemp -d)
py code/verify_finite.py --output "$T/verification_results.json" > /dev/null
tr -d '\r' < "$T/verification_results.json" | diff - data/verification_results.json
```

At the write (3 October 2026, Python 3.14.4, Windows) the run took under a
second and the only difference was the `python_version` line (3.14.4 against
3.13.5). The recorded run covers all permutations on at most seven points
(5,913 structures), all ordered pairs of permutations on at most five points
(15,017), 4,456 isomorphic component swaps, the 64 six-bit marker codes and
69,632 marker-translation cases.

## Build the PDF

pdfLaTeX with mathpazo, geometry, amsmath/amssymb/amsthm/mathtools,
microtype, aliascnt, booktabs/tabularx/array/longtable, enumitem, xcolor,
fancyhdr, hyperref and cleveref; the bibliography is inline. Build in a
scratch copy, either way:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

```sh
B=$(mktemp -d); cp article.tex code/build.sh "$B/"; cd "$B"; bash build.sh
```

The committed PDF was built the first way with MiKTeX: 31 pages (30 before
the batch-90 reciprocal notes, 4 October 2026); no errors
or warnings, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations, no overfull or underfull boxes. The
delivered `build.sh` on a copy also succeeded (30 pages, before the batch-90
notes; not rerun since). The delivered
source, built the first way, gives 27 pages and one duplicate-destination
warning (`page.1`), removed as described under Labels.

## Provenance

- Sources cited by the manuscript: Glazer–Yao, arXiv:2602.21970v1; Glazer,
  arXiv:2312.11902v3; Yao, *Set Theory with Urelements*, doctoral
  dissertation, University of Notre Dame, 2023 (arXiv:2303.14274v3); the
  three ProveIt files above at the pin.
- Repository input: the pin `2b7b388ba` (3 October 2026, "Catalogue batches
  81 to 86"), an ancestor of the placement.
- Batch 89 of `docs/incoming`, manuscript 05 of five; arrival `8ea27d6c0`,
  placement `23adb85f9`, written in the batch-89 write phase (3 October
  2026). Single source, so the write made no merge choices.
