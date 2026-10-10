# Incoming reports

This directory is ProveIt's drop zone for new external research reports,
delivered as `.zip` archives. Each archive is one manuscript package. It holds
a LaTeX article, and usually its PDF, a delivery README, verification code,
recorded outputs, audit notes and a checksum manifest.

**Do not delete this `README.md`.** Once a batch has been placed, remove its
archives as section 7 describes, not this file.

Nothing in this directory is part of the repository's research material. An
archive becomes part of it only once it has been placed in, and written into,
a report at one of the destinations of section 2.

## Where this procedure comes from

The procedure was developed in the Surreal repository, whose drop zone was
`docs/new`, over surreal batches 13 to 35. That repository is now
[`Algebra/SurrealNumbers`](../../Algebra/SurrealNumbers/), merged with its
full history, and this directory replaced `docs/new` when it arrived. The
Cardinals repository, now [`SetTheory/Cardinals`](../../SetTheory/Cardinals/),
ran a parallel intake of ten "deliveries" into its research-report collection
before its own merge. Both histories are part of ProveIt's, so every commit
cited here can be inspected with `git show`.

Two consequences for reading those commits:

- **Paths moved.** In a Surreal-era commit the report collection is at the
  tree root's `docs/`, and its archives at `docs/new/`; in ProveIt it is at
  `Algebra/SurrealNumbers/docs/`. In a Cardinals-era commit the collection is
  at `docs/reports/`; in ProveIt it is at `SetTheory/Cardinals/docs/reports/`.
  A path quoted below without a prefix, such as `docs/README.md` in a
  Surreal-era worked example, is relative to that project.
- **Batch numbers continue the Surreal sequence.** The batch index counts
  every batch processed from this directory and from `docs/new` before it. The
  last Surreal batch was 35, so the first batch processed here is **36**. The
  Cardinals deliveries (first to tenth) are a separate, closed numbering.

Earlier batches differ from the procedure below in recorded ways:

- Batches 13 to 15 (`b071389`, `d6eee04`, `d3d9688`) put every manuscript
  under a `sources/` directory, with its README beside it. That covered merge
  bases, merge members and additions, and those placements staged no
  `article.tex` for a merge. `e5791a8` retired that practice.
- Batch 17 (`a826a41`) numbered its additions by batch position instead of by
  the target report's local sequence. `e9a9650` records this.
- The WIP commit `de84d8b` edited three delivered files. Batch 18 restored
  them.
- The catalogue step was done late for batches 14 and 15, in `e5791a8`, and
  batch 17 was catalogued together with batch 18.
- No Surreal batch after 13 has a separate audit commit.
- `docs/new` first appears in `f7f9a96`, after batch 17 was placed, so batch
  18 is the first batch processed from a drop zone.
- The Cardinals deliveries were not committed as archives (they went to the
  Recycle Bin), kept each package's delivered layout at the report root, and
  merged duplicates in commits of their own after a placement commit
  (`cb0af0ad8` placed, `0e5075f81` merged).

Reports placed before Surreal batch 13 predate the layout described here. They
keep main files such as `surreal_graphs.tex`, output directories such as
`results/`, and scripts at the report root; most Cardinals-collection reports
likewise keep their delivered layout. Do not "fix" them while processing a
batch. Where a past commit and this README differ, follow this README. The
commits cited at the end are worked examples, subject to these differences.

## 1. Inventory

- **Check that every archive is committed as delivered.** Run
  `git status --short -- docs/incoming`; it must show no untracked `.zip`.
  Deliveries are committed on arrival in a commit titled "New incoming
  external reports: …", as in `f7f9a96` and `15d4bab`. The root `.gitignore`
  does not ignore archives here, so a plain `git add docs/incoming/<archive>.zip`
  commits one. (The surreal package's own `.gitignore` ignores `*.zip`, which
  is why the Surreal-era deliveries needed `git add -f`; it does not reach this
  directory.) If an archive is untracked, commit it on its own, unchanged,
  before placing anything, or ask Vladimir to. Never delete it. Only a
  committed archive can be recovered after section 7 removes it.
- Extract every archive into a scratch directory **outside the repository**,
  such as the session scratchpad under `%TEMP%`. Never extract into the
  repository or into `C:\` root. Extract each archive into its own directory
  named after the archive: several archives may wrap an inner directory of the
  same name (`persistent_frontier_heights/` in two archives of batch 36), and
  on Windows a second extraction into the same place silently merges them.
- **Check whether an archive was already processed.** A later delivery may
  repeat an earlier one.
  - Hash every extracted file with `git hash-object`.
  - Find each hash in history with
    `git log --all --format=%h --find-object=<hash>`. A hit shows the commit
    that introduced that exact blob. Look for placement commits ("Place N
    manuscripts …" in ProveIt and the Surreal history, "Place N new reports …"
    or "Unpack, classify and catalogue …" in the Cardinals history).
  - Then confirm in the placement commit's own tree (`git ls-tree -r <place>`),
    not at `HEAD`: later commits rewrite articles and READMEs, and sometimes
    staged code, data or audits too.
  - At its placement commit, every staged file matches the delivered bytes,
    with one recorded exception. `a826a41` staged manuscript 05's
    `SOURCE_AUDIT.md` with a dated correction appended, because that audit
    made a false claim about the repository. A hash miss on such a file does
    not show that its archive is new.
  - `e9a9650` checked its nine repeated archives this way against
    `a826a41`.
- **Check the pin.** A delivery names the ProveIt commit it was written
  against (for Surreal-era deliveries, a Surreal commit). Record it for every
  manuscript; the report cites it as provenance (section 4, item 6).
- **Number the manuscripts.** Number the new manuscripts of the batch `01`,
  `02`, … in arrival order. This **manuscript number** names each manuscript
  in the placement commit message and, for a new merged report, is its file
  prefix. It is not the batch's own index (36, 37, …). The batch index appears
  only in write and audit commit titles and in the table at the end.
- **Checksum manifests and line endings are not intake work** (Vladimir,
  9 October 2026: "Don't be pedantic about line endings and checksums, and
  do not spend any effort on checking them or normalizing them. Completely
  ignore this issue."; `181579587`). A checksum manifest (`SHA256SUMS`,
  `SHA256SUMS.txt`, `MANIFEST.sha256` and the like) is neither verified nor
  special-cased: git's existing ignore rules decide whether it is staged.
  The root `.gitignore` ignores `**/SHA256SUMS` and `**/SHA256SUMS.*`, so a
  bare one stays out, while a prefixed copy is staged under `data/` like any
  other record (`0e05d71a1`, `18abb81b2`). Text files are staged as
  delivered under the existing `.gitattributes`, with no `-text` exceptions
  added and no CR check. A record that carries hashes alongside other
  content, such as a package, build or provenance manifest, is data and is
  staged under `data/`. Batches up to 137 verified every checksum manifest
  and dropped it (`e9a9650` dropped four `SHA256SUMS.txt` files but staged a
  `package_manifest.json` as
  `data/07-scale-moderate-interpolation-package_manifest.json`), kept CRLF
  files by `-text` lines, and normalized the unknot reports to LF; those
  commits are left as they are.
- **Run every verification suite on a copy**, never in place. Many suites
  rewrite their own evidence files, and some write timings or version strings.
  A check made after running a suite in place would compare two equally
  modified copies. Use `py` or `uv run --no-project python`; bare `python` does
  not resolve reliably here. A suite that needs a package (SymPy, say) runs
  under `uv run --no-project --with sympy==<pinned> python …`.

## 2. Decide placement

Read each manuscript, not its title. Titles and archive names mislead in both
directions. A `surreal_` archive may be about surcomplex objects. A shared word
such as "moment", "spectrum", "phase", "resonance" or "small divisor" can hide
different mathematics, and different titles can hide the same theorem.

### Destinations

ProveIt holds external research reports in two collections and in research
programmes. Choose the most appropriate place for each manuscript by its topic
and content (Vladimir's direction for batch 37), and state the reason in the
placement commit. The delivery README usually names the ProveIt path it
continues; verify that path against the current tree rather than trusting it.

| Place | Destination | Holds |
|---|---|---|
| Surreal collection | `Algebra/SurrealNumbers/docs/<family>/<report>/` | reports on `No`, `No[i]`, omnific integers and related structures; families below |
| Research-report collection | `SetTheory/Cardinals/docs/reports/<category>/[<subcategory>/]<report>/` | every other self-contained external report: ordinals and wqos, enumerative combinatorics, Hankel determinants, congruences, asymptotics, automata, graphs, the Jacobian conjecture, radicals and Galois theory, convex geometry, probability, … |
| Research programme | `Computability/TuringDegrees/Research/CoarseDegrees/research-reports/<NN>/`, `SetTheory/Cardinals/docs/cardinals/research-reports/` | numbered reports that continue a programme's own research plan and synthesis (plan targets, synthesis items) |
| Fabius frontier drafts | `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/<group>/<Document_Name>/` | Fabius, Rvachev up-function and Thue–Morse work continuing that tree's volumes; filed by the tree's own quick-intake procedure (its `drafts/incoming/README.md`): delivered package kept whole with its PDF, `MANIFEST.md` row and group-README mention, no SHAs in the records, claim review deferred (batch 38) |
| Transseries | `Analysis/Transseries/docs/series-and-transseries/<Document_Name>/` | transseries work of every kind (reversion, inversion, resurgence, regularity, transseries of special functions or sequences); **never under FabiusFunction** (Vladimir, 2026-09-29, after the split `277c782b8`). Filed like the Fabius drafts: the package kept whole with its PDF beside the volume it continues, a mention in `docs/series-and-transseries/README.md` naming that volume and the passage continued, no SHAs; merging into the volumes is deferred (batch 45) |
| Gowers–Szemerédi research | `Combinatorics/Ramsey/Research/GowersSzemeredi/<report>/` | work sharpening Gowers's proof of Szemerédi's theorem, placed beside its Lean development by Vladimir's direction (6 October 2026, batch 115), an exception to the formal-project rule below; so far every such manuscript is a numbered source of `local-quantitative-refinements` |
| Polylogarithms | `Analysis/Polylogarithms/docs/{articles,reports}/` | Vladimir's own PolyLog programme (moved from Smithereens `src/PolyLog`): delivered layout and names kept, Smithereens `docs/` mirrored so its relative links stay valid; PDFs kept as authored artifacts; only delivered content is placed, and local private paths are redacted with a dated note (Vladimir, 7 October 2026, placement `13f0d8f20`); claim review in the project README. Continuations are merged by thematic spine into `docs/reports/<spine>/`, delivered files kept, with an `OVERVIEW.md` reconciliation note and the corrections they propose recorded in the project README's "Status of claims" (batches 138 and 139, `06039f479`, `d4dead2c6`); the unified manuscript under `docs/manuscript/` (`c307fe77c`) is maintained in its own commits and not edited by intake |
| Unknot recognition | `Topology/UnknotRecognition/reports/<NN>/` | every report on unknot recognition: the archive extracted into the next number, with its single wrapper directory removed, files staged as delivered (line endings and checksum files are not checked, normalized or special-cased: git's existing attributes and ignore rules apply; Vladimir, 9 October 2026, for all intake), and a row in `reports/README.md`. **No test runs, no patch application, no soundness review**: a delivered patch to `fast/` stays inside the report directory (Vladimir, 7 October 2026: "the same applies to all future reports on this topic"; first placement `reports/07/`). Since 9 October 2026 knot-related reports belong to another agent (Vladimir's direction): the intake and catalogue of other topics neither place nor index them, and this README's records stop at report 25 |

- A manuscript that continues a report already in one of the collections goes
  to that report, whatever its subject.
- A manuscript that attacks a target of a research programme's plan, or an
  item of its synthesis, becomes the programme's next numbered report
  (numbered as its reports README prescribes; for CoarseDegrees, by archive
  modification time). Several manuscripts on one spine are merged into one
  numbered report. The programme's reports README gains a row, and amending
  the synthesis is separate work.
- Any other manuscript that continues a formal (Lean/Rocq) project goes to
  the research-report collection, in the category of its subject, never into
  the project's own directory (the one exception is the Gowers–Szemerédi
  research of the table above). The project README gains a pointer to it in
  the catalogue step (section 5). Batch 36 first placed five such reports in
  project `Research/` directories (`1a1396d4d`); Vladimir directed that they
  belong in the collection, and they were moved there before being written.
- A report that continues a formal development gains no formal status from
  it. Its README says which of its statements, if any, the project has
  already formalized (by declaration name), and that the rest are not. It
  cites the project's files as repository paths, not as relative links.

The Surreal collection's family directory follows the scalar system:

| Family | Contents |
|---|---|
| `surreal/` | `No` and real Hahn fields |
| `surcomplex/` | `No[i]` and complex Hahn fields, or results uniform in `R` and `C` |
| `surquaternions/` | quaternions over `No` |
| `physics/` | physical assessments |
| `foundations-and-computation/` | mathematics about the subject |

The research-report collection's categories are listed in
[its README](../../SetTheory/Cardinals/docs/reports/README.md). Neither list is
closed. A new family or category may be opened, but only in the placement
commit (or, as in batch 36, the move that corrects it) and with the reason
stated there. `d6eee04`
opened `surquaternions/` because its scalar system is new, and `physics/` to
keep assessments apart from mathematics. `d7fc004` opened
`foundations-and-computation/`.

### Role of each manuscript

For each manuscript, decide one of the following.

- **Addition to an existing report.** Choose this when the manuscript:
  - answers or refutes an open question or a claim that an existing report
    names;
  - delivers a continuation or "missing" item that a report names; or
  - re-derives a report's main theorem.

  The manuscript becomes a new part or section of that report, not a rival
  report. Continuing only one of a report's non-claims is not enough on its
  own. `a826a41` placed 02 + 03, which continue a non-claim of
  `spectral-theory`, as the new report
  `infinite-dimensional-hahn-spectral-theory`, which cites that non-claim.
- **Merge.** Choose this when several new manuscripts belong in one report.
  - They may prove the same spine: seven differential manuscripts in
    `b071389`, 08 and 09 in `a826a41`.
  - They may be complementary work on one subject. Complementary manuscripts
    become a multi-part report, and each part keeps its own definitions and
    hypotheses (`a826a41`: 02 + 03).
  - A merge may have more than one spine (`e9a9650`: 10 + 11 + 15).
  - When the manuscripts prove the same theorems, the **base** is the one with
    weaker hypotheses or greater generality. `a826a41` chose 08, which assumes
    only Γ ≠ 0, over 09, which assumes divisibility. Proofs taken from the
    others must be re-read for hidden uses of their stronger hypotheses.
  - A merge can also be an addition: several manuscripts that all answer one
    report's question are merged with each other and become one addition to
    that report.
- **New standalone report.** Choose this when the manuscript shares no named
  question and no spine with anything in the tree.
- **Placement only** (Vladimir, 9 October 2026). A single manuscript on a new
  topic is placed and not written: no write and no independent check follow
  (sections 4 and 6 do not apply). It keeps its delivered layout and file
  names with the wrapper directory removed, its delivered PDF, and its
  delivery README as the report README (a `README.txt` renamed `README.md`,
  content unchanged); the catalogue entry says that it was placed only. The
  model is `0599fe867` (nine probability reports). Where several deliveries
  overlap (one host, one theorem proved more than once), the intake decides
  between a full write and a reconciliation note: a README or `OVERVIEW.md`
  beside the delivered files that lists them by source, the overlap, the
  base and the credits, with its facts labelled as intake findings, no
  delivered file edited and no PDF built (`3d0303836`, `eb8dee994`,
  `a477aff21`, `845e133ec`).

Check every gap a manuscript claims to fill against the **current** tree, and
quote the passage with file and line. Manuscripts are written against pinned
older snapshots, so a gap may already be filled, perhaps by the previous
batch, or by a Lean or Rocq development the manuscript did not inspect.

If a manuscript refutes a claim that an existing report or project README
makes, check the refutation against the tree yourself. Also look for the same
claim repeated in other reports and READMEs, including the topic READMEs and
the root README. Retract the claim in a commit of its own before the
placement commit, and cite that retraction there. `d0e61c4` retracted a
claim, and `d3d9688` then placed the refuting manuscript. A manuscript that
improves a bound a README states (rather than refuting it) is a stale-claim
correction for the write phase (section 4, item 5), not a retraction; a
formally verified bound stays stated, beside the unverified improvement.

For a large batch, write one dossier per cluster before deciding. A dossier
records:
- setting and hypotheses;
- main results;
- notation collisions;
- repository claims, checked against the tree;
- how the verification suite behaves;
- non-claims.

## 3. Place: one commit, before any writing

Commit the placement before merging. The commit is titled "Place N manuscripts:
…" and states every decision and its reason. Since `e5791a8` retired
`sources/`, a manuscript that is not staged survives only in its committed
archive.

What is staged depends on the role of the manuscript:

| Role | `article.tex` and `README.md` | Code, data, audit and provenance files |
|---|---|---|
| New single-source report | staged as delivered, unprefixed (main `.tex` renamed to `article.tex`) | staged unprefixed |
| Placement-only report (section 2) | staged as delivered, names kept, with the delivered PDF | staged as delivered, in the delivered layout |
| Base of a new merge | staged as delivered, unprefixed | staged with a prefix |
| Other member of a merge | not staged | staged with a prefix |
| Addition to an existing report | not staged | staged with a prefix |

This table records the practice of `a826a41` and `e9a9650`, the placements
made after `sources/` was retired. Use `b071389`, `d6eee04` and `d3d9688` as
examples of placement decisions, not of staging.

- **Never staged:** for a report that will be written, PDFs and the
  manuscripts and READMEs of merge members and additions. Their provenance
  is recorded in the report instead. A placement-only report keeps its
  delivered PDF; checksum files follow section 1.
- **Where files go:**
  - scripts, proof sketches and build files (`.py`, `.sh`, `.ps1`, `.wl`,
    `.wls`, `.lean`, `.cpp`, `Makefile`, …) → `code/`;
  - recorded outputs, certificates, examples and requirements → `data/`;
  - audit and provenance markdown → the report root.
  - An existing report whose delivered layout differs (a Cardinals-collection
    report with `verify.py` at its root, say) still receives its additions in
    `code/` and `data/`; do not move its existing files.
- **Prefixes** have the form `NN-short-slug-`, for example
  `08-exact-and-drifting-multipliers-verify.py`.
  - A new merged report keeps its members' **manuscript** numbers, as every
    cluster merged since `1349004` did (for example `10-`, `11-` and `15-` in
    `e9a9650`). The two older surreal merges of `534e073`,
    `hahn-evaluation-at-omega` and `canonical-forms-need-not-be-subgraphs`,
    carry no prefixes.
  - An addition to an existing report continues that report's **own local
    sequence**. Use the next number after its highest existing prefix, with an
    unprefixed original counting as `01`. `d6eee04` already numbered this way:
    its manuscript 07 became `05-` in `contours-and-stokes`. `d3d9688` states
    the rule, and `e9a9650` spells out both clauses. Several manuscripts
    merged into one addition each take their own number in that sequence.
  - `a826a41` gave its additions their batch numbers instead. That is why
    `entire-functions-at-arbitrary-rank` has a `01-` below its `03-`, and why
    `exponential-automorphism-rigidity` has `04-` and `05-` after its
    unprefixed original. Do not rename them; count from the highest prefix
    present.
- **Delivered files stay byte-identical.**
  - This covers code, recorded outputs, and audit and provenance markdown. It
    holds even when code overwrites its own evidence, or when the text names
    delivery paths or files that are not shipped.
  - The one exception so far is an audit staged with a dated correcting
    finding appended (`a826a41`). Announce any such exception in the placement
    commit.
  - Disclose every other discrepancy in the report's README, and do not fix
    it in the delivered file.
  - `de84d8b` broke this rule: it patched a `build.py` and reran a suite in
    place. It is not a precedent, and batch 18 restored the delivered bytes.
- **Disclose renames.** The report's README maps delivery names to shipped
  paths. It names the shipped files whose text still uses delivery names:
  audits, build reports, and Makefiles that now live in `code/`. Rerun
  instructions must work with the shipped names: run on a copy, or pass an
  explicit output path.
- **Keep paths short.** Windows tools fail on paths over 260 characters, and
  the error they give is "file not found", not "path too long". The
  research-report collection is deep, so check that every staged path,
  prefixed with `C:\ProveIt\`, stays well under that limit (aim for 200), and
  shorten the slug of the prefix if not.
- **Verify the staging.** Copy every staged file from a **fresh** extraction,
  not from a directory where a suite was run. Then verify every staged blob
  against the fresh extraction, up to line endings: `.gitattributes`
  normalizes text to LF (`* text=auto eol=lf`), and since 9 October 2026 a
  blob that differs from the delivered bytes only in its line ends is
  accepted without a check (section 1).
- **Retire the archives in this same commit**, as described in section 7.

## 4. Write the reports

Turn the placed material into finished reports (a placement-only report,
section 2, is not written). Commit them in one or more
commits titled "Write batch <index> (<k>/<n>): <subject> into <report>", as
batches 30 to 35 did, or "Merge …". The rules below come from defects found in
earlier batches.

1. **Labels.** Every new `\label` carries a report prefix, for example `dyn:`
   or `ent:`.
   - Many reports have no prefix, or only a partial one:
     - bare `thm:…` and `eq:…` names in `gamma-functions`,
       `rank-one-berkovich`, `exponential-automorphism-rigidity`,
       `computable-surreals` and others;
     - bare names alongside `spec:` in `spectral-theory`;
     - per-part `a:` … `f:` prefixes in `analysis`;
     - nearly every report of the research-report collection, as delivered.
   - In a new report, give the delivered labels the report prefix during the
     write phase, before anything cites them.
   - New material in an existing report takes that report's prefix, plus a
     sub-prefix where names would collide (for example `tate:node:`). If the
     report has no single prefix, choose one for the new material, as
     `608dd23` chose `spec:`, and leave the bare names alone. The bare labels
     `de84d8b` added to `exponential-automorphism-rigidity` are not a
     precedent.
   - Once a report has been written, **never rename or delete any of its
     labels.** The surreal collection's `FORMALIZATION.md` cites labels by
     name, bare ones included, and maps them to Lean declarations; other
     projects' crosswalks may do the same.
   - Snapshot the labels before editing and compare afterwards. Count both
     `\label{…}` and the cleveref form `\label[type]{…}`, for example with the
     pattern `\\label(\[[^]]*\])?\{`.
   - Confirm that none were lost, and that every report receiving an addition
     or a merge gained labels. A gain of 0 means the integration did not
     happen, even if it reported success (`608dd23`).
2. **Union, not selection.** A merge keeps every result of every source.
   Print a duplicated result once, say which sources proved it, and keep
   genuinely different proofs as marked second routes.
3. **Non-claims.** Keep every limitation, disclaimer and priority caveat
   stated by any source. Dropping one silently strengthens the report
   (`e260237`).
4. **Notation.** Resolve every collision in the new material, never in
   existing labelled text.
   - When one word or letter carries several meanings across the sources,
     give each notion its own name and symbol, and fix them in a convention
     before any is used. Examples are "phase" in batch 13, and "resonance" and
     "small divisor" in batch 14. The batch-14 dynamics report opens with a
     table of notions (`fa9af09`).
   - Print the tempting false reading beside the true one (`d06ea7a`).
   - Disclose every symbol renamed from a source, with any change of
     normalization.
   - Before committing, check every reserved symbol, and every declaration
     such as "uses no J", against every use in the article. The batch-13 audit
     found three such declarations false as printed (`6048fb6`).
5. **Stale claims.** Correct any sentence that says the repository lacks
   something it now has, and keep the pin as provenance.
   - An open question that is only partly answered stays open and is
     re-scoped.
   - If a manuscript shows that an existing report's novelty or priority
     claim is incomplete, correct that report's existing text as well
     (`e9a9650` found such a gap in `hahn-tate-uniformization`). Item 4 limits
     notation changes only; it does not forbid these corrections.
   - A project README that states a result the new report improves keeps its
     statement, with its formal status, and gains a sentence on the
     unverified improvement and where it is.
6. **Provenance.** Say:
   - how many manuscripts the report was built from;
   - what each contributed;
   - each one's pinned commit;
   - where the merge had to choose.

   Promise no file that is not shipped, in text you write. Where a verbatim
   delivered file names one, say so in the README.
7. **Build.** Run
   `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex`
   (MiKTeX provides `latexmk`, `pdflatex` and `lualatex`; use the engine the
   report already uses).
   - The build must have zero errors, zero undefined references or
     citations, zero multiply-defined labels, zero duplicate PDF
     destinations, and zero mistyped cross-references (`d06ea7a`, `fa9af09`,
     `608dd23`).
   - A title page that resets the page counter needs
     `\hypersetup{pageanchor=false}` … `\hypersetup{pageanchor=true}` around
     it.
   - Do not attribute pre-existing warnings or boxes to a new edit: compare
     with a build of the committed text.
   - Build in a scratch directory. Commit `article.pdf`, but no auxiliary
     files (`.aux`, `.log`, `.toc`, `.out`, `.fls`, `.fdb_latexmk`).
   - Render the changed pages (`pdftoppm`) and look at them; text extraction
     is not layout verification.
8. **README.** Each report has a report README, not the delivery README.
   It gives the title and provenance, a listing that matches the directory,
   and the label prefix. It says what is claimed and what is not, describes
   the relation to neighbouring reports and to any formal development
   it continues, and gives build and rerun instructions. Check every number in it
   against the build or the data.
9. **Reciprocal notes.** Where a new result answers, sharpens or bears on
   another report, record it there in a short remark, in a commit of its own
   titled "Write batch <index> (reciprocal notes …): …", as batches 31 to 35
   did (`ab18444bb`, `6477b1c24`).
10. **Every edited report is rebuilt.** A reciprocal remark added to a
    neighbouring report changes that report too. Rebuild its PDF, and update
    any page count its README states.
11. **Unproved and wrong claims are never dropped** (Vladimir's standing
    rule, 4 October 2026). This applies to claims of a source, of a review
    and of the write itself, during the write, the audit and any later
    review.
    - An unproved claim moves to a "Further questions and research" section
      of the Part, or to the report's existing questions section. It is
      stated as an open question with its source credited, the argument
      sketch it came with, and what is missing.
    - A claim that is demonstrably wrong stays on record, with an explicit
      proof of its failure or a concrete counterexample (a numbered remark)
      whenever one can be given. Batch 92's correction of a lemma in the
      Kuhlmann–Serra preprint by the counterexample t ↦ t + t² on k(t) is
      the model.
    - The commit message lists every claim so moved or refuted.

## 5. Catalogue

Catalogue every destination the batch touched, in one commit titled
"Catalogue batch <index>: …".

- **Surreal collection:**
  - Update `Algebra/SurrealNumbers/docs/README.md`: the report count in its
    opening sentence, the per-family counts in its section headings, and the
    family tables.
  - Update `Algebra/SurrealNumbers/docs/manifest.tex`: one `\entry` per
    report, plus every count it spells out. Those are the `pdfsubject` in the
    preamble, the title page, the Scope paragraph with its per-family
    breakdown, and the opening paragraph of each family section, including
    sub-counts. Then rebuild `manifest.pdf`.
- **Research-report collection:**
  - Update `SetTheory/Cardinals/docs/reports/README.md`: the count in its
    opening sentence and the category table with its total, and the account
    of deliveries and merges when the batch merged anything.
  - Update `SetTheory/Cardinals/docs/reports/manifest.tex`: one `\entry` per
    report (an extended report's entry gains the new result and its source
    archives), plus every count it spells out, including the `pdfsubject`,
    the Scope section and the directory-tree table. Then rebuild
    `manifest.pdf`.
- **Formal projects continued:** a project whose work a new report continues
  (the Jacobian-conjecture, polyomino and polynomial-formula projects in
  batch 36) gets a short pointer in its README, and in its `Research/README.md`
  if it has one: where the report is, what it claims, and that it is not
  formalized. A result the report improves stays stated with its formal
  status (section 4, item 5).
- **Counts elsewhere.** The root `README.md`, the topic READMEs
  (`Algebra/README.md`, `SetTheory/README.md`, …), `SetTheory/Cardinals/README.md`
  and the Surreal package's own README state collection sizes ("63 research
  reports", "104 research reports"). Correct every count the batch changed.
- **Unknot recognition** reports are not catalogued here since 9 October
  2026 (destinations table).
- **Catalogue every report without a row**, not only this batch's. Take the
  count from the report directories, not by adding to the old total, and check
  the rows against `git ls-tree -d HEAD` of the collection.

A lagging catalogue has already misled an incoming manuscript. The source
audit delivered with batch 17's manuscript 05 read the collection README,
found no exponential-automorphism row, and concluded that the collection had
no such report. See `a826a41`.

Four other shared files of the surreal collection are maintained by its
review and formalization work:
- `Algebra/SurrealNumbers/docs/FORMALIZATION.md`
- `Algebra/SurrealNumbers/docs/NORMAL_FORM_BRIDGE.md`
- `Algebra/SurrealNumbers/docs/NOTATION.md`
- `Algebra/SurrealNumbers/docs/REVIEW.md`

Do not rewrite them while processing a batch.

**Check their label citations report by report.** For each surreal report the
batch edited, every label cited in that report's section of `FORMALIZATION.md`
must still resolve in the file named on the section's `Source:` line. That
file is `article.tex`, except in `canonical-forms-need-not-be-subgraphs`
(`surreal_graphs.tex`) and `gonshor-product-birthdays`
(`surreal_product_birthdays.tex`). Do not search the whole collection
instead: bare labels such as `thm:main` are defined in several reports, so a
label lost from one would still be found in another. Check the other three
files' label citations into the edited reports the same way. A project whose
Lean crosswalk cites report labels is checked the same way.

Line numbers in `FORMALIZATION.md` are navigation hints, and the formalization
work refreshes them. A batch may correct a figure there that it has made
false, such as the number of main reports. Correct only that figure, say so
in the commit, and leave indexing the new reports to that work. The one
precedent is `72560ca`.

## 6. Audit and fix

Audit the written reports independently, with each auditor taking one lens:
- fidelity to the sources;
- notation;
- non-claims;
- whether a reader could believe more was verified than was, in particular
  that a report continuing a Lean or Rocq development is itself verified.

Commit the fixes as "Fix <count> defects found auditing batch <index>", for
example `6048fb6`, "Fix twenty defects found auditing batch 13". Rebuild and
re-check labels afterwards.

## 7. Clear this directory, in the placement commit

In the placement commit of section 3, as `e9a9650` did, remove the batch's
archives from this directory:
- Use `git rm docs/incoming/<archive>.zip` for each archive of the batch.
  Also remove any archives of earlier batches still here, after verifying them
  against the placement commit that used them.
- Never run `git rm -r docs/incoming` or delete the directory: a later
  delivery may already be waiting here. **Keep this `README.md`.**
- Record in the placement commit which archives were retired and how each was
  accounted for.
- If `git rm` reports that an archive is not tracked, stop. Do not delete the
  file; commit it first (section 1).

The archives remain available from the commit that added them
(`git show <arrival>:docs/incoming/<archive>.zip > <scratch>/<archive>.zip`).
The write phase needs the manuscripts, READMEs and pins of merge members and
additions, which are never staged. Re-extract them into a fresh scratch
directory from that commit.

## Worked examples in the history

Surreal-era batches (paths relative to `Algebra/SurrealNumbers/`; archives
under `docs/new/`):

| Batch | Place | Write or merge | Catalogue | Audit |
|---|---|---|---|---|
| 13 | `b071389` | `d06ea7a` | `3b2338e`; ledger counts `72560ca` | `6048fb6` |
| 14 | `d6eee04` | `fa9af09` | `e5791a8` (late) | — |
| 15 | `d3d9688` | `608dd23` | `e5791a8` (late) | — |
| 17 | `a826a41` | `de84d8b` (a WIP; see section 3), `b147a9d` | with batch 18 | — |
| 18 | `e9a9650` | `813ce54` | `befea11` (with batch 17) | — |
| 19 | `30dfb4f` | `ed88b8f` | `9b69d4e` | — |
| 20 | `5fe7f8d` | `fb182ea` | `463fcc7` | — |
| 21 | `d4e71b7` | `3a2d35d` | `13cb68e` | — |
| 22 | `7b5f934` | `68e2960` | `5d369a0` | — |
| 23 | `e4f8848` | `7af7056` | `087ee37` | audited before commit (`7af7056`) |
| 24 | `be06fc8` | `bbdd536`, `7494d53` | `b5f0bfd` | — |
| 25 | `cf350b1` | `e27070f`, `0240140`, `3daef3c` | `b5f0bfd` | — |
| 26 | `f4c9504` | `9b80a30`, `1e54d5a`, `aae58bb` | `b5f0bfd` | — |
| 27 | `a4dcb91` | `337d4a4`, `600397e`, `e118d89`, `b829d8b` | `b5f0bfd` | — |
| 28 | `c6359e4` | `3d9dbe9`, `b3fa9e2`, `74b8974`, `a2b22a9`, `ac54217` | `b5f0bfd` | — |
| 29 | `66d7e55` | `1bdd65c`, `4420ec6`, `a8f35b5`, `298bed6`, `e9d1959`, `2da3bd4` | `b5f0bfd` | — |
| 30 | `21375f8` | `Write batch 30 (1/5)` … `(5/5)` | kept current by review commits | — |
| 31 | `9d28e28` | `Write batch 31 (1/7)` … `(7/7)`; notes `ab18444` | kept current by review commits | — |
| 32 | `7d04483` | `Write batch 32 (1/8)` … `(8/8)`; notes `2535d52`, `fbb8d2d`, `749d429` | kept current by review commits | — |
| 33 | `aa9c891` | `Write batch 33 (1/6)` … `(6/6)`; notes `0e16436`, `6fb0f74` | `5055c82`, `b41c41c` | — |
| 34 | `a7a435f` | `Write batch 34 (1/9)` … `(7/9)`; no commit is titled `(8/9)` or `(9/9)` | kept current by review commits | — |
| 35 | `dec8d56` | `32bb723`; notes `6477b1c` | kept current by review commits | — |

List a batch's write commits with `git log --oneline --grep="Write batch 34"`.

Batch numbers:
- No commit names a batch 16. The only report added between batches 15 and 17
  is `computable-surreals`, which arrived already merged and was added in
  `e5791a8` without a placement commit.
- The number 18 for `e9a9650` is inferred: that commit numbers the manuscripts
  of two deliveries, `f7f9a96` and `15d4bab`, as one sequence 01–18.
- The numbers 30 to 35 of the placement commits are inferred from the write
  commits that follow them; the placement messages do not state them.
- Batches 30 to 35 have no catalogue commits of their own: the concurrent
  proof-review and formalization commits kept `docs/README.md` and
  `docs/manifest.tex` current, most fully in `b41c41c` ("Synchronize the
  63-report catalogue"). A batch processed here catalogues itself (section 5).

Earlier merges were audited in `b5231b1` (the six surcomplex merges of
`1349004`), and in `abce2d6` and `e260237` (the two merges of `e268b51`).

Cardinals-era deliveries (paths relative to `SetTheory/Cardinals/`): the
first unpacking `a3fe9660e`; sorting and duplicate merges `f0f61b70d`,
`8374aaa79`; the seventh delivery placed in `854a8b4f9` and catalogued in
`b64b2c0c1`; the eighth placed in `cb0af0ad8` and merged in `0e5075f81`.

ProveIt-era batches (from this directory):

| Batch | Place | Write or merge | Catalogue | Audit |
|---|---|---|---|---|
| 36 | `1a1396d`; moved into the collection by `d5e1fb3` | `3a15f34`, `b3d0c1b`, `2becd30`, `bb501ab`, `c69841a`, `d532b65`, `a10e9be`; notes `6c9175a`, `a20a47c` | `de4ac5a` | `821f699` (29 defects, three lenses) |
| 37 | `0e53d10` | `e2f896d`, `ac07b4c`, `3f47574`, `f0fc69f`, `b6ef9e5`; notes `15c5658` | "Catalogue batches 37-38" | — |
| 38 | `938b2f7` (five packages filed in the Fabius drafts tree by its quick intake) | `fa77d9e` | "Catalogue batches 37-38" | — |
| 39 | `e2b1f01` (four collection additions; two packages filed in the Fabius drafts tree) | `a30b1c5`, `6a354f5`, `ed123c7`, `0e0368b` | "Catalogue batch 39" | — |
| 40 | `afb2d12` | `d607838`, with batch 41: `8d936ee`, `18634ca` | "Catalogue batches 40-41" | — |
| 41 | `eaf787d` | `18634ca` (DFAO Part III, with batch 40), `ac9107d`, `c130dba`, `ccc29b9`; notes `e489bd5` | "Catalogue batches 40-41" | — |
| 42 | `3609d04` | `e9f425f`, `3815377`, `a835019`, `b1f5e8d`, `0e6632a` | "Catalogue batch 42" | — |
| 43 | `faef2ed` (six archives from two arrival commits) | `b8e4607`, `fb60de0`, `22f7689`, `d252e2a` | "Catalogue batch 43" | — |
| 44 | `2030160` | `ff9032b`, `b26d06011`, `6f09f41`; notes `21890f8` | "Catalogue batch 44" | — |
| 45 | `13e4dc0` (six transseries packages filed whole under `Analysis/Transseries`; two arrival commits) | — (merge into the volumes deferred) | in the placement commit | — |
| 46 | `296aa22` (six transseries packages filed whole under `Analysis/Transseries`) | — (merge into the volumes deferred) | in the placement commit | — |
| 47 | `e87ca20` (seven transseries packages filed whole under `Analysis/Transseries`; two arrival commits) | — (merge into the volumes deferred) | in the placement commit | — |
| 48 | `2fc8325` (ten transseries packages filed whole under `Analysis/Transseries`) | — (merge into the volumes deferred) | in the placement commit | — |
| 49 | `140860b` (five transseries packages filed whole under `Analysis/Transseries`; one Fabius-zonoid continuation filed under `Analysis/FabiusFunction/…/representations`; two arrival commits) | — (merge into the volumes deferred) | in the placement commit | — |
| 50 | `88a2647` (five transseries packages filed whole under `Analysis/Transseries`; one Fabius-jet correction filed under `Analysis/FabiusFunction/…/representations`, after the retraction `7cf49f7` of the zonoid report's jet small-ball conjecture) | — (merge into the volumes deferred) | in the placement commit | — |
| 51 | `1dcf447` (two transseries packages filed whole under `Analysis/Transseries`) | — (merge into the volumes deferred) | in the placement commit | — |
| 52 | `a701d90` (eight transseries packages filed whole under `Analysis/Transseries`; four additions to the research-report collection — Part II of `specialization-safe-radical-solvers`, Part IV of `adjacency-bounded-132-avoiders` from two manuscripts, Part II of `open-query-membership-games`; four arrival commits) | `def933b`, `4b71d56`, `f11edd3` (the three collection reports; merge of the transseries packages into the volumes deferred) | "Catalogue batches 52 and 53" | — |
| 53 | `1dc8749` (one transseries package filed whole under `Analysis/Transseries`; one addition to the research-report collection — Part IV of `shifted-catalan-hankel-polynomials`) | `e300500` (the collection report; merge of the transseries package into the volumes deferred) | "Catalogue batches 52 and 53" | — |
| 54 | `4d922d5` (four Fabius-tree arrivals filed whole — `thue-morse`, two in `inverse-and-sampling`, `representations`; one addition to the research-report collection — Part IV of `nonreal-roots-in-iterative-equations`; three arrival commits; `ProveIt_Lorentzian_Support` held for batch 55) | `902757b` (the collection report; editorial pass on the Fabius-tree arrivals `1085b50`) | "Catalogue batches 54 and 55" | — |
| 55 | `26473df` (five additions to the research-report collection — Parts V–VII of `preorder-root-polytopes` from four manuscripts, one of them held from batch 54; Part V of `shifted-catalan-hankel-polynomials`; three arrival commits) | `8c6517c`, `b2aed2d` (the two collection reports) | "Catalogue batches 54 and 55" | — |
| 56 | `ae718a4` (four Fabius-tree arrivals filed whole — `representations`, two in `inverse-and-sampling`, `spectra-and-arithmetic`; two additions to the research-report collection — Part II of `cigler-conjecture-16-parity`, Part III of `open-query-membership-games`; after the retraction `473b641` of the information frontier's expected `q^{mn}` Appell diagonal) | `3a06260`, `f8a20bc` (the two collection reports; editorial pass on the Fabius-tree arrivals `25b4737`) | "Catalogue batches 56 and 57" | — |
| 57 | `70b3994` (three Fabius-tree arrivals filed whole — `inverse-and-sampling`, `rvachev_up_fourier_decay`, `thue-morse`; three additions to the research-report collection — Part VI of `shifted-catalan-hankel-polynomials`, Part II of `sextic-block-resolvent-separators`, Part III of `bernoulli-entropy-quasiconcavity`) | `f5c3313`, `23cb2d0`, `5e0f4e0` (the three collection reports; editorial pass on the Fabius-tree arrivals `cae7755`) | "Catalogue batches 56 and 57" | — |
| 58 | `b30441a` (a new six-source Surreal-collection report, `surreal/polytopes-at-surreal-scales`; Part II of the research-report collection's `arithmetic-local-global-fibers`) | `f608f1c`, `4e12835` (the collection report and the surreal report, Parts I–V) | "Catalogue batches 58 to 61" | — |
| 59 | `f2cb203` (six additions to the Surreal-collection report `surreal/polytopes-at-surreal-scales`, Parts VI–X) | `da05b41` (reciprocal note in `omnific-groups-and-lattices` `526c255`) | "Catalogue batches 58 to 61" | — |
| 60 | `7498484` (two new research-report collection reports in a new category `hilbert-tenth-problem/` — `canonical-diophantine-certificates` from six manuscripts, `probabilistic-quantum-and-continuous-computation` from three; three arrival commits) | `5b87c88`, `e18718e` (the two reports; the first also merges batch 61's manuscript; the pointer in `Computability/HilbertTenthProblem/README.md` deferred) | "Catalogue batches 58 to 61" | — |
| 61 | `3bf66a8` (one queue-certificate manuscript, a seventh member of `hilbert-tenth-problem/canonical-diophantine-certificates`, merged in the batch-60 write) | with the batch-60 write, `5b87c88` | "Catalogue batches 58 to 61" | — |
| 62 | `adeddce` (fourteen Diophantine-certificate manuscripts: Parts X–XIII of `hilbert-tenth-problem/canonical-diophantine-certificates`, Parts V–VII of `probabilistic-quantum-and-continuous-computation`, and a new report `liveness-beyond-halting`; three arrival commits) | `0744012`, `176e31c`, `2a34b17` (the three reports; the third also merges batch 63's liveness manuscript; the pointer in `Computability/HilbertTenthProblem/README.md` deferred) | "Catalogue batches 62 to 64" | — |
| 63 | `62f1ad0` (three additions to the research-report collection — a third member of `hilbert-tenth-problem/liveness-beyond-halting`, Part XIV of `canonical-diophantine-certificates`, Part VIII of `preorder-root-polytopes`) | `2a34b17` (the liveness member, with the batch-62 write), `781594d`, `7498921` | "Catalogue batches 62 to 64" | — |
| 64 | `3025c15` (one Fabius-tree arrival filed whole — `inverse-and-sampling/comb-interpolation/Approximate_Phase_Rigidity`; five research-report additions — Part IX of `preorder-root-polytopes`, Part III of `arithmetic-local-global-fibers`, Part XIV of `slice-regularity-and-fueter-inversion`, Part VIII of `probabilistic-quantum-and-continuous-computation`, Part V of `adjacency-bounded-132-avoiders`) | `8a8c072`, `6b51eba`, `ff69694`, `4681763`, `b8b0fa2` (the five collection reports; 1d89951) | "Catalogue batches 62 to 64" | — |
| 65 | `3fd8500` (three Fabius-tree arrivals filed whole — `inverse-and-sampling`, `exponents-and-q-series`, `representations`; one transseries package filed whole under `Analysis/Transseries` (tenth delivery); one addition — Part IV of `open-query-membership-games`) | `6743009` (Part IV of `open-query-membership-games`; Fabius-tree and transseries flags fixed in `1156651`) | "Catalogue batches 65 to 68" | — |
| 66 | `4fee1cd` (five research-report additions — Parts II and III of `constrained-crossover-closure`, Part III of `cigler-conjecture-16-parity`, Part III of `insertion-degree-spectra`, Part X of `preorder-root-polytopes`; one Fabius-tree arrival filed whole — `representations/Critical_Complements_Fabius_Conditioning`) | `202aafd`, `e181765`, `8498962`, `63a7a32` (the four collection reports; Fabius editorial pass `54f5c9c`) | "Catalogue batches 65 to 68" | — |
| 67 | `d281a28` (three research-report additions — Parts V and VI of `dfao-reversal-coloring-obstruction`, Part II of `domination-root-minus-four-order-30`; one Fabius-tree arrival filed whole — `exponents-and-q-series/Entire_Borel_Transform_Natural_Boundary_q_Fabius_Law`; two arrival commits) | `269ab1c`, `ab19706` (the two collection reports; Fabius editorial pass `54f5c9c`) | "Catalogue batches 65 to 68" | — |
| 68 | `29e52fc` (three Fabius-tree arrivals filed whole — `thue-morse`, `inverse-and-sampling`, `representations` (a second, independent Critical Complements package beside batch 66's); three research-report additions — Part V of `open-query-membership-games`, Part XI of `preorder-root-polytopes`, Part VI of `adjacency-bounded-132-avoiders`) | `e909e2e`, `4a3b699`, `cfdefe6` (the three collection reports; Fabius editorial pass `54f5c9c`) | "Catalogue batches 65 to 68" | — |
| 69 | `92b9041` (one Fabius-tree arrival filed whole — `spectra-and-arithmetic/Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws`) | Fabius editorial pass `c703cc7` | — | — |
| 70 | `51c6943` (four research-report additions — Part IV of `cigler-conjecture-16-parity`, the depth-three addition to `power-tower-derivative-term-counts`, Part III of `sextic-block-resolvent-separators`, Part XII of `preorder-root-polytopes`; one new report — `jacobian-conjecture/keller-map-dynamical-degrees`; one Fabius-tree arrival filed whole — `rvachev_up_fourier_decay/Sharp_Cr_Spectral_Disks_Rvachev_Thue_Morse`) | `369927b`, `ca81647`, `4408aa8`, `d5e863b`, `4f8b1a7` (the four collection reports and the new Keller report; Fabius editorial pass `c703cc7`) | "Catalogue batch 70" | — |
| 71 | `427bca7` (three research-report additions — Part IV of `constrained-crossover-closure`, Part XIII of `preorder-root-polytopes`, Part VII of `adjacency-bounded-132-avoiders`; one Fabius-tree arrival filed whole — `representations/Second_Order_Critical_Complements_Fabius_Conditioning`) | `f0ab7f4`, `7eb503b`, `d70ea7b` (the three collection reports; Fabius editorial pass `82e45c7`) | "Catalogue batch 71" | — |
| 72 | `9e6b046` (72D: Parts VIII–IX of `adjacency-bounded-132-avoiders`), `0eb68d4` (72E: eight Fabius-tree arrivals filed whole in `representations/`), `a6a3b49` (72B: thirteen Fabius-tree arrivals filed whole in `thue-morse/`), `8bb543f` (72C: new report `log-concavity-and-unimodality/matching-rank-normalization`), `d292c67` (72A: five additions to `power-tower-derivative-term-counts`, new reports `power-tower-exponent-supports` and `a290268-unbounded-deficits`); 79 archives in one arrival commit, split into five topical clusters; duplicates not staged: three repeats of batch 71, one in-batch byte copy, two superseded versions and many embedded copies | `8cdb865`, `30370df` (72D); `d795a17`, `d47b43c`, `a67a561`, `2c8efd7`, reciprocal `ef66df0` (72A); `7a5c50c`, `db5e315`, `e6de4d9`, `7112deb`, reciprocal `4b478ba` (72C); Fabius editorial passes `64b137c` (72E), `d3c317c` (72B) | "Catalogue batch 72" (`e37a178`) | — |
| 73 | `26abf25` (73X), `9df4ba5` (73O1), `6e193dd` (73O2), `5e4f126` (73C1), `8f5c531` (73C2); 62 archives in seven arrival commits (`f8c3a39` … `aa43cc5`), split into five clusters; not placed: superseded editions and re-proofs (ten archives); same-theorem pairs merged with second routes; eighteen collection reports opened across 73/74, one surreal report, one Fabius package, one transseries package | writes `13ef7d9`, `4c11849` (73X); `946b6c7` … `82afb95` (73O1, ten); `0a5908e` … `c970d90`, reciprocal `1f64c1b` (73O2, eight); `a584868`, `b886fe4`, `454d7d4` (73C1); `017ac1e` … `bc576a8` (73C2); surreal `9265235`, reciprocal `5cbcc02`, fix `a68b926`; reciprocal `a115f6f`, `b8c8adc`; transseries editorial pass `5b5f670`; Fabius editorial pass `8c47d6d` | "Catalogue batches 73 and 74" (`f6436c1`) | — |
| 74 | `b669cff` (five archives of `c664fc2`: Part II of `factorial-ratio-polynomial-divisibility`, a second derivation for `a097356`, Part II of `a189281`, new reports `a273821-first-pattern-failure` and `a238016-restricted-partitions-cubic-boundary`; three re-prove today's reports, printed as second routes) | `aeca276`, `18d0560`, `f440ed3`, `d42d33d`, `83fcbe5`, reciprocal `31cf70f` | "Catalogue batches 73 and 74" (`f6436c1`) | — |
| 75 | `6ea60e3` (six archives of `4b874ce`: sources 01 and 06 into `a022629-distinct-partition-norms` (its third and fourth independent proofs; only new material printed), Part IV of `a215561-fixed-composition-excursions` (Kauers–Koutschan Conjecture 15), new reports `a069762-pyramidal-frobenius`, `valley-monotone-bargraphs`, `a126764-lconvex-polyominoes`) | `046c3a9`, `c58206c`, `0276bb4`, `9891e1f`, `9368967` | "Catalogue batch 75" (`171ddcb9e`) | — |
| 76 | `2a04b60f2` (seven archives of `6914ccca6`: three independent manuscripts on the lexicographic order of the well-orderings of the reals merged as the new report `ordinals-and-order-types/lexicographic-well-orderings-of-reals`; Part III of `a088714-bell-scale-growth`; Part IX of `probabilistic-quantum-and-continuous-computation`; the new report `hilbert-tenth-problem/group-theoretic-substrates` from two manuscripts; nothing superseded; four files of 01 equal to repository files and its regenerable 2.49 MB coefficient table not staged) | `718bfa3b5`, `603f6ed31` (lexicographic well-orderings), `227127edf` (Part III), `05ff58c7f` (Part IX), `a5c1e450a` (group-theoretic substrates; guard fixes to two of its imported programs from the Hilbert's-tenth review, `db3b377f0`); reciprocal note in `point-separating-game-values` with the catalogue | `da8ca7cb3` | — |
| 77 | 71 archives of `096ee7b87`, in six clusters: `089d2b825` (77U: Section 14 of `preorder-gamma-rank-ulc`; 95.1 MB of certificate shards that no shipped program regenerates kept only in the arrival commit, with a retrieval and replay recipe; a 4.0 MB input staged as an xz container), `4f11bc9c0` (77P5: six new reports, Part III of `apery-hankel-determinant-growth`, Parts II of `a330266-balanced-smirnov-poisson` and `a126764-lconvex-polyominoes`, a third route for `a279619-level-seven-gamma-constant`; three transseries packages filed whole under `Analysis/Transseries`; two exact-value tables of 2.2 and 18 MB excluded as regenerable), `f76fcb566` (77P1: four new reports from eleven manuscripts, five of them nested byte for byte inside others and staged once; 18 page renders, 4.4 MB, excluded and reproduced byte for byte), `d0e6008d9` (77P4: eleven new reports, one of them in `automata-and-formal-languages`; 27 superseded by its attribution revision 26; 29 handed to 77P3), `34f1acd4b` with `c47b7e984` (77P3: seven new reports from fifteen archives; 20 superseded by 21; five galled-triangle files, 3.49 MB, excluded as regenerable; `c47b7e984` removes five archives that an index-lock race left behind), `aa7345800` (77P2: six new reports, a fifth source for `a022629-distinct-partition-norms`, Part V of `a215561-fixed-composition-excursions`, Part IV of 77P3's `a082161-airy-amplitudes`; 54 superseded by 53; three embedded foundations staged once); 34 new collection reports | 77U `4108f2b18`; 77P1 `c368ae9cf`, `a532b7582`, `80da274bb`, `65f5f48dc`, reciprocal `cb483cb9d`; 77P2 `1b0698659`, `c04fef32b`, `104e37ec8`, `03b314eb0`, `e76783c09`, `eab13fe8d`, `ba16c5b02`, `766f0de79`, reciprocal `67d54b7ac`; 77P3 `df01ebad9`, `2cbf7e130` (with 77P2's Part IV), `4dde85e7f`, `48c008375`, `3bdd8611a`, `b3ffc8d30`, `68cff5deb`, reciprocal `5b6fa58a5`; 77P4 `d502248d6` … `0428a87a0` (eleven), reciprocal `222291f94`; 77P5 `d0225ca12`, `1a372a1ca`, `424734dc4`, `ce04a5088`, `e4df71779`, `54a4f400d`, `5ee0abf33`, `f73d2f729`, reciprocal `6eb000fc7` (its pointer from `a022629-distinct-partition-norms` to `a291698-moving-fugacity-partitions` is in `ba16c5b02`); transseries editorial pass on the three 77P5 packages `a601d5e1b` | `da8ca7cb3` | — |
| 78 | fourteen archives in four arrival commits (`1977e6ea6`, `808b53ed8`, `48ee077c7`, `24a743255`), in three clusters: `aa11f3fef` (78H1: three interaction-combinator manuscripts as Part XV of `canonical-diophantine-certificates`; two of them prove one compiler theorem by one method, printed once), `798b0c5d4` (78H2: the new reports `signal-machine-collision-certificates`, two routes to one theorem, and `stochastic-and-thermal-exactness` from three manuscripts; two certificate files of 11.9 and 21.8 MB excluded, regenerated byte for byte in 17 s), `41e7f1189` (78H3: Part XVI of `canonical-diophantine-certificates`, Parts III–IV of `group-theoretic-substrates`, the new report `quadratic-orthant-certificates` from three manuscripts; its two Waterfall machine files are third-party data, Iijil's from the MTGPrograms repository with no upstream licence observed, staged with a provenance note and not covered by MIT-0); nothing superseded; re-proofs of `canonical-diophantine-certificates` Parts V and XI printed as pointers | 78H1 `ebea5a2e8`; 78H2 `b6a99c594`, `57baff577`, reciprocal `f16419fce`; 78H3 `cb8238b64`, `44983ed7e`, `c51b9880d`, reciprocal `f417337ac`; reviews of the same archives in the Hilbert's-tenth research tree by another session (`44b28c395`, `126028588`, `a1264b55c`, `f19aaa092`) | `da8ca7cb3` | — |
| 79 | nineteen archives in four arrival commits (`060e08a07`, `2a8a39599`, `ef2fc7990`, `aebfa386e`), in three clusters: `224ca41df` (79J1: two manuscripts proving one theorem by two routes as Part XVII of `canonical-diophantine-certificates`; the new reports `polynomial-witness-histories` from three manuscripts, one answering another, and `smooth-diophantine-finalizers` from one; three expanded-polynomial exports of 1.0–1.6 MB excluded, regenerated byte for byte), `bbaf322e5` (79J3: an independent re-proof of Part XVI printed inside it as a second route, and Part XVIII, of `canonical-diophantine-certificates`; Parts IV–V of `stochastic-and-thermal-exactness`, two of the three manuscripts proving one theorem by two routes; Part VI of `liveness-beyond-halting`; nothing excluded), `a7ae02511` (79J2: Parts III–IV of `signal-machine-collision-certificates`, Parts IV–VI of `quadratic-orthant-certificates`, Part XIX of `canonical-diophantine-certificates`; 07 superseded by its corrected edition 16, nothing of it staged; the reset-net manuscript re-derives the universal-membrane manuscript's program layer, staged and printed once; twenty-one heavy regenerable files, 70.1 MB, excluded with tested reconstruction recipes; two `.gitattributes` `-text` lines keep two delivered CRLF tables; four copies of the third-party Waterfall machine table not staged again); no other archive superseded; re-proofs of `canonical-diophantine-certificates` Parts I, II, V, VI, IX, XI and XIII, of `liveness-beyond-halting` and of Part I of `stochastic-and-thermal-exactness` printed as pointers or marked second routes | 79J1 `c03d95fe6`, `83abbd7fa`, `f97814421`, reciprocal `7ec2b5a2a`; 79J3 `c5f6a3219`, `957351037`, `0ac86bb58`; 79J2 `bd8a8afd6`, `11abe5008`, `954261e15`, reciprocal `bbc67d225`; reviews of the same archives in the Hilbert's-tenth research tree by another session (before placement `e5497072e`, `9f033fa6e`, `49bc4c654`, `2c311e525`, `85294a527`, `be1fc3f62`, `fd4a2e8d3`, `9975af7e1`, `3b5989da9`, `899391bde`; after placement `a21c86070`, `5b633fcf9`, `9df1f72ca`; placement authentications `5971f9294`, `5b633fcf9`, `653349f6a`; audits of the written Parts `c7dd5823d`, `15da2d356`, `d402a41a3`, `811fcb024`, `c8e503d8a`, `4fc9630f4`) | `ca62e1488` | — |
| 80 | twelve archives in one arrival commit (`4e270aa46`), in three clusters: `8a4e64732` (80K1: three corrected code editions of batch-79 packages, amending Part XIX of `canonical-diophantine-certificates`, Part VI of `quadratic-orthant-certificates` and Part IV of `signal-machine-collision-certificates`; manuscripts byte-identical to batch 79, so nothing printed changes; each repair is equivalent to the Hilbert's-tenth review's patch; 13 placed files replaced under their names, 8 added), `345a9e44e` (80K2: four conserved-mass manuscripts as Parts V–VI of `signal-machine-collision-certificates`, sources 14–17; 06 superseded by its attribution revision 05, nothing of it staged; 10 re-proves `smc:sl:thm:two`, printed as a pointer, and its receipt, equal to Part IV's, not staged again; 02 extends 10, its five vendored programs shipped once; five rule and certificate exports of 10, 20.8 MB, excluded with a reconstruction recipe; one `.gitattributes` `-text` line keeps 03's CRLF table), `ccc046989` (80K3: four independent surreal well-order manuscripts, two pairs sharing an archive name without being editions, merged as the new surreal-collection report `foundations-and-computation/surreal-well-orders`, base 11; the core proved up to four times printed once; the set-sized layer re-proves `lexicographic-well-orderings-of-reals`, printed as pointers; nothing heavy); no other archive superseded | 80K1 `c8d3ff5cb`, `5ac948652`, `86267b8a3`; 80K2 `ef114b0bb`, reciprocal `561344322`; 80K3 `d51fafea8`, `0be9b9134`, reciprocal `a13efdd51`; reviews of the same archives in the Hilbert's-tenth research tree by another session (before the writes `abfc0cb25`, `933600302`, `7f1161730`, `c338541e3`, index `e903a3f35`; placement authentication `3aa123856`; audits of the written texts `fbad71e8c`, `280583d2f`, `afb706742`, `a3cf6e939`, `f787251a2`); the publication patch of `fbad71e8c` applied, with the 79J2 review `37a829e0b`, in `7969f7168` | `c4547455f` | — |
| 81 | six archives in two arrival commits (`9a4ce14e9`, `bd599ac06`), one cluster: `f0cd7032d` (81L: five independent follow-ups to the surreal-collection report `foundations-and-computation/surreal-well-orders` as one addition, Parts VI–IX; all five prove its represented-cut theorem by one proof, printed once and credited to all) and `c4720e1b2` (81L2: a sixth, source 18 of the same addition; about half of it re-proves the report and the batch-81 sources, printed as routes and notes); nothing superseded; nothing for the research-report collection | `a3cfa73ca`, `691454089`, `2a9292305` (81L 1/4–3/4, by the placing session), `57d66a24b` (4/4, by the next session); reciprocal `d68b65ea0` | "Catalogue batches 81 to 86" | — |
| 82 | twenty-three archives in one arrival commit (`db37d18c8`), all "Research Reports" of one pipeline built on the Hilbert's-tenth research tree, in four clusters: `bca6383e9` (82M1: Reports 14–19 as the new report `hilbert-tenth-problem/five-particle-binary-automata`; byte copies of earlier Reports and of `quadratic-orthant-certificates` files not staged; eighteen heavy regenerable files, 174 MB, excluded with recipes), `7d2b1b245` (82M2: Reports 21–22 as Part VIII of `signal-machine-collision-certificates`, Reports 20 and 26–28 as Parts V–VI of the new five-particle report; 70 circuit files and a 32 MB source excluded), `2f58ab4e9` (82M3: Reports 23 rev. 1, 24, 25, 33, 34 as the new report `fixed-universal-polynomials`, Report 32 as Part V of `group-theoretic-substrates`; the first edition of Report 23 superseded by its revision, nothing of it staged; a 61 MB circuit DAG excluded; third-party papers not staged), `49dfa8fd6` (82M4: addendum 13 as source 18, the third of Part VI, and Reports 29–31 as Part VII of `signal-machine-collision-certificates`); re-proofs of SMC, QOC, CDC and research-tree results printed as pointers or credited second routes | 82M1 `e6a410588`, 82M3 `72678ed90` (Parts I–IV of `fixed-universal-polynomials`), both by the placing session; by the next session: 82M2 `d2043bbd0`, `9ba11eaf7`; 82M3 `134dfc0c8`; 82M4 `9b3977008`; reciprocal `0f95145cb`; reviews of the same archives in the Hilbert's-tenth research tree by another session (among them `fb7e3cb47`, `32da04296`, `0055e1c4d`, `69730d3e8`, `16f50dcc6`, `7b547f686`, `c875bad40`, `735f62a6a`, `8aabb1453`; relocation-only replay `ceb7222e9`; publication audit `6bf7f30d0`) | "Catalogue batches 81 to 86" | — |
| 83 | sixteen archives in six arrival commits (`b63f0c852`, `3051d1446`, `5ad44b1ed`, `0d7b2441d`, `79049d58c`, `51b0a69d7`), three clusters: `216bd81e1` (83H1: Reports 35–36 as Part XX of `canonical-diophantine-certificates`; 36 re-proves 35's certificate theorem, printed once; 35's machine table equals one in `quadratic-orthant-certificates`, not staged), `a51a439cd` (83H2: Report 37 as Part V of `fixed-universal-polynomials`, Report 38 as the new report `hilbert-tenth-problem/periodic-turmite-first-revisits`), `2e06337d5` (83L: twelve independent surreal well-order follow-ups as Parts X–XIV of `surreal-well-orders`; none an edition of another or of a batch-80/81 source sharing its archive name); nothing superseded | 83H1 `6f2a59d6e`; 83H2 `f4bd591e4`, `c2fe5f03b`; reciprocal `8c5831d55`; 83L `07ee2b30c`, reciprocal `da289d902`; reviews of the four Reports in the Hilbert's-tenth research tree before placement (`c120b34df`, `308f14072`) | "Catalogue batches 81 to 86" | — |
| 84 | `e1395c66c` (seven archives of `06395052a`, all on self-embeddings of `No`: the new surreal-collection report `surreal/surreal-self-embeddings`, base 03, six independent texts; 01 an earlier edition of 05, superseded, nothing of it staged; about half of each re-proves five existing surreal reports, printed as credited notes; after the retraction `f06e67d10` of a false sentence of `omnific-preserving-automorphisms` found by manuscript 07) | `a11efab09`; reciprocal `883e0b3b2` | "Catalogue batches 81 to 86" | — |
| 85 | nine archives in three arrival commits (`317c1ce2e`, `345284ac8`, `9d6968c8a`), three clusters: `713149ded` (85A: Part III of `a189281-path-forest-expansions`, Part II of `a000571-tournament-score-sequences`, the new report `a082528-rounding-extinction`; the A306631 partition-inversion package filed whole under `Analysis/Transseries` as that tree's thirteenth delivery, with its README entry in the same commit), `fa2f3e419` (85B: two independent manuscripts proving the same core theorems merged as the new report `a261781-matrix-compositions`, base 06, with a notation dictionary; one manuscript's claim to prove two posted conjectures narrowed to minimality), `ddf8df5d5` (85C: the new reports `a182220-source-boundary`, `a047874-long-increasing-subsequences`, `a181199-shifted-rectangles`); nothing superseded | 85A `0db483f9e`, `4af956fe0`, `2b3b69b4b`; 85B `60bb2c804`; 85C `eab47e330`, `795c75dbf`, `6fef5383b`; reciprocal `ac33f7ac5`; the drafted pointers into the transseries volumes await that tree's editorial pass | "Catalogue batches 81 to 86" | — |
| 86 | ten archives in three arrival commits (`ae9baa422`, `31fdc6571`, `fb8414869`), three clusters: `0f084afa9` (86A: two multi-subject OEIS manuscripts split by subject: the new report `enumerative-combinatorics/a343093-bridgeless-toroidal-maps`, Parts IV–V of `a088714-bell-scale-growth` with a proof of its Conjecture 8.1, not yet independently reviewed, Part II of `a301981-unitary-divisor-partitions`, Part II of `a321941-asymptotic-coefficient-integrality`; one shared driver staged once), `3d2177df4` (86B: three manuscripts on Glazer's Question 2 as the new surreal report `foundations-and-computation/polish-models-of-omnific-arithmetic`, base 05), `0bd0e5527` (86C: five more, four as Parts III–V of that report, two independent texts sharing a title merged as Part III with base 07, and one as an addition to `surreal/discrete-initial-subgroups-and-omnific-normalization` that corrects a lemma of an external preprint); nothing superseded | 86A `4487535be`, `a46cf8a95`, `3331dfb05`, `e2f253846`; 86B `ae7b9ab74`; 86C `4eed8c460` (the addition), `c3661c2ee` (Parts III–V); reciprocal `3b137a683` | "Catalogue batches 81 to 86" | — |
| 87 | `d151b39ca` (six archives of one arrival commit, `fa0a0576e`: five Glazer/Polish arithmetic manuscripts as Parts VI–IX of the surreal report `foundations-and-computation/polish-models-of-omnific-arithmetic`, two of them proving Part VI's theorem by different proofs, base 03, and Part VIII a claimed, not independently reviewed, ATR₀ answer to Glazer's Question 1; Glazer's box-game paper as the new collection report `ordinals-and-order-types/measurable-box-games`; two provenance files carrying a third party's personal profile URL not staged); nothing superseded | `83926d574` (Parts VI–IX), `5f02820a7` (`measurable-box-games`); reciprocal `8d7d03c3e`; review of the six archives in the Hilbert's-tenth research tree before placement (`f15962acd`) | "Catalogue batches 87 to 90"; corrections `d5bbde040` | — |
| 88 | ten archives of one arrival commit (`c5612efa1`), the pipeline's Research Reports 39–48, in two clusters sharing no theorem: `ed7c76266` (88T1: Reports 40, 42, 44, 47, 48 as Parts II–IV of `hilbert-tenth-problem/periodic-turmite-first-revisits`, answering its question 3 with a literal periodic Langton ant and a fixed polynomial for U15's sentinel-pair halting language, not an ordinary-input loader; Report 44 a recovered edition; 27 heavy regenerable files, about 156 MB, excluded with recipes; seven primitive cell maps derived from a third-party paper's figure sources staged with provenance, not covered by MIT-0), `992aaafb3` (88T2: Reports 39, 41, 43, 45, 46 as Parts VI–VIII of `fixed-universal-polynomials`; Report 46 contains Report 45 whole, staged once; Report 45's main theorem printed as a second route to a research-tree theorem); nothing superseded | 88T1 `119a1325d`; 88T2 `85ea6145d`; reciprocal `f7ca8360b`; reviews of the same archives in the Hilbert's-tenth research tree by another session (`cfbe37de7`, `5d7e884a5`, `5d8889017`, `57a6afbeb`; placement review `70bbc9ce2`) | "Catalogue batches 87 to 90"; corrections `d5bbde040` | — |
| 89 | `23adb85f9` (five archives in two arrival commits, `7c0f2d9f9` and `8ea27d6c0`: Part XV of `foundations-and-computation/surreal-well-orders`, nothing staged; Part X of `polish-models-of-omnific-arithmetic`; Parts VI–VII of `foundations-and-computation/birthday-cutoffs-and-hereditary-sets`; the new collection report `ordinals-and-order-types/naming-elementary-embeddings`, which proves Part VI's Collection spectrum independently, cross-referenced at the writes); nothing superseded | `193e2e942` (Part XV), `c9bc70d8f` (Part X), `e3e58a882` (Parts VI–VII), `aa9a7ec80` (`naming-elementary-embeddings`); reciprocal `fc1ad4275`; routing review in the Hilbert's-tenth research tree before placement (`6aadaa4f2`), and reviews of the writes and notes after it (`2511163a7`, which corrected presentation in two surreal reports; `bcc1a4438` on Part X; `e872d8711` on the notes) | "Catalogue batches 87 to 90"; corrections `d5bbde040` | — |
| 90 | `12076b2e8` (six archives of one arrival commit, `a162e4386`: Parts XI–XII of `polish-models-of-omnific-arithmetic`; source 04 of `surreal/discrete-initial-subgroups-and-omnific-normalization`; Part II of the collection report `measurable-box-games`; Part VIII of `birthday-cutoffs-and-hereditary-sets`; the new surreal report `foundations-and-computation/cantor-families-of-surreal-subfields`; one source record carrying a LinkedIn URL not staged; a `.gitattributes` `-text` line keeps one delivered CRLF table); nothing superseded | `dd26f917c` (Parts XI–XII), `5c32fda02` (source 04), `95527cf73` (Part II), `1404038df` (Part VIII), `6f5f9954c` (`cantor-families-of-surreal-subfields`); reciprocal `e50dde15b`; reviews in the Hilbert's-tenth research tree (the six archives `bcc1a4438`, placement `3c25fbb55`; of the writes and notes `a71bc5aaf`, `5a6ed3cce`, `566365fd8`, `063c1eceb`) | "Catalogue batches 87 to 90"; corrections `d5bbde040` | — |
| 91 | twenty-four archives of one arrival commit (`0d7f51c44`): the pipeline's Research Reports 49–71 (Report 68 never delivered; only its README survives, shipped in `signal-machine-collision-certificates`) and an OEIS pair, in four clusters placed by host: `b0a536b63` (91A: Reports 50, 52–54 as Part XXI of `hilbert-tenth-problem/canonical-diophantine-certificates`; Report 52 bundles Report 50 whole, staged once), `d750d98dd` (91S: Reports 49, 51, 56–67, 69 as Parts IX–XIII of `signal-machine-collision-certificates`; Report 67's heavy evidence excluded with rebuild commands), `22a8ca89e` (91C: Report 55 as Part VI of `group-theoretic-substrates`, its DAG regenerated by its builder; Reports 70–71 as Part VII of `five-particle-binary-automata`), `ec8ae3dc7` (91O: two manuscripts, the second building on the first, as the new report `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196460-clipping-tables`); nothing superseded | 91A `fb2287290`; 91S `61c9e3eb2`; 91C `b93c4a0b5`, `4cabe3899`; 91O `9f924ac47` (guide correction `f0c56034c`); reciprocal `1fdcaf5a6` (the signal-machine report's own in its write); reviews in the Hilbert's-tenth research tree before placement (`49b100cfd`, `a9ab9a698`, `bc6e1a62c`) and of the publications (`316148ed5`, `f135cfb15`, `4187c07d3`, `e92064458`, `5b9101184`; of the reciprocal notes `c529380eb`) | "Catalogue batches 91 to 95"; the a196460 entry first in `d5bbde040` | — |
| 92 | six archives in two arrival commits (`9dc8db274`, `afd7ffabb`), two clusters: `e38f368c2` (92B: three box and hat manuscripts as Parts III–IV of `ordinals-and-order-types/measurable-box-games`; Part IV merges two independent answers to its question 29.2 by one construction, base 06), `e24ce2ce0` (92A: three as Parts XIII–XV of the surreal report `foundations-and-computation/polish-models-of-omnific-arithmetic`; Part XV shows Kuhlmann–Serra's Lemma 4.2.4 false as stated, printed with the counterexample); nothing superseded | 92B `721cf8196`; 92A `4af6f191d`; reciprocal `9bffd43d5`; reviews in the Hilbert's-tenth research tree (placement `e663441d7`; publications `42b49fdbd`, which refuted the write's new open-range sentence, and `c3da7b57a`; reciprocal notes `fa3ead76f`, which restored two hypotheses) | "Catalogue batches 91 to 95" | — |
| 93 | six archives in two arrival commits (`2faa3b37a`, `de37a66d1`), two clusters: `5e4d8eed8` (93B: two as Parts XVI–XVII of `polish-models-of-omnific-arithmetic`), `47a77daba` (93A: one as Part II of `ordinals-and-order-types/naming-elementary-embeddings`; three as Parts II–III of the surreal report `foundations-and-computation/definable-surreals-and-omnific-integers`, two independent manuscripts proving one core merged as Part II, base 02); nothing superseded | 93B `9a8894d0a`, Lean-scope correction `b8bc36acc`; 93A `8a7f289b8`, `c7d65e30b`; reciprocal `c70ced0dd` (those into `birthday-cutoffs-and-hereditary-sets` in `abba38172`); reviews in the Hilbert's-tenth research tree (`4187c07d3` on the definable-operations archive, `f135cfb15` on the 93A placement; publications `c3da7b57a`, `0bb0baf45`, `341c9f187`, the last two correcting guide wording) | "Catalogue batches 91 to 95" | — |
| 94 | five archives in two arrival commits (`bd1de458b`, `516049bf9`), all complex-transseries articles, filed whole under `Analysis/Transseries/docs/series-and-transseries` as its fourteenth delivery: `ec91f8c7c` (94A: three), `6132faa30` (94B: two new articles, not editions of 94A's; one refutes the directional clause of the q-Pochhammer monograph's `conj:cyclotomic-resurgent-inverse`, corrected in `7389d7de4`); `ec91f8c7c` also added batch 95's archives 01 and 02, which its message does not mention | — (merge into the volumes deferred); reviews in the Hilbert's-tenth research tree (arrivals `f135cfb15`, `196e11d19`; the conjecture correction `d04b13cf6`) | in the placement commits | — |
| 95 | four archives (01 and 02 added by `ec91f8c7c`, 03 and 04 in `f300069cf`), two clusters: `350b9a954` (95A: two independent answers to one assignment as Part IX of the surreal report `foundations-and-computation/birthday-cutoffs-and-hereditary-sets`, base 01, nothing of 01 staged), `05304d5ec` (95B: two transseries articles, independent answers to one assignment and not editions, filed whole as the fifteenth transseries delivery); nothing superseded | 95A `abba38172` (with the batch-93 reciprocal notes into that report), reciprocal `ddb36da6c`; 95B — (merge into the volumes deferred); reviews in the Hilbert's-tenth research tree (all four archives `196e11d19`; the 95B placement `b8b4c92e9`) | "Catalogue batches 91 to 95" (95B in its placement commit) | — |
| 96 | eleven archives in six arrival commits (`62846e17a`, `7be14aa84`, `fb9f5884b`, `26e036956`, `78528873b`, `e3839ad2c`), four clusters: `635a3e026` (96B: Part V of `ordinals-and-order-types/measurable-box-games`; the manuscript's finite-public hypothesis false as worded, corrected at the write with a counterexample), `27f200305` (96C: two independent manuscripts answering one question merged as Part III of `ordinals-and-order-types/naming-elementary-embeddings`, base 05; 05's figure staged in `figures/`), `54ece48ab` (96A: four manuscripts, none an edition of another, as Parts XVIII–XXI of the surreal report `foundations-and-computation/polish-models-of-omnific-arithmetic`), `111c38012` (96D: four independent answers to one request merged as Part XVI of the surreal report `foundations-and-computation/surreal-well-orders`, base 10); nothing superseded; manuscripts, PDFs and delivery READMEs kept only in the arrival commits | 96B `a21208b3f`; 96C `03683e579`; 96A `20262718e`; 96D `62b16914e`; reciprocal `90b2d40e6`; reviews in the Hilbert's-tenth research tree (archives `8dffc7af0`, `3abf23ba1`, `3d87c3d6b`, `18825ee16`, `1eab36bb3`, `556836e9b`, `fcc4098ec`, with the effectivity note `c6082d075`; placements `608e06daa`, `b16786caf`, `ccb0bba7f`; the hat-seed correction confirmed in `c52f7d055`; publications `47ab39154`, which refuted two sentences of the 96B write (Remark 75.9), `6d78c238d` with the guide correction `6d06f8952`, `9280aa6d4`, which corrected three editorial statements of the Polish report, and `ec4b972db`, three metadata claims of Part XVI) | "Catalogue batches 96 to 108 and 114" | `a21a42d8c` (independent check of the 96D write, recorded in the 97A write: four Part XVI statements repaired) |
| 97 | seven archives in two arrival commits (`d7cf7d554`, `e88ed8bf6`), four clusters: `6571ee1af` (97A: a fifth answer to batch 96D's request, arrived after that placement, printed whole as Part XVII of the surreal report `foundations-and-computation/surreal-well-orders`), `a4542b8a3` (97G: Section 17 of `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a279619-level-seven-gamma-constant`; its OEIS draft staged as data, never submitted), `41f53f7d8` (97F: three packages filed whole in the Fabius drafts tree, in `rvachev_up_fourier_decay/`, `representations/` and `spectra-and-arithmetic/`; claim review deferred to the editorial pass), `5a69916e8` (97H: Parts IV and V of `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions`, two additions sharing no theorem; one requirements file a byte copy, not staged); nothing superseded; CRLF CSVs of 97F, 97G and 97H kept by `.gitattributes` `-text` lines | 97A `a21a42d8c` (with four corrections to Part XVI; merged with a concurrent review in `5908f9de7`); 97H `eea159818`; 97G `3412ae074`; reciprocal `c04452509`; reviews in the Hilbert's-tenth research tree (the six analytic archives `37af2f0d6`; the 97A archive `39bb02ece`, its placement `cd4799536` and publication `65969409c`, which corrected three guide claims of Part XVII and empty-domain cases of Part XVI; the 97H publication `8bba916ca`, a notation repair) | "Catalogue batches 96 to 108 and 114" | `57ccadf2d` (Subsection 17.10: no gap, one sentence added); `f70ab0c7d` (two links, the Apéry Part III description, a note date) |
| 98 | twelve archives in two arrival commits (`2172df76a`, eleven; `1ec443bc4`, the late twelfth), in four clusters, every manuscript a new Part of an existing collection report: `9353a7171` (98A: Part III of `a000571-tournament-score-sequences`, Part II of `enumerative-combinatorics/valley-monotone-bargraphs`, Part II of `a122399-surjection-diagonal`), `0fba5167f` (98B: Part II of `a181199-shifted-rectangles`, two overstatements of its manuscript to be corrected at the write; Part II of `a033552-catalan-partitions`, two independent manuscripts merged, base 06; Part II of `enumerative-combinatorics/a273821-first-pattern-failure`; Part III of `a261781-matrix-compositions`; Part II of `a238016-restricted-partitions-cubic-boundary`; three byte copies not staged), `b50febf79` (98C: two independent answers to Part I's Question 1 merged as Part II of `a182220-source-boundary`, base 05), `3b9458b31` (98D: the late arrival as Part II of `a357825-theta-ballot-power-sums`, nothing staged, its package being the article and PDF only; one identity of it false as printed); articles, PDFs, delivery READMEs and checksum manifests not staged; 53 CRLF files kept by `-text` lines; none to `Analysis/Transseries`; nothing superseded | 98A `a763feee1` (Part III), `abdad4eef` (bargraphs), `77fff37e3` (a122399); 98B `b71545625` (a181199; its Parts III–V with batch 101), `b21eab238` (a033552), `246175583` (a273821), `324818ddb` (a261781), `a4198a037` (a238016); 98C `ed438414b`; 98D `2b257ba94`; reciprocal `639b038ab` (with batch 100) | "Catalogue batches 96 to 108 and 114" | `1ee6d763b` (bargraphs: Lemma 19.1 uniqueness range widened), `1fffcbef0` (a122399: impossible regime in necessity note), `f00cfc175` (a033552: no correction), `ed8e73df9` (a181199: no correction), `cf204d897` (a238016: one decimal, inverse step order), `978b52fb5` (a182220: Corollary 21.7 added, two values corrected), `2ff7e46eb` (a357825: two wording fixes); a000571, a273821 and a261781: check pending |
| 99 | `9985d6ed6` (thirteen archives of the session bundle `60f54ea06`, all filed in the `thue-morse/` group of the Fabius drafts tree by its quick intake: five trace parts, a byte copy of the batch-72 package and a checker repair for `Thue_Morse_Integer_Pressure_Feedback_Boundary`, five interval parts for `Thue_Morse_Integer_Pressure_Full_Range`, and the new package `Thue_Morse_Integer_Pressure_First_Return` (Report 80); the 68 traces and 110 interval files, regenerable and kept in the arrival commit, not staged) | — (claim review deferred to the Fabius editorial pass) | "Catalogue batches 96 to 108 and 114" (nothing for the two collections) | — |
| 100 | `36571ae0e` (eleven archives of the session-bundle arrival `60f54ea06`, in seven clusters: Report 59 as Part IV of `oeis-sequence-asymptotics/power-tower-exponent-supports`; Report 81 as Part VI of `log-concavity-and-unimodality/matching-rank-normalization`; Reports 89 (base), 82 and 93 as Sections 21–22 of `a022629-distinct-partition-norms`; the new reports `a126348-stable-hilbert-series` (Report 84), `a007716-bipartite-multigraphs` (Reports 88, base, and 92, its sequel), `a271619-strict-twice-partitions` (Reports 182, base, and 181) and `a307316-leafless-multigraphs` (Report 131); PDFs, checksum manifests, byte copies, Report 81's prerequisite archive (its host's source 05), three of its files over 1 MB and Report 182's 1.43 MB coefficient table not staged; seven `.log` records force-added; one `.gitattributes` `-text` line keeps a delivered CRLF TSV); nothing superseded | `231237c5c` (a126348), `26088828f` (a307316), `f4dabd895` (Part VI), `72091374c` (a007716), `aa4a1136f` (a271619), `1b247299e` (Part IV), `2ef752171` (Sections 21–22); reciprocal `639b038ab` (with batch 98) | "Catalogue batches 96 to 108 and 114" | `f8accf37c` (a126348 truncation error corrected; matching-rank Remark 46.1 and a307316 Proposition 9.1 valid), `0c81c51e2` (Part IV outlook restricted to 1/2 ≤ a < 1), `342a4583e` (a271619 completions valid, one justification added), `91ef1ef6f` (a022629 theta-shift order claim corrected) |
| 101 | `f7c612c72` (thirteen archives of the session bundle `60f54ea06`, in eight clusters, all OEIS asymptotics: Reports 231, 233, 85, 91 as Parts III–V of `a181199-shifted-rectangles`; 90 (base) and 86 as Part VI of `a215561-fixed-composition-excursions`; 87 and 94 as Parts III–IV of `a113226-vincular-avoiders`; 95 as Part III of `a126764-lconvex-polyominoes`; 98 as Part III of `a330266-balanced-smirnov-poisson`; 83 and 232 as Parts VI–VII of `a189281-path-forest-expansions`, 232 overturning its triage as a new report; 96 as the new report `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196275-column-convex-permutominoes`, its two byte-identical 1.26 MB exact-count tables excluded as regenerable; 154 files staged; manuscripts of the additions, PDFs, delivered READMEs and checksum manifests not staged); nothing superseded | `5a1d923db` (a196275), `a75a4e41b` (a330266), `07fd071f8` (a113226), `e9994117b` (a189281, with the a330266 reciprocal notes into it), `e8055d890` (a126764), `013b32fca` (a215561), `ca1668212` (a181199); reciprocal: in `e9994117b`; the notes into `a181280-binary-matrix-formula` and `a357825-theta-ballot-power-sums` not yet applied; bounded review in the Hilbert's-tenth research tree `e5e401a81` | "Catalogue batches 96 to 108 and 114" | `39b1110a6` (profile bound sharpened to exact distance), `07068a4b9` (unequal-rank proposition wording tightened), `af05d23ba` (Lemma 28.1 edge constant sharpened), `a368aed3c` (false reversion-term decay sentence corrected), `aab6be85d` (three wordings refined, no number changed), `9830327b9` (enclosure checks c_11, not c_12), `6e4dbcd38` (lower-degree higher-order recurrences proved) |
| 102 | `6ab1f1979` (thirteen archives of the session-bundle arrival `60f54ea06`, bundle Reports 97, 99–105, 107, 108, 241–243, six clusters, all in `oeis-sequence-asymptotics`: Report 97 as Part V of `a202058-ascent-000-growth` and Report 99, which generalizes it, as Part III of `a294220-ascent-multiplicity-caps`; Reports 100, 101, 103 as Part V of `a082161-airy-amplitudes`; Reports 104 (base) and 102 as Parts III–IV of `a213863-tree-child-networks`; the new reports `a202059-ascent-100-110-growth` (Reports 243, base, and 241, which keeps priority for the refutation of a published conjecture), `a098569-self-modified-ascents` (Report 242) and `a336070-weak-ascents` (Reports 105, base, 107, 108; 108's Sections 3–4 are 107's, printed once); manuscripts of the additions, PDFs, checksum manifests, byte copies and 154 empty run records not staged); nothing superseded | `3daaab24e` (`a098569`), `3ed50db4e` (`a202059`), `32122c09e` (`a336070`), `b71fda5be` (`a202058` Part V, `a294220` Part III), `7e85b5a0c` (`a213863` Parts III–IV), `3e71ff1e6` (`a082161` Part V); reciprocal: none separate (the cross-references are in the writes; pointers from `a202061` and `a202062` drafted, not applied); relevance review in the Hilbert's-tenth research tree `c6dea60c7` | "Catalogue batches 96 to 108 and 114" | `811ad87f0` (C₁ sign change at 15,865; Report 243 credit narrowed), `5ada42e2f` (Report 242 implies the sum estimate only), `71f343e25` (`i ≥ 1` range; real `d` coefficient `⌈d⌉/2`), `edb875773` (two clarifications, no correction), `84cd75b5a` (three wording refinements, no correction), `c5fcc3348` (Corollary 66.3's two dependencies stated) |
| 103 | `9c995cefe` (eleven archives of the bundle arrival `60f54ea06`, bundle Reports 106, 109–117 and 130, in seven clusters, all in `oeis-sequence-asymptotics`: Report 112 as Part III of `a377922-corner-polyhedra-schnyder`; Reports 113, 115 and 117 as Parts II–IV of `a333497-historic-trees` (second routes to Part I, and A333497 and A336009 not P-recursive); Report 130 as Part II of `a116379-bounded-identity-trees`; the new reports `a135501-closed-lambda-terms` (base 110, with 109), `a348351-one-sided-rectangulations` (111), `a008608-tesler-matrices` (106) and `a345470-self-complementary-scores` (base 116, with 114; a new report, not Parts of `a000571-tournament-score-sequences`, overturning the triage call); both self-complementary manuscripts copy Denisov–Wachtel's misprinted limit density, mass `0.1154…`; manuscripts of the additions and merged members, PDFs, checksum manifests, byte copies and Report 130's two regenerable coefficient exports not staged; nine delivered `.log` records force-added); nothing superseded | `0c2cdf435` (`a348351`), `17d995b94` (`a008608`), `9b4001d29` (`a377922` Part III, with `a348351`'s reciprocal notes), `6603ab5a8` (`a333497` Parts II–IV), `1b792e07a` (`a345470`, the density corrected), `b432720bf` (`a135501`), `a2dc5d320` (`a116379` Part II, the Furnas misattribution corrected); reciprocal: no separate commit (the `a000571` pointer to `a345470` drafted, not applied); reviews in the Hilbert's-tenth research tree of the lambda archives and publication (`c0cb99917`, `ca8221993`, `f5b09f57d`, `479871ca4`) and an extension of its Proposition 18.2 (`a8455335c`) | "Catalogue batches 96 to 108 and 114" | `019cf8e50` (`a348351`: no defect; `δ_t` range, Pringsheim step), `42c8a99c8` (`a008608`: O'Neill numbering; margin-sharpness proof completed), `f8bcc8515` (`a377922`: half-scale table rows, one coefficient), `0c4719e03` (`a333497`: Weiss–Margaliot replacement scope; Mallet-Paret–Smith signs), `24e36bc20` (`a135501`: three sentences; Proposition 18.2 added), `f1c0e8d8c` (`a135501`: Proposition 18.2 range, large `N`), `78a7cef4a` (`a345470`: walk computation replaces Monte Carlo; `A ≈ 0.0374`), `1cb706454` (`a116379`: mistaken criticism withdrawn; one digit) |
| 104 | `612787fb4` (twelve archives of the bundle arrival `60f54ea06`, bundle Reports 118–129, in two triage clusters, all in `oeis-sequence-asymptotics`: the eight-source Britt–Beaton inversion-sequence cluster split by method into three new reports, `a279544-inversion-kernel-classes` (base 118, with 119 and 122), `a279571-inversion-cone-walk` (base 125, with 123, whose exponent follows from the proof, not the statement, of `a377922`'s cone theorem) and `a279551-inversion-log-deficit` (base 129, with 127 and 126, printed in dependency order; Britt–Beaton's numerical `n^(3/8)` forms refuted); four A005163 manuscripts as the new report `a005163-diagonally-symmetric-asms` (base 128, with 124 in full, 121 and 120); PDFs, member manuscripts, delivered READMEs, checksum manifests, embedded copies and byte copies of repository files not staged); nothing superseded | `37c5ebe97` (`a279544`), `ed4d0a12f` (`a005163`), `80adcb910` (`a279551`), `4d3a6730f` (`a279571`); reciprocal `32919c4cf` (`a377922`, `a348351`, `a202061`); reviews in the Hilbert's-tenth research tree of the A279551 publication (`76e197985`) and, with batch 105, for computational relevance (`97b95bd35`) | "Catalogue batches 96 to 108 and 114" | `cc8144111` (`a279544`: Part III's inverse has no `W₋₁`), `77cec68db` (`a005163`: weak interlacing; three evidence statements), `b54142448` (`a279551`: two mis-rounded residual-table entries), `1c7e526c7` (`a279571`: no correction) |
| 105 | `e85586b7c` (thirteen archives of the bundle arrival `60f54ea06`, bundle Reports 134–146, all in `oeis-sequence-asymptotics`, as four new reports: `a217057-unique-pattern-occurrences` (base 137, with 134, 135, 136, 138 and 140: one 1234, 1243 or 12345; Report 134 refutes Conway–Guttmann's `R = 1/2`), `a224182-unique-1432-order` (139 alone, its method unrelated), `a292692-weighted-dyck-newton-diagonal` (base 142, with 141 and 143) and `a398540-proportional-placement-game` (base 146, with 144 and 145; 146 corrected in place before delivery, the earlier version never received); Nakamura–Zeilberger's `oF12345a` staged with attribution; PDFs, member manuscripts, delivered READMEs, checksum manifests and embedded byte-identical copies not staged); nothing superseded | `42721c521` (`a292692`), `0480c6184` (`a398540`, Serra's prefactor and three further statements refuted), `bb5ca9433` (`a224182`, the placement's MRR attribution and "rising" ratio qualified), `84c52f028` (`a217057`); reciprocal `c8fd19e36` (`a217057`, `a224182`, `a047874`); relevance triage in the Hilbert's-tenth research tree (`97b95bd35`) | "Catalogue batches 96 to 108 and 114" | `159c9a901` (`a292692`: false positivity note at `m = 0`), `c5f63aa29` (`a398540`: Serra's Step-2 ansatz amplitude; transseries wording), `c437f27be` (`a224182`: three wordings), `a4f4d8ceb` (`a217057`: two wordings; refutation rerun) |
| 106 | `47fc7a069` (twelve archives of the bundle arrival `60f54ea06`, in five triage clusters, as seven new collection reports in `generating-functions-and-asymptotics/oeis-sequence-asymptotics`: bundle Reports 149 + 151 → `a347546-alternating-baxter-involutions` (base 149; correcting Min's 2021 recurrence and 21 OEIS terms), 150 + 152 → `a156808-circle-graphs` (152 a sequel), 153 → `a123448-permutation-graphs`, 133 → `a005975-interval-graphs`, the three graph reports kept apart (shared pipeline, no shared statement), 147 + 148 → `a252782-diagonal-euler-transforms` (base 147; refuting the OEIS `e^{1/e}` conjecture), 225 + 226 + 228 → `a290354-iterated-euler-diagonals` (dependency order; not a Part of `a139383-iterated-bell-diagonals`), 223 → `a005121-strict-partition-chains`; embedded copies of Reports 147, 149, 225 and 226 byte-identical and not staged; PDFs, delivered READMEs and checksum manifests not staged; its claims that Report 153 carries "prepared for private review" and answers Johnston's `o(n!)` question corrected at the write (the phrase occurs in no delivered file; Bassino et al. 2024 answered the question first, Report 153 adds the constant `1/4` and all orders); nothing superseded) | `8f7baed2b` (a252782), `c6557f9c9` (a156808), `742754a50` (a347546), `44ebdfef9` (a005121), `6fb3059e5` (a123448), `c6488293e` (a005975), `84fc1aaed` (a290354); reciprocal `3f9fc9d4f` | "Catalogue batches 96 to 108 and 114" | `3065f0ccf` (Theorem 7.2 an instance, not analogue), `686e1e3ba` (side condition holds for every `L > 0`), `63482555d` (half-index clarified; Min-list values direct counts), `cfc13c377` (OEIS-sign remark sharpened; depth gap explained), `b62ef2422` (1990 `a_20` double-format note; Johnston wording qualified), `20fdce33d` (extrapolation-window range of `b_0` fits corrected), `a3a2d5582` (Part II interface novelty overstated, not new) |
| 107 | `3988bf5c4` (eleven archives of the bundle arrival `60f54ea06`, bundle Reports 154–156, 158–160, 162, 163, 165, 205, 207, in four triage clusters, all as new reports under `generating-functions-and-asymptotics/oeis-sequence-asymptotics/`: 107-DIAGP (Reports 156, 159, 158, 160, 162 merged as `a238873-diagonal-partitions`, base 156, Parts in dependency order, Part V conditional on the preprint arXiv:2607.27504v1; Wiseman's A238873 conjecture, given there as addressed by no source, was proved by the write, the same argument credited to Garrot in A387112), 107-STIRL (154, 155 merged as `a192563-factorial-stirling-products`, base 154, one OEIS family, different methods), 107-STCAT (205, 207 merged as `a064856-stirling-catalan-transforms`, base 205 in its corrected revision 2, revision 1 never received; its generated TeX inputs staged under `data/`), 107-PART1 (163 as `a068598-disjoint-partition-families`, 165 as `a067590-odious-evil-partitions`, both staged unprefixed); PDFs, member manuscripts, delivered READMEs and checksum manifests not staged); nothing superseded | `0ca2804be` (a238873), `715fb82db` (a067590), `ea25dd768` (a064856), `774c233c4` (a192563), `6e53455cf` (a068598); reciprocal: none committed (the drafts find none required; optional pointers into `a082161-airy-amplitudes` and the Thue–Morse atlas not applied) | "Catalogue batches 96 to 108 and 114" | `8be867096` (a238873: "decays like" was an upper bound), `45f6ef541` (a064856: volume's `h` separated from `h(ρ)`), `56d6dd98c` (a068598: Simkin interval, block-construction sentence), `1af8a89a5` (a192563: no correction; a non-claim widened), `383dd42ce` (a067590: three Lean citations made precise; `K₋`'s printed digits interval-enclosed) |
| 108 | `602e5bd0f` (thirteen archives of the bundle arrival `60f54ea06`, bundle Reports 132, 157, 161, 164, 166–169, 184, 194, 236, 238, 239, in four triage clusters, all under `generating-functions-and-asymptotics/oeis-sequence-asymptotics/`: 108-POP (Reports 164, 161, 166 merged as `a307030-pop-stacked-permutations`, base 164, file prefixes `164-egf-`, `161-operator-`, `166-runs-`; CGP's printed pole list omits `ρ₁₂`; Patel's prior proof credited by 166, unread at intake, read and checked at the write), 108-A261781 (169 as Part IV of `a261781-matrix-compositions`, prefix `08-packed-`, second routes plus a joint Gaussian–Poisson law), 108-MISC (157 as `a397711-bounded-indegree-dags`, 167 as `a308338-nested-cycle-assemblies`, which proves the boxed `E[X] ~ N√n` of Riedel's note, `N = e^(−γ/2)`, and meets the Erlihson–Granovsky (4.54) negative variance; the placement message misquoted the note as `N n^M` with fitted `M ≈ 0.4705`, corrected at the write), 108-MATR (132, 168, 184, 194, 236, 238, 239 as seven single-source reports: `a299907-lonesum-decomposable-matrices`, `a197458-line-sum-two-matrices`, `a089479-fixed-permanent-matrices`, `a222959-zero-slope-matrices`, `a110058-square-contingency-tables` (its Canfield–McKay claim narrowed to one regime), `a138178-symmetric-packed-matrices` (separate from a261781), `a027832-symmetric-sign-matrices` (two stray CR bytes kept by a `-text` attribute until the write repaired them)); 184 and 194 cite unshipped implementations; PDFs, member manuscripts, delivered READMEs and checksum manifests not staged); nothing superseded | `ab4e30d32` (a261781 Part IV), `12013349a` (a307030; CGP's pole list and complex pairs corrected with proof), `e5152f378` (a397711), `399df8a49` (a308338; Riedel's conjecture proved, Erlihson–Granovsky's display corrected), `6ef3f0983` (a299907), `3e9c7ae10` (a222959), `3834812cd` (a197458), `71813ce3f` (a089479), `d63de7211` (a110058), `b5026035f` (a027832; CR bytes repaired, `-text` line removed), `c569b0b98` (a138178); reciprocal `2d0c65ab2` (a082161), `dfd51a4af` (a238873), `a5baee363` (a182220), `5f354ade2` (a116379, README only), `2cf326693` (a122399), `0c79ec1b7` (a260700), `0fe578e64` (a380592), and `7fe061402` (a321941's stale A000262 sentence, README only) | "Catalogue batches 96 to 108 and 114" (placed state); "Catalogue batches 108 to 125" (written state) | `0961de7b7` (a261781: "settles one instance" → "answers an analogue"), `0b6cb9c59` (a307030: the write's ABH Theorem 11 correction withdrawn; ρ₁₂ printed as a truncation), `3efeb45ac` (a397711: Remark 6.1's fit reading withdrawn), `25df8755d` (a308338: E–G (5.72) holds only for `C = 1`), `a77c67139` (a299907: no error, `c₄` stated), `3e37daf93` (a197458: one false sentence of Remark 7.3(b)), `7ca6d36e5` (a089479: no error, joint orbits A003087), `988e20e71` (a222959) and `9e23adc2a` (a110058: their inverses also Lambert-W template instances), `8687b782b` (a138178: no error, `C₃` confirmed numerically), `28b48d027` (a027832: no error, two README roundings) |
| 109 | `f7e9e5c2f` (eleven archives of the bundle arrival `60f54ea06`, bundle Reports 170–179 and 219, in four triage clusters, all as new reports under `generating-functions-and-asymptotics/oeis-sequence-asymptotics/`, placed after the catalogue `e2dec1a59` so that its count stands: 109-KINGS (Reports 174, 173, 175 merged as `a137432-maximum-density-kings`, base 174, prefixes `174-aspect-`, `173-square-`, `175-planar-`; not an addition to `a201513-sparse-chess-placements`), 109-BISHOP (219 as `a002465-nonattacking-bishops`, not a Part of a201513, whose theorem assumes a finite move set), 109-TRIP (176, 178 merged as `a297487-tripartite-maximal-matchings`, base 176, prefixes `176-balanced-`, `178-boundary-`), 109-MISC (170 as `a097998-outerplanar-graphs`, correcting the BGKN 2007 Theorem 5.1 amplitude by `9/4`; 171 as `a324312-planar-eulerian-orientations`, its regenerable 3.0 MB `exact.json` not staged; 172 as `a397045-square-root-sums` (`dsr:` taken, labels `srs:`), the entry's radicand comment refuted at `n = 2`; 177 as `a262810-diagonal-alignments`; 179 as `a328716-lazy-closed-walks`); shared helper files staged once; PDFs, member manuscripts, delivered READMEs and checksum manifests not staged); nothing superseded | `3625d8199` (a137432; the A137432 conjecture proved), `8dacae7a7` (a297487), `e1db00e99` (a002465), `20fa679b0` (a097998; BGKN's amplitude, introduction and preprint value refuted with proof), `05dcc17a8` (a324312), `b1a39e80f` (a397045; the conjecture proved, the OEIS comment refuted), `b7a7eb374` (a262810), `f3fb85cb6` (a328716; Kotěšovec's A328718 row conjecture proved); reciprocal `ec0175d5d` (a201513, for a137432 and a002465; the other writes found none required) | "Catalogue batches 108 to 125" | `80177120d` (a137432: fixture SHA-256 = Matsuo's table; three rounded digits, one range), `60d3c10df` (a297487: two quotation sources), `ae0721fd9` (a002465: Santos's Theorem 6), `3e8dd96be` (a097998: correction confirmed; BGKN Theorem 3.6 misprint; series-parallel constants questioned), `1e631c991` (a324312: citation note in every version; the authors' later view of Proposition 8.3), `356cc7fe4` (a397045: one inference, a theorem's letters), `07600efc8` (a262810: one route claim qualified), `1ba9be08f` (a328716: the `1/N` term made explicit) |
| 110 | `8622ca7e5` (twelve archives of the bundle arrival `60f54ea06`, bundle Reports 180, 183, 185–193 and 211, in five triage clusters, and `Periodic_Rounding_Extinction.zip` (`e4d5dcf9e`), held from batch 114: Parts II and III of `a082528-rounding-extinction` (files `02-rates-`, `03-schedules-`), and eight new reports under `generating-functions-and-asymptotics/oeis-sequence-asymptotics/`: `a330499-decorated-eta-products` (185 base, 211), `a094925-spiral-fibonacci` (190 base, 191), `a096537-exponential-towers` (192 base, 193), `a386381-modified-entringer` (180), `a394326-tableau-defect-clusters` (183), `a065094-rounded-running-means` (186), `a326805-square-root-factorial-sampling` (187), `a098131-minimum-length-compositions` (189); the A096537 amplitude, A096542's `T(n,1)` and A394326's two formulas recorded as refuted, for the writes; four CRLF CSVs of Part III kept by `-text` lines; 323 files staged); `f6b774865` retired the last archive, which git's rename detection had left out of the placement; nothing superseded | `7fe078b25` (a082528 Parts II–III; the host's questions on rates and schedules answered), `bb51b57e3` (a330499; A330498's `log 2` proved), `d30bfb2a3` (a094925; Scheucher's equivalents proved, his heuristic form refuted), `cff2b48aa` (a096537; A096537's amplitude and A096542's formula refuted), `e378a2d67` (a386381), `5d3107954` (a394326; both formulas refuted), `1ebd8c33c` (a065094; both Bessel conjectures proved), `6ec1f3f92` (a326805; Kotěšovec's conjecture proved), `89b899bf3` (a098131); no reciprocal note required | "Catalogue batches 110 to 137" | `f0ae397ee` (a082528: archive sizes, an intake band, one perturbation sentence), `60860dd40` (a330499: one notation attribution), `ef1d91e4f` (a094925: one provenance date), `7781110bc` (a096537: one sentence qualified), `3d6e73ab1` (a386381: one provenance sentence), `e98226347` (a394326: the residual comment proved for `n ≥ 30`), `fc8a50c68` (a065094) and `fe3862203` (a326805: Lean declaration names), `d980a69f2` (a098131: one transseries statement) |
| 111 | `d451ef3d8` (eleven archives of the bundle arrival `60f54ea06`, bundle Reports 195–199, 201, 202, 204 and 216–218, in three triage clusters, as five new reports under `oeis-sequence-asymptotics/`: `a239950-maximal-schreier-supports` (195), `a239964-sizes-equal-max-multiplicity` (196), `a373271-distinct-multiplicity-values` (197 base, 198), `a350879-extreme-part-conditions` (216 base, 217, 218), `a290569-power-weighted-dyck-moments` (201 base, 199, 202, 204); A350879's alternative form recorded as refuted and A338634's parity conjecture as proved, for the writes; two regenerable data files over 2 MB not staged; 154 files staged); nothing superseded | `a0d4f816a` (a239950), `4b5cfc9b1` (a239964), `0064d11e6` (a373271, Parts I–II), `27ecec221` (a350879; Kotěšovec's first form refuted, A117086 shown strictly increasing), `fb9602e55` (a290569; A338634's conjecture proved, the Kriecherbauer–McLaughlin trust boundary disclosed); no reciprocal note required | "Catalogue batches 110 to 137" | `57a8055a0` (a239950: one OEIS attribution, two precisions), `54212e64a` (a239964: two precisions), `a03243ec3` (a373271 Parts I–II: one precision), `afddc5983` (a350879: one provenance statement), `45a31a828` (a290569: a b-file claim corrected, one attribution made precise) |
| 112 | `f79c9bef1` (twelve archives of the bundle arrival `60f54ea06`, bundle Reports 200, 203, 206, 209, 210, 212–215, 222, 227 and 229, in three triage clusters, as seven new reports under `oeis-sequence-asymptotics/`: `a094149-sparse-graph-moments` (214 base, 213, 212, 210, 209; not added to `a064856-stirling-catalan-transforms`, which names them as leads), `a055779-labeled-fat-trees` (203), `a003238-uniform-trees-binary-partitions` (215), `a242375-many-color-rooted-trees` (222), `a244407-high-outdegree-rooted-trees` (227 base, 229), `a001425-commutative-magmas` (200), `a340021-distinguished-maximal-independent-sets` (206); Kotěšovec's A242249 conjecture recorded as proved and Cloitre's A003238 conjecture as refuted, for the writes; Report 229's embedded copy of 227 and Report 200's 4.2 MB `fixed_counts.json` not staged; 212 files staged); nothing superseded | `e4199e04f` (a094149), `b76f517a4` (a055779), `37b523e32` (a003238; Cloitre's conjecture refuted, Erdős–Loxton's question answered), `d53b7fbd4` (a242375; Kotěšovec's A242249 and A255517 conjectures proved), `155fb997d` (a244407), `7f470df1e` (a001425), `0c4f9054d` (a340021); reciprocal `f8f9eb33b` (a064856, with batch 113) | "Catalogue batches 110 to 137" | `5f0331dc8` (a094149: one OEIS quotation completed), `0f10e9822` (a055779: the write's value of Kotěšovec's `p`), `b978b0cd8` (a003238: the radial sieve checked by other means), `879bb7ef3` (a242375: one instance claim qualified), `31111c548` (a244407: no correction), `f68e935fe` (a001425: one OEIS citation), `a2fe3ed38` (a340021: a preamble package recorded) |
| 113 | `a4186a946` (nine archives of the bundle arrival `60f54ea06`, bundle Reports 208, 220, 221, 224, 230, 234, 235, 237 and 240, in two triage clusters, as eight new reports under `oeis-sequence-asymptotics/`: `a360592-self-powered-binomial-sums` (230 base, 235), `a386374-first-block-maximum` (208), `a173217-ordered-tuple-relations` (220), `a332709-fixed-couple-menage` (221), `a060053-two-covers-line-graphs` (224), `a368246-cycle-minima-sums` (234), `a104779-total-kostka-sums` (237; not a Part of `a138178-symmetric-packed-matrices`), `a323297-singleton-free-hypergraphs` (240); the first corrections of A360592, A360479 and A360747 and A132219's `a(4) = 66` recorded as refuted, for the writes; Report 220's two findings on the transseries volume's Fubini chapter repaired there in a commit of their own, `d92db8d06`; 188 files staged); nothing superseded | `a0bec1539` (a360592; three OEIS first corrections refuted), `20f872d12` (a386374), `7ad0ec8ab` (a173217), `b353bba89` (a332709; both A332709 conjectures proved, the expansion reading of the A258667 conjecture refuted), `43e0c9a22` (a060053; A132219 shown not to count line graphs), `f24d4b02b` (a368246; Kotěšovec's conjecture proved), `c95388b8e` (a104779), `8748cfc59` (a323297); reciprocal `f8f9eb33b` (a260700, with batch 112) and `0603ceb9c` (a138178 and a260700, for a104779) | "Catalogue batches 110 to 137" | `2a7fce071` (a360592: one duplicate PDF destination), `21e010ada` (a386374: two finite ranges), `d42f42690` (a173217: A000670's conjectures, a line count; the same missing constant in `q2:thm:weighted`, repaired in the volume by `08bc7a5c8`), `492aa527e` (a332709: A258664–A258666 and A258673 settled the same way), `7a1ff0c36` (a060053: two precisions), `ff6f743ac` (a368246: a file count, one "proved" qualified), `de043efe1` (a104779 and its reciprocal notes: a third exponentially small effect), `ea5241c74` (a323297: one OEIS comparison) |
| 114 | `99053b5d1` (seven of the eight archives of two non-bundle arrival commits: `binary_morphic_fluctuations` and `Digit_Sum_Divisibility_in_Lacunary_Iteration` from `e4d5dcf9e` (the intake record gave the first as `2399df2bd`), the other five from `2399df2bd`; dossiers 114-CONT and 114-PUZ: Part III of `binary-substitution-discrepancy` (files `03-fluct-`, labels `bmf:`; answers Part II's question 7), Part II of `a168362-lacunary-iterates-mod4` (files `02-digitsum-`, labels `lim:dsd:`; answers question 13.2, re-scopes 13.3), and five new single-source reports in `ordinals-and-order-types/`, staged unprefixed and not merged (shared template, no shared theorem): `random-bits-arithmetic-cuts`, `noisy-parity-cubes`, `robust-neutral-choice`, `freiling-symmetry-blacklists`, `bounded-width-power-set-compression`; the eighth archive, `Periodic_Rounding_Extinction` (`e4d5dcf9e`), held for batch 110 (host `a082528-rounding-extinction`) and not placed; PDFs, checksum manifests and the additions' manuscripts and READMEs not staged; five delivered CRLF CSVs kept by `-text` lines); nothing superseded | `788a7bd5a` (binary-substitution Part III), `42d31831e` (a168362 Part II), `90198e982` (random-bits), `b7d0d5e96` (noisy-parity), `9ccf04eae` (robust-neutral-choice), `bf70d7db4` (freiling), `74a988c32` (bounded-width; source's antichain transfer refuted as printed, repaired in Remark 9.10); reciprocal `ae36f0190` | "Catalogue batches 96 to 108 and 114" | `19cdaf73c` (robust-neutral-choice: no correction), `bf04031ba` (freiling: SAP_1 strictly stronger than C_2), `c71217525` (bounded-width: no correction), `b5df007e4` (binary-substitution: eleven missed Part II renames restored), `cbc7a553b` (a168362: Part I formula (16) corrected), `4b519a0b9` (random-bits: formal status names Optimizations copies), `cf0e8e46f` (noisy-parity: no correction) |
| Report 274 | `2680aae95` (`Report274_Stressed_Kunz_Finite_Amplitude.zip`, which arrived alone in `764740f07`, outside the session bundle: the new collection report `enumerative-combinatorics/numerical-semigroup-stressed-amplitude`, beside `numerical-semigroup-leaf-types`; its main theorem unverified at intake, the counts pre-asymptotic; 7 files staged); nothing superseded | `a08662116` (read in full, no error found, not independently verified) | "Catalogue batches 110 to 137" | `444e6d6b6` (no error in a second reading; the theorem stays unverified) |
| 115 | ten archives in two arrival commits (`66f24b0d0`, five; `62e21161f`, five), a priority intake placed by Vladimir's direction under `Combinatorics/Ramsey/Research/GowersSzemeredi/`, beside the Lean development `Combinatorics/Ramsey/Lean/GowersSzemeredi`, not in the research-report collection: `aefb0b44a` (115 1/2: sources 01–05 as the new report `local-quantitative-refinements`, base 04, labels `gsr:`, five thematic Parts rather than one per manuscript; 01 and 04 independent manuscripts, not editions; 40 files staged, PDFs and members' manuscripts and READMEs not), `ad37962c4` (115 2/2: sources 06–10, prefixed files only; the quartic lower bound with coefficient 12 false, as 08 and 09 show; 46 files staged); nothing superseded | `18507e2b2` (01–05: 167 pp.), `9f83dbe0f` (06–10: 321 pp.; the coefficient-12 quartic bound refuted on record, Remark W1) | "Catalogue batches 108 to 125" | the checks of the 01–05 and 06–10 writes, recorded in `b16ce380d` (four and five wording defects corrected, no mathematical error) |
| 116 | four archives in two arrival commits (`08ab4187e`, three; `d179062cc`, one): `6f530c29c` (sources 11–14 of `local-quantitative-refinements`; 13 reuses source 03's archive name but is an independent manuscript; 14's Theorem 2.1 settles 04's question Q1, the secondary coefficient `(9/4)^(1/3)`; 39 files staged); nothing superseded | `b16ce380d` (452 pp.; 11's cutoff `N ≥ 34` shown not removable, Remark W2) | "Catalogue batches 108 to 125" | — |
| 117 | three archives in three arrival commits (`212999d4b`, `99f28708e`, `060528502`): `eed2ab863` (sources 15–17; uncredited prior work, overstated novelty and understated formal status, no wrong headline claim; one CRLF CSV kept by a root `.gitattributes` `-text` line; 21 files staged); nothing superseded | `eae64ceca` (with batch 118: 647 pp.) | "Catalogue batches 108 to 125" | — |
| 118 | three archives in two arrival commits (`82bc38a30`, two; `83f3171c1`, one): `58aa0c493` (sources 18–20; 18 a new Section 15 chapter, 19 the Lemma 16.10 interpolation, 20 quadratic counting; 21 files staged); nothing superseded | `eae64ceca` (with batch 117) | "Catalogue batches 108 to 125" | — |
| 119 | three archives of `26908b3b6`, dropped from the tree by the merge `f7efeb4f5` after a race with the drop process and restored byte-identically by `e3125e698`: `a902613c9` (sources 21–23; 21 and 23 prove the same exponent-five theorem, answering 14's Q1; two CRLF CSVs kept by `-text` lines; 38 files staged); nothing superseded | `4b7266a65` (with batch 120: 837 pp.) | "Catalogue batches 108 to 125" | — |
| 120 | four archives in four arrival commits (`e2bf630b0`, `d7c4aa399`, `7e827c6f3`, `6078f6e16`): `79d9075b9` (sources 24–27; 26, Report275, a written proof of the degree-one instance of `corollary_5_8`, then open; 27 not an edition of 25; 22 files staged); nothing superseded | `4b7266a65` (with batch 119) | "Catalogue batches 108 to 125" | — |
| 121 | six archives in four arrival commits (`624d7a42a`, `12da35673`, `6c2e2172b`, `17dd7886c`): `c5513046e` (sources 28–33; 32, Report276, a written proof of its degree-two instance; 61 files staged); nothing superseded | `bec460a33` (1,001 pp.) | "Catalogue batches 108 to 125" | — |
| 122 | six archives in three arrival commits (`70c6a1cf1`, `a33bcaedf`, `b103a65d4`): `bf2fe146d` (sources 34–39; 34's `c₄^odd ≤ 2/3`; four CRLF CSVs kept by `-text` lines; 77 files staged); nothing superseded | `0f0a7cb2b` (1,221 pp.) | "Catalogue batches 108 to 125" | — |
| 123 | seven archives in six arrival commits (`13f105f42`, `a6eea2a19`, `7382d8c44`, `0b4890a1c`, `f70d42385`, `f2baec573`): `2dfe46f44` (sources 40–46; 40, `fejer-arrangement-selection`, arrived before batch 120 and was overlooked when it was numbered; 41, Report277, a written proof of the whole of `corollary_5_8`, then open, in every degree (the Lean development has since proved it, `b548d998e`); four claims of 43 not checked at intake; 52 files staged); nothing superseded | `b51c063c2` (1,417 pp.) | "Catalogue batches 108 to 125" (placed state); "Catalogue batches 110 to 137" (written state) | — |
| 124 | seven archives in two arrival commits (`b6a8ee966`, `5d4718772`): `f8bc5e2ec` (sources 47–53; 50 a written counterexample to the catalogue Prop `lemma_16_10` as encoded, 52 to the preserved encodings `lemma_13_7_without_domain` and `lemma_13_7_without_prime_assumption`, neither to Gowers's lemmas in context; 49's `c₄^odd ≤ 0.6094183`; 58 files staged); nothing superseded | `52faf9fcd` (1,618 pp.) | "Catalogue batches 108 to 125" (placed state); "Catalogue batches 110 to 137" (written state) | — |
| 125 | six archives in two arrival commits (`aa1d86f6f`, `9458a55a9`): `7dc1ee29d` (sources 54–59; 57 a written proof of `theorem_13_12`, then open (since proved in Lean, `d48e8af00`); three CRLF CSVs kept by `-text` lines; 55 files staged); nothing superseded | `dfc1a5a68` (1,796 pp.) | "Catalogue batches 108 to 125" (placed state); "Catalogue batches 110 to 137" (written state) | — |
| 126 | five archives of `0d93c1eac`: `39d3295c4` (sources 60–64 of `local-quantitative-refinements`; 63's `lim c_d^odd = 1/3`; 66 files staged); nothing superseded | `32057611f` (with batch 127: 2,136 pp.) | "Catalogue batches 110 to 137" | — |
| 127 | five archives of `0281fcb05`: `06b30ca52` (sources 65–69; 65 and 69 prove one all-degree Boolean theorem independently; one CRLF CSV kept by a `-text` line; 57 files staged); nothing superseded | `32057611f` (with batch 126) | "Catalogue batches 110 to 137" | — |
| 128 | six archives of `579f95dfe` (Reports 282–287): `b788eda88` (sources 70–75; 70's headline, the printed Theorem 13.12, already proved in Lean and in writing by 57; 74 refutes in writing the later universal `Section16ContextualLiftAt` contract at `γ < 1`; 38 files staged); nothing superseded | `ddafb95a8` (with batch 129: 2,399 pp.) | "Catalogue batches 110 to 137" | — |
| 129 | six archives of `579f95dfe` (Reports 288–293, one chain): `487859db5` (sources 76–81, hereditary relative energy, with the sharp constants 3/4, 19/27, `ρ`, 53/81 and `λ`; 43 files staged); nothing superseded | `ddafb95a8` (with batch 128) | "Catalogue batches 110 to 137" | — |
| 130 | seven archives in two arrival commits (`579f95dfe`, Reports 294–299; `006cd822e`, one): `bbde2b873` (sources 82–88; 87 shows `Section16ContextualLiftAt` false even at `γ = 1`, the source of the formal refutation `48efbb992`; 84 and 86 open a Part V chapter on the five-term threshold; 69 files staged); nothing superseded | `803a5be32` (with batch 131: 2,736 pp.) | "Catalogue batches 110 to 137" | — |
| 131 | six archives in four arrival commits (`fe6aa5608`, three; `fab704838`, `785382058`, `0049d075d`): `39beb65f2` (sources 89–94; 89/92 and 90/93 prove the same results independently, printed as second routes at the write; two CRLF CSVs kept by `-text` lines; 70 files staged); nothing superseded | `803a5be32` (with batch 130) | "Catalogue batches 110 to 137" | — |
| 132 | two of the four archives of `7b8ed30e7`: `09f5b745a` (sources 95–96; 96's `c₄^odd ≤ 0.5868716`; 26 files staged); the other two, not Gowers material, went to NG1; nothing superseded | `88296c9fc` (batches 132–137: 3,050 pp.; it also printed the abstracts of sources 70–94, which the two previous writes had announced but not printed) | "Catalogue batches 110 to 137" | — |
| 133 | two of four archives in four arrival commits (`33da30eb2`; the third-energy paper of `98f4b3b67`): `9599d8566` (sources 97–98; 11 files staged); `uniform-lattice-bridges-research` (`fe7165a3c`), `sharp_operator_mixing_research` (`e416e9273`) and the spectral paper of `98f4b3b67` left for NG1; nothing superseded | `88296c9fc` | "Catalogue batches 110 to 137" | — |
| 134 | two archives of `a41aa448d`: `53eedc74c` (sources 99–100; 17 files staged); `Optimized_Van_der_Waerden_Bounds` (`1aa2f12ec`), not Gowers material, placed by `002a46f18` as the new report `Combinatorics/Ramsey/Research/VanDerWaerden/superexponential-lower-bounds`, outside the collection, delivered layout kept; nothing superseded | `88296c9fc` (99–100); the van der Waerden report placement only (9 October rule: no write) | "Catalogue batches 110 to 137" | — |
| 135 | `sharp_cube_stability_ProveIt` (`138139e1f`): `3a5a735dc` (source 101; 12 files staged). Five archives of the same arrivals, not Gowers material, placed as new reports outside the collection, delivered layout kept: `277e8f510` (`uniform_geometric_avoidance`, `85aaec238`, opening `Analysis/ErdosSimilarity`), `97f51e381` (`Fourier_Codimension_Research` of `1308bef8f` and `Boolean_Fourier_Correlations` of `933cf7f7b`, merged as `Combinatorics/BooleanFunctions/Research/square-root-degree-bound`), `98db5a81a` (`local_fourier_sign_codes`, `1308bef8f`, opening `Combinatorics/Sidorenko`) and `395600733` with `670a67d35` (`polar-discriminant-mixing-research`, `9d9078c78`; the first retired the archive but, after an index-lock collision, committed none of its files, which the second added). `PolyLog.zip` (`f220191c8`) went to its own dossier (PL); nothing superseded | `88296c9fc` (101); the five other reports placement only (9 October rule: no write) | "Catalogue batches 110 to 137" | — |
| 136 | two archives (`eaa83fb0f`, `af40648da`): `e38d7731f` (sources 102–103; 103 proves 101's Conjecture 12.1, which this placement misnumbered "9.1"; 17 files staged); the two other archives of `eaa83fb0f` went to NG2; nothing superseded | `88296c9fc` | "Catalogue batches 110 to 137" | — |
| 137 | three of the four archives of `d96a456d2`: `bb6ecb32b` (sources 104–106; 104 a second proof of 101's Conjecture 12.1, 105 a proof of 92's Conjecture 11.4, `m_{3,1} = 11/27`; two delivered `.log` records added with `-f`; 28 files staged); the fourth went to NG4; nothing superseded | `88296c9fc` (every placed source, 01–106, now written) | "Catalogue batches 110 to 137" | — |
| NG1 | five manuscripts of three arrivals of 7 October, not Gowers material, left by batches 132 and 133: `9a10a617f` (the partitions manuscript of `ProveIt_Research_2026-10-07.zip`, `7b8ed30e7`, as Part III of the collection's `a373271-distinct-multiplicity-values`, files `03-fluct-`; two CRLF CSVs kept by `-text` lines), `5476940ed` (its sensitivity companion as the new report `Combinatorics/BooleanFunctions/Research/sensitivity-block-sensitivity`; the archive retired), `ef4960d4c` (`Sharp_Incidence_Stability_ProveIt`, `7b8ed30e7`, as `Combinatorics/Sidorenko/Research/sharp-incidence-stability`), `3cf0a2758` (`uniform-lattice-bridges-research`, `fe7165a3c`, as Part II of the collection's `a328716-lazy-closed-walks`, files `02-bridges-`) and `d294770a7` (`sharp_operator_mixing_research`, `e416e9273`, and the spectral paper of `ProveIt_Spectral_Transfer_and_Third_Energy_2026-10-07.zip`, `98f4b3b67`, merged as `Combinatorics/Ramsey/Research/SquareDifferences/spectral-list-mixing`); delivered layouts kept for the new reports; nothing superseded | `b0ad11d15` (a373271 Part III), `3257a20bd` (a328716 Part II, Sections 13–21); the three others not written (the sensitivity host has a reconciliation README, `eb8dee994`) | "Catalogue batches 110 to 137" (placed state); this commit (written state) | `4163d271d` (a373271 Part III: every constant, table and label confirmed; one re-scoping restricted to `0 < α ≤ 1`), `640d9375d` (a328716 Part II: the `D = 16` counterexample confirmed by two further routes; one comparison relabelled, two precisions of scope) |
| NG2 | two archives of `eaa83fb0f`, not Gowers material (assessed with batch 136): `7003b6e89` (`sparse_grid_moments_quadratic_closure` as `Combinatorics/Ramsey/Research/QuasipolynomialProgressions/sparse-grid-moments`) and `bfbfe9151` (`Ordered_Matrix_Removal_Research` as `Combinatorics/OrderedMatrices/Research/ordered-matrix-removal`, with a nested Apache-2.0 licence); delivered layouts kept; nothing superseded | — (placement only, 9 October rule) | "Catalogue batches 110 to 137" | — |
| NG3 | `ProveIt_Binary_Two_Way_Corank.zip` (`964621dd2`): `bdcae034b` (the new collection report `automata-and-formal-languages/binary-two-way-corank`, delivered layout kept, with a nested Apache-2.0 licence; two CRLF files kept by `-text` lines in `SetTheory/Cardinals/.gitattributes`; 29 files staged); nothing superseded | `d89be4d77` (37 pp., prefix `btc:`; Theorem 5.4 kept conditional on its external premise) | "Catalogue batches 110 to 137" (placed state); this commit (written state) | `417ff568f` (the headline bound confirmed, Theorem 3.1 rebuilt from the text alone, two precisions on the trust boundary) |
| NG4 | `parity_moment_cancellation.zip` (`d96a456d2`, assessed with batch 137): `d2ccfed6d` (manuscript 03 of `Combinatorics/BooleanFunctions/Research/square-root-degree-bound`, which answers its question on higher-codimension moment minima; files `03-parity-moments-`; 9 files staged); nothing superseded | — (placement only, 9 October rule; reconciliation README of the host, `eb8dee994`) | "Catalogue batches 110 to 137" | — |
| PL | `PolyLog.zip` (`f220191c8`), Vladimir's own PolyLog programme from the private Smithereens repository, placed with priority at his direction: `13f0d8f20` (the new topic project `Analysis/Polylogarithms`: eight articles and thirty-one reports with their PDFs, delivered names kept, one local path redacted with a dated note) | `a87af186c` (the project README with the intake claim review; delivered files not edited) | `a87af186c` (index entries and the destinations row) | — |
| UK | the unknot-recognition deliveries of 7 October 2026, placed under `Topology/UnknotRecognition/reports/` as delivered, by Vladimir's standing rule (destinations table): `c292eda28` (07, `eb79136d9`), `47b65da21` (08–11; `7a46ad3c1`, `ca61a1a5f`), `3f7662bba` (12, whose arrival the drop process folded into `47b65da21`), `739ff4f4e` (13–16; `c1224a2c7`, `0090314cf`, `b9e06c751`), `8917bae6d` (17–19; `d54009df0`, `a0c3e9b67`, `df4e6385e`), `1da9ecfd8` (20–21; `ed3bef73c`, `910b93949`), `1b1e1311c` (22, `0e45cc0db`), `1ce70340e` (23–24, `be8c70cd9`) and `612d4935c` (25, from `09c9cfe4b`; see the note below); `8c7f2b71b` and `325fe8b74` dropped the `-text` exceptions and normalized 19 delivered files to LF, and `460f30c43` recorded that rule here | — (none, by the standing rule) | each placement's row in `reports/README.md`; "Catalogue batches 110 to 137" | — (no soundness review, by the standing rule) |
| 138 | the arrivals of 8 October 2026 (`b28d0850b`, `36f1dd8ef`, `fcfe6ef6a`, `2c7f4fd68`; their unknot archives went to the unknot intake): twenty-nine manuscripts in twenty-six archives, placed in six groups from one triage: `0e05d71a1` (Gowers: source 107 of `local-quantitative-refinements`), `cd984a34c` (Erdős similarity: sources 02–04 of `Analysis/ErdosSimilarity/Research/uniform-geometric-avoidance`, one common C-finite avoiding set proved three times), `803f4d937` (OEIS: Part II of `a308338-nested-cycle-assemblies`, Part VI of `a094149-sparse-graph-moments`, Part IV of `a290354-iterated-euler-diagonals`, the collection's new `ford-renewal-logarithmic-remainder` and `a275672-cubic-distances`, placed only and without their PDFs, and one Fabius-tree arrival filed whole, `representations/Uniform_High_Moment_Asymptotics_Weighted_Uniform_Series`), `06039f479` (PolyLog: six continuations as five merged reports under `Analysis/Polylogarithms/docs/reports/`), `18abb81b2` (combinatorics: manuscript 04 of `square-root-degree-bound`, Part II of `sensitivity-block-sensitivity`, and two new reports placed only, `Combinatorics/Sidorenko/Research/four-cycle-quasirandomness` and the collection's `convex-geometry/optimal-simplex-products`, which opens `convex-geometry/`) and `0599fe867` (probability: nine single-manuscript reports placed only, opening `probability/`); files staged as delivered under the rules of 9 October; no delivered claim found wrong; nothing superseded | `643803af9` (Gowers 107; 3,082 pp.), `aeecf5e9e` (a308338 Part II), `cebf43994` (a094149 Part VI), `03c28e4c8` (a290354 Part IV); notes `7354dd9e1` (a005121, a139383); reconciliation notes instead of a write: `3d0303836` (uniform-geometric-avoidance), `eb8dee994` (the two BooleanFunctions hosts), `58b50f89b` and `a477aff21` (the PolyLog README's status of claims; the five `OVERVIEW.md`) | this commit | `96002ee3f` (a308338: `E_* = W(1/e)/e` proved, answering Question 23.3; one rounding corrected), `443af1da6` (a094149: nothing wrong), `d00eba30c` (a290354: nothing wrong) |
| 139 | four archives in three arrival commits of 9 October (`3e07f86cf`, `cbe9e9b59`, `eaad5886e`): `d4dead2c6` (PolyLog manuscripts 14–17, continuations of the unified manuscript, merged as `Analysis/Polylogarithms/docs/reports/gaussian-parity-reductions/`, base 14; they prove its Gaussian weight-five and weight-six candidates and show `articles/gaussian-multiple-polylog-depth.tex`, lines 284–292, false as printed); nothing superseded | — (reconciliation `845e133ec`: the project README's status of claims and the `OVERVIEW.md` notes) | this commit | — |

Batches 99 to 113 are the fifteen clusters into which the intake triaged
the session bundle of Research Reports 1–243 (177 archives in one arrival
commit, `60f54ea06`). Batch 99 went to the Fabius drafts tree only;
batches 100 to 113 are placed and written. Batch 114 is the seven
non-bundle archives of the two
arrival commits `e4d5dcf9e` and `2399df2bd`; the eighth,
`Periodic_Rounding_Extinction.zip` (`e4d5dcf9e`), was held for batch 110,
which placed and wrote it as Part III of its host
`a082528-rounding-extinction`. Three placement
records are corrected in the rows above: batch 106's message said that
Report 153 carries "prepared for private review" (the phrase occurs in
none of its delivered files, only in sentences saying such material is
excluded) and that it answers Johnston's `o(n!)` question (Bassino et
al., 2024, answered it first; Report 153 adds the constant `1/4` and every
order); batch 107's message gave Wiseman's A238873 conjecture as addressed
by no source (the write proved it, crediting Garrot's prior argument in
A387112); and the batch-114 intake record gave `binary_morphic_fluctuations`'
arrival as `2399df2bd` (it arrived in `e4d5dcf9e`). A fourth is corrected
in the batch-108 row: the placement message paraphrased Riedel's note as
conjecturing `E[X] ~ N n^M` with a fitted `M ≈ 0.4705`, and the first
catalogue repeated it; the note's boxed conjecture is `E[X] ~ N√n`, which
`a308338-nested-cycle-assemblies` proves with `N = e^(−γ/2)`, and its
alternative `n^M`, `M` "close to but not equal to 1/2" with printed
`M ≥ 0.4704567259`, is refuted there.

Batches 115 to 137 are one hundred and six Gowers–Szemerédi manuscripts
that arrived on 6 and 7 October 2026 (the fifty-nine of batches 115 to 125
in thirty-one commits on 6 October), numbered 01–106 in arrival order
(then ASCII order of archive name) as the sources of one report,
`Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements`.
By Vladimir's direction they are a priority intake, placed beside the Lean
development of Gowers's proof (`Combinatorics/Ramsey/Lean/GowersSzemeredi`)
and the edited source paper, not in the research-report collection, which
overrides the rule of section 2 for reports that continue a formal project;
every later Gowers-related report takes precedence over other intake work.
Each batch added its sources to the report as prefixed files, the base
(source 04) unchanged, and each write appends dated additions without
renumbering anything printed; the writes cover sources 01–106, the last
(`88296c9fc`, 3,050 pages) also printing the abstracts of sources 70–94
that the two writes before it had announced but left out. The report's README is
its own index, and its "Relation to the formal project" section records
the formal status: none of its statements gains any from the placement.
`FORMALIZATION_STATUS.txt` beside the Lean development names sources 41,
57 and 49–53 as written results for obligations that were open at the
time (`128f514af`, `c6b9e8da9`). Source 40 arrived before batch 120 and
was numbered only in batch 123; batch 119's archives, dropped from the tree by a merge during a
race with the drop process (`f7efeb4f5`), were restored byte-identically
(`e3125e698`) before placement. Batch 136's placement message calls the
conjecture of source 101 that source 103 proves "Conjecture 9.1"; it is
101's Conjecture 12.1, as batch 137's placement and the write record.
Batch 138 added a hundred and seventh manuscript, source 107
(`0e05d71a1`, written `643803af9`), under the same direction.

The arrivals of 7 October that the Gowers batches assessed but that do
not concern Gowers's argument were placed in their own rows: NG1 to NG4
from the non-Gowers queue, and the non-Gowers placements recorded in the
rows of batches 134 and 135. Three of them went to the research-report
collection (Part III of `a373271-distinct-multiplicity-values`, Part II of
`a328716-lazy-closed-walks`, the new `binary-two-way-corank`), and all three
have since been written and independently checked (rows NG1 and NG3). The others
opened new research directories outside it, beside the nearest topic
project: `Analysis/ErdosSimilarity/Research/`,
`Combinatorics/BooleanFunctions/Research/`,
`Combinatorics/Sidorenko/Research/`, `Combinatorics/OrderedMatrices/Research/`
and, beside `GowersSzemeredi/`, `Combinatorics/Ramsey/Research/` with
`VanDerWaerden/`, `SquareDifferences/` and `QuasipolynomialProgressions/`.
The destinations table of section 2 has no row for such directories, and
their placement messages cite no direction of Vladimir's for them; they
are recorded here as placed, with their delivered layout, no article write
yet, and pointers in `Analysis/README.md` and `Combinatorics/README.md`.
Batch 138 added sources to `uniform-geometric-avoidance`,
`square-root-degree-bound` and `sensitivity-block-sensitivity`, which
gained READMEs of reconciliation notes (`3d0303836`, `eb8dee994`), and
opened `Combinatorics/Sidorenko/Research/four-cycle-quasirandomness`. Most of these manuscripts refine releases of
openai/math with attribution, and several stage that release's Apache-2.0
licence as a nested licence.

The unknot-recognition reports 07–25 follow the destinations-table rule:
extracted as delivered, wrapper removed, no test runs, no patch
application, no soundness review, and, from 7 October, LF text without
`-text` exceptions and no checksum files (Vladimir; `69344bb09` also
removed fourteen SHA-256 records from earlier imported reports and kept the
one that `a324312-planar-eulerian-orientations` reads). On 9 October
Vladimir withdrew the line-ending and checksum rules for all intake
(`181579587`) and gave the knot-related reports to another agent, so this
note, like the UK row, stops at report 25. Report 25 departs
from it: `612d4935c`, from the unknot integration work, verified the
archive's 45 SHA-256 entries and kept its `SHA256SUMS.txt`, ran its 47-test
suite, and left `unknot_cyclic_garside_20261007.zip` (`09c9cfe4b`) in this
directory. When the catalogue of 7 October was written, that archive and
three later ones awaited placement (all four have since left this
directory): `ProveIt_Unknot_Determinant_Continuations_2026-10-07.zip`
(`a58110851`), `ProveIt_Report25_Causal_R3_2026-10-07.zip` (`3990b5c80`)
and `unknot_classical_closure_research_20261007.zip` (`8f5820a52`).

Batch 138 is the first batch under Vladimir's rules of 9 October 2026
(sections 1 and 2). Thirteen of its reports are placed only, with no
write and no independent check: the nine in `probability/`,
`optimal-simplex-products`, `four-cycle-quasirandomness`,
`ford-renewal-logarithmic-remainder` and `a275672-cubic-distances`. The
overlapping deliveries got either a full write (Gowers source 107 and the
three OEIS Parts) or a reconciliation note at the intake's judgment (the
Erdős-similarity, BooleanFunctions and PolyLog hosts). The placement-only
reports are not staged alike: the probability placement, made under the
rule, keeps each delivered PDF and README, while the four others were
staged as if a write would follow, without their PDFs,
`four-cycle-quasirandomness` also without its delivery README, and
`optimal-simplex-products` with a `main.tex` whose input
`../common/preamble.tex` does not resolve where it is placed (the copy is
at `common/preamble.tex`). Batch 139 is four continuations of the unified
PolyLog manuscript, placed as one merged report; two later PolyLog
archives of `412dbd004` await placement.

Batches 81 and 82 were placed by one intake session, which ended with their
writes unfinished: it committed the batch-81 writes (1/4)–(3/4) and the
first writes of `five-particle-binary-automata` and
`fixed-universal-polynomials`. The next session took over the remaining
writes from the first session's dossiers and drafts, re-verifying them, and
processed batches 83 to 86 itself.
