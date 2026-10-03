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
- **Checksum manifests.** Verify each checksum manifest against the extracted
  files, then plan to drop it. A checksum manifest is a file whose purpose is
  to list the package's hashes: `SHA256SUMS`, `SHA256SUMS.txt`,
  `CHECKSUMS.sha256`, `MANIFEST.sha256`, `sha256.json` and the like.
  Repository policy abolishes them (the root `.gitignore` ignores
  `**/SHA256SUMS` and `**/SHA256SUMS.*`), and no collection ships one. A
  record that carries hashes alongside other content, such as a package,
  build or provenance manifest, is data. Verify its hashes too and stage it
  under `data/`. The report's README says which of the files it lists are not
  shipped. For example, `e9a9650` dropped four `SHA256SUMS.txt` files but
  staged a `package_manifest.json` as
  `data/07-scale-moderate-interpolation-package_manifest.json`.
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
| Research-report collection | `SetTheory/Cardinals/docs/reports/<category>/[<subcategory>/]<report>/` | every other self-contained external report: ordinals and wqos, enumerative combinatorics, Hankel determinants, congruences, asymptotics, automata, graphs, the Jacobian conjecture, radicals and Galois theory, … |
| Research programme | `Computability/TuringDegrees/Research/CoarseDegrees/research-reports/<NN>/`, `SetTheory/Cardinals/docs/cardinals/research-reports/` | numbered reports that continue a programme's own research plan and synthesis (plan targets, synthesis items) |
| Fabius frontier drafts | `Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/<group>/<Document_Name>/` | Fabius, Rvachev up-function and Thue–Morse work continuing that tree's volumes; filed by the tree's own quick-intake procedure (its `drafts/incoming/README.md`): delivered package kept whole with its PDF, `MANIFEST.md` row and group-README mention, no SHAs in the records, claim review deferred (batch 38) |
| Transseries | `Analysis/Transseries/docs/series-and-transseries/<Document_Name>/` | transseries work of every kind (reversion, inversion, resurgence, regularity, transseries of special functions or sequences); **never under FabiusFunction** (Vladimir, 2026-09-29, after the split `277c782b8`). Filed like the Fabius drafts: the package kept whole with its PDF beside the volume it continues, a mention in `docs/series-and-transseries/README.md` naming that volume and the passage continued, no SHAs; merging into the volumes is deferred (batch 45) |

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
  the project's own directory. The project README gains a pointer to it in
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
| Base of a new merge | staged as delivered, unprefixed | staged with a prefix |
| Other member of a merge | not staged | staged with a prefix |
| Addition to an existing report | not staged | staged with a prefix |

This table records the practice of `a826a41` and `e9a9650`, the placements
made after `sources/` was retired. Use `b071389`, `d6eee04` and `d3d9688` as
examples of placement decisions, not of staging.

- **Never staged:** PDFs, checksum manifests, and the manuscripts and READMEs
  of merge members and additions. Their provenance is recorded in the report
  instead.
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
  against the fresh extraction. `.gitattributes` normalizes text to LF
  (`* text=auto eol=lf`), so check that staged text files contain no CR bytes
  and read the "CRLF will be replaced by LF" warnings of `git add`; otherwise
  the committed blob will differ from the delivered bytes.
- **Retire the archives in this same commit**, as described in section 7.

## 4. Write the reports

Turn the placed material into finished reports. Commit them in one or more
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
