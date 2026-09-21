# Foundations for Surreal and Surcomplex Mathematics

**Set Theory, Type Theory, Size-Safe Analysis, and Lean**  
September 21, 2026

## Contents

- `surreal_foundations.pdf`: the 32-page article, including a table of contents,
  17 main sections, two appendices, and 28 bibliography entries.
- `surreal_foundations.tex`: self-contained LaTeX source. References are inline;
  no separate BibTeX database or external figures are required.
- `lean/LogicalGuards.lean`: illustrative universe and algebra examples.
- `lean/SourceAudit.lean`: illustrative probes for the pinned source environment.
- `source_audit.json`: repository revisions, inspected declarations, input hashes,
  live-documentation sources, and explicitly unverified dependencies.
- `build_report.json`: PDF production status, separate from Lean verification.
- `SHA256SUMS`: checksums for the files in this package other than itself.

## Scope and evidence

The article compares ZF/ZFC definable classes, GB/GBC/NBG, Kelley--Morse,
set-sized birthday fragments and Hahn fields, Grothendieck universes and TG,
classical dependent types, IZF/CZF, HoTT, and internal set-theoretic models in Lean.
It applies those distinctions to the two supplied surcomplex manuscripts.

Particular attention is given to admissible cut sizes, class quotients,
well-founded recursion, small Hahn supports, the difference between a full-class
fine topology and a workspace topology, and the additional structure needed to
specify a global surcomplex exponential. The article supplies proofs of several
foundational lemmas and counterexamples, a theorem-dependency audit, and a
layered Lean implementation plan.

Consistency claims are relative to the chosen foundation. This package is not
an absolute consistency proof and does not certify all analytic results in the
source manuscripts.

## Verification status

The PDF was successfully compiled and its rendered pages were inspected.
The Lean files were **not compiled or kernel-checked**: no Lean or Lake executable
was installed in the preparation environment. They are explicitly labeled as
illustrative source. A successful future execution of the small examples would
not constitute a verification of the full surreal theory or of the manuscripts.

The implementation audit is based on primary-source inspection of:

- Repository: https://github.com/vihdzp/combinatorial-games
- Revision: `02b4a908ea2ecfefffecb438f691951a814a5264`
- Commit date: September 19, 2026
- Toolchain at that revision: `leanprover/lean4:v4.35.0-rc2`
- Mathlib dependency: `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`

The general mathlib documentation was inspected separately as live documentation.
It is not asserted to be generated from that pinned dependency commit. The audit
identifies existing field and small-support infrastructure but does not assert
that unverified normal-form or analytic dependencies are absent from every project.

## Rebuilding the article

With a TeX distribution containing the packages named in the preamble, run from
this directory:

```text
pdflatex -interaction=nonstopmode -halt-on-error surreal_foundations.tex
pdflatex -interaction=nonstopmode -halt-on-error surreal_foundations.tex
pdflatex -interaction=nonstopmode -halt-on-error surreal_foundations.tex
```

Multiple passes resolve the table of contents, citations, theorem references,
and PDF bookmarks. LaTeX intermediate files are not included in the archive.
Font files are not included.

## Running the illustrative Lean probes

The following commands are a reproduction recipe, **not commands executed while
preparing this package**. They require Git and an installed Lean/Lake toolchain
manager. Build the upstream project with its original pinned dependency manifest;
do not run `lake update` and then describe that as a check of this exact revision.

### POSIX shell

```sh
ARTICLE_DIR=/absolute/path/to/surreal_foundations
git clone https://github.com/vihdzp/combinatorial-games.git
cd combinatorial-games
git checkout --detach 02b4a908ea2ecfefffecb438f691951a814a5264
lake build
lake env lean "$ARTICLE_DIR/lean/LogicalGuards.lean"
lake env lean "$ARTICLE_DIR/lean/SourceAudit.lean"
```

### PowerShell

```powershell
$ArticleDir = (Resolve-Path 'C:\path\to\surreal_foundations').Path
git clone https://github.com/vihdzp/combinatorial-games.git
Set-Location combinatorial-games
git checkout --detach 02b4a908ea2ecfefffecb438f691951a814a5264
lake build
lake env lean (Join-Path $ArticleDir 'lean/LogicalGuards.lean')
lake env lean (Join-Path $ArticleDir 'lean/SourceAudit.lean')
```

Record command exit codes and the actual output of `#print axioms` when executing
these probes. Compilation failures should be reported rather than replaced by
unproved declarations. In particular, a field instance is not a proof of real
closedness, and a small-support Hahn datatype is not by itself a proof of its
isomorphism with the game-based surreal field.

## Source manuscripts

The original manuscripts are cited in the article and identified by SHA-256 in
`source_audit.json`. They are not duplicated in this archive. Other archives
mentioned in their references were not examined for this task. Public references
and source links appear in the article's bibliography.
