# Agents working in `Analysis/FabiusFunction`

Several agents develop this directory concurrently in separate worktrees.
Please read [`docs/COLLABORATION.md`](docs/COLLABORATION.md) before making
structural changes; it is a proposal, open for revision, and it records which
collisions have already happened and how they were resolved.

The rules that have actually cost time so far:

1. **Fetch and inspect `origin/main` before you start, and again before editing
   any module you did not create.** Merge it when the worktree is clean.  For a
   dirty shared worktree, freeze every writer and follow the path-overlap and
   Git-owner protocol in `docs/COLLABORATION.md`; never merge or stash behind
   another writer's back.  The same refactor has already been performed
   independently three times by three branches.

2. **A lemma belongs in the upstream-most module that can state it** — facts
   about `rvachevUp` needing only its definition and `IsFabius` go in
   `Basic.lean`, not `Differential.lean`. But relocating into `Basic.lean`,
   `Arithmetic.lean`, or `Differential.lean` invalidates all 172 modules and
   is the edit class most likely to collide, so acquire a live path lease as
   described in `docs/COLLABORATION.md` first.

3. **Say in the commit message what you actually compiled.** Committing
   uncompiled work is fine and often necessary — a full rebuild costs the
   better part of a day on this machine — but write an explicit
   `Verified: …` / `Not yet compiled: …` line.

4. **In a shared worktree, source-only subagents edit only leased files.** One
   Git owner stages explicit paths and changes HEAD; one build owner runs Lean
   or Lake with writers frozen.  Subagents do not stage, merge, push, clean, or
   mutate build outputs.

5. **All mathematical writing is LaTeX.** See the documentation policy below.
   Markdown is for repository bookkeeping — READMEs, coverage maps, audits,
   coordination — never for mathematics.

Invariants that must not regress: no `sorry`, `admit`, `axiom`, or `opaque`;
the axiom set stays exactly `propext`, `Classical.choice`, `Quot.sound`;
`set_option autoImplicit false` in every file; a doc comment on every
non-`private` declaration; new modules registered in
`Lean/FabiusFunction.lean`.

## Documentation policy

**Every mathematical document in this directory is a LaTeX document, and its
compiled PDF is committed with it.**

1. **Format.** Mathematics is written in `*.tex`, never in Markdown. A
   write-up of a theorem, a derivation, a table of coefficients, a numerical
   study, or an expository account of any part of the development belongs in a
   `.tex` file. Markdown remains correct for `README.md`, `AGENTS.md`,
   `docs/PAPER_COVERAGE.md`, `docs/COLLABORATION.md`, `docs/registry/*.md` and
   similar repository bookkeeping, which contain no displayed mathematics.

2. **Style.** New documents reuse the preamble of
   [`docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`](docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex)
   verbatim: the same `geometry`, font and `microtype` setup, the same
   `linkblue`/`shadegray`/`rulegray` colours and `hyperref` configuration, the
   same `fancyhdr` and `titlesec` section formatting, the same theorem
   environments (`theorem`/`proposition`/`lemma`/`corollary`/`conjecture`,
   `definition`/`algorithm`/`example`, `remark`/`warning`), the same macro set
   (`\R`, `\C`, `\Q`, `\N`, `\Z`, `\Up`, `\e`, `\ii`, `\dd`, `\E`, `\Prob`,
   `\bigO`, `\qbinom`, `\repo`, …), the same `proofidea` and `boxedremark`
   environments, and the same `pseudo` listing style. Only the `\title`,
   `\author`, `\date`, `pdftitle`/`pdfsubject`/`pdfkeywords` and the running
   head change. Do not invent a second visual identity for this directory.

3. **Layout.** One directory per document, named after it, holding the `.tex`
   and the `.pdf` of the same name — as in
   `docs/Fabius_Function_and_Rvachev_Up/` and
   `docs/Small_Argument_Asymptotics/`.

4. **The PDF is committed.** Build it before committing and commit it in the
   same commit as the source:

   ```sh
   cd Analysis/FabiusFunction/docs/<Document_Name>
   pdflatex -interaction=nonstopmode -halt-on-error <Document_Name>.tex
   pdflatex -interaction=nonstopmode -halt-on-error <Document_Name>.tex
   pdflatex -interaction=nonstopmode -halt-on-error <Document_Name>.tex
   rm -f *.aux *.log *.out *.toc
   ```

   Three passes: the first writes the `.aux` and `.toc`, the second resolves
   `\ref`/`\cref`, the third settles the table of contents and page numbers. Do
   not commit `.aux`, `.log`, `.out` or `.toc`. A `.tex` change without a
   rebuilt `.pdf` is an incomplete commit.

5. **Verify the rendered PDF, not the source.** Never write LaTeX through a
   shell heredoc or a Python patch script that round-trips through
   `unicode_escape`: both silently destroy backslashes and non-ASCII
   characters, and LaTeX does *not* error on the result — it renders
   something plausible and wrong. Use the editor tools, then check the page
   count and the log.

6. **Cross-reference the formalization.** A mathematical document should carry
   a table mapping its objects to the Lean names and modules that formalize
   them, and should state explicitly what is *not* claimed.

## Building Lean

Build one module per `lake` invocation, in topological order. `LAKE_JOBS=1` is
not enough: a single `lake build A B` still starts two `lean` processes, and on
this 13 GB machine both then die with a misleading
`failed to read file '….olean'`, which is an out-of-memory symptom rather than
a real error.

The module target needs a `+` prefix. `lake build FabiusFunction.Basic` fails
with `unknown target`; `lake build +FabiusFunction.Basic` is the working form.

A worktree without its own `.lake` would rebuild Mathlib from scratch. Give it
one whose `packages` is a directory junction to the shared
`C:\ProveIt\.lake\packages`, so the built Mathlib is reused while the Fabius
build outputs stay isolated per worktree:

```sh
mkdir -p .lake
cmd //c mklink //J ".lake\\packages" "C:\\ProveIt\\.lake\\packages"
```

### Validating another branch without merging it

A build owner can check somebody else's commit without either party merging,
and without disturbing an in-progress closure, by using a throwaway sparse
worktree:

```sh
git worktree add -f --no-checkout --detach <dir> <sha>
cd <dir>
git sparse-checkout init --cone
git sparse-checkout set Analysis/FabiusFunction
git checkout
mkdir -p .lake
cmd //c mklink //J ".lake\\packages" "C:\\ProveIt\\.lake\\packages"
LAKE_JOBS=1 lake build +FabiusFunction.<Module>
```

The junction is the point: a fresh worktree without it rebuilds Mathlib and is
worse than useless. Cone mode matters too — a full checkout of this repository
can take minutes on a busy disk, while the `Analysis/FabiusFunction` cone plus
the root files is seconds.

This makes "who owns the build" a scheduling question rather than a structural
one: the owner of the slot can spend it on any branch, and a peer's commit can
be validated at the price of one checkout. It does not change the arithmetic
that only one `lean` process may run at a time.

Prefer the cheapest module that exercises the change. A module's cost is the
size of its Fabius import closure, not its own length; a leaf with no Fabius
imports is a single invocation off warm Mathlib.

Two further traps that have cost real time here:

- **`ContDiff ℝ ⊤` means *analytic*, not `C^∞`.** In this Mathlib `ω` is
  `(⊤ : WithTop ℕ∞)` and `∞` is the strictly smaller `((⊤ : ℕ∞) : WithTop ℕ∞)`.
  Write `ContDiff ℝ ∞`, and remember that `∞` is `scoped[ContDiff]` notation:
  a file that uses it needs `open scoped ContDiff`.
- **Windows line endings.** A build-order list generated by Python in text mode
  carries `\r`, and every entry then fails with `unknown target` — or, with the
  `+` prefix, `unknown module [anonymous]`. Pipe the list through `tr -d '\r'`.
