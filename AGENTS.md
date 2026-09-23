# Notes for agents working in this repository

Practical information about the tools, configuration and workflow used to
formalize the theorems in `docs/`. Mathematical scope and status live in
[docs/FORMALIZATION.md](docs/FORMALIZATION.md); this file only records how to
work efficiently and safely.

## Repository layout

- `docs/` — the research reports (LaTeX sources, PDFs, verification code).
  Reports are grouped as `foundations-and-computation/`, `physics/`,
  `surcomplex/`, `surquaternions/` and `surreal/`. Newly placed reports may
  not yet appear in the ledger; check `docs/README.md` and `git log`.
- `docs/FORMALIZATION.md` — the coverage and dependency ledger. Its
  "Implementation mappings" table maps each source label (for example
  `trigonometry:prop:lift`, `found:thm:workspace`) to Lean declarations and
  states the exact proved scope. Statuses are strict: **Pending**,
  **Prerequisites proved**, **Proved**, **Needs correction**.
- `docs/NORMAL_FORM_BRIDGE.md`, `docs/NOTATION.md` — the normal-form bridge
  and shared notation.
- `Surreal/` — the Lean library, split into `Algebra/` (generic ordered-field,
  polynomial and power-series algebra), `HahnSeries/` (generic Hahn-series
  results, namespace `Surreal.HahnSeries`), `Foundations/` (the sign-sequence
  carrier, small normal forms and the actual surreal field) and `Surcomplex/`
  (the actual surcomplex numbers `No[i]` and their analysis).
- `Surreal.lean` — the root import list. **Every new module must be imported
  here**, otherwise it is neither built by default nor covered by the audit.
- `SurrealAudit.lean` — default build target that rejects any transitive axiom
  other than `propext`, `Quot.sound` and `Classical.choice` for every
  declaration in the `Surreal` and `SurrealHahnSeries` namespaces.
- `vendor/combinatorial-games/` — vendored path dependency (numeric-game
  quotient and its ordered field); see its README before touching it.

## Lean toolchain and build

- Toolchain: `leanprover/lean4:v4.32.0` (`lean-toolchain`), Mathlib tag
  `v4.32.0` at commit `81a5d257c8e410db227a6665ed08f64fea08e997`
  (`lake-manifest.json`). `elan`, `lake` and `lean` are on `PATH` under
  `C:\Users\vresh\.elan\bin`.
- `lakefile.toml` sets `warningAsError = true`: unused variables, unused
  `simp` arguments, deprecated names, long lines flagged by linters and any
  `sorry` all fail the build.
- **Do not run many `lean.exe` processes in parallel.** The machine has about
  14 GB of RAM, and by default Lake starts one `lean.exe` per core (12). Each
  one maps Mathlib, so an unthrottled build exhausts memory and fails with
  spurious `failed to read file '...olean.private'` errors. Always cap the
  job count through Lake's thread pool:

  ```bash
  LEAN_NUM_THREADS=2 lake build
  ```

  (PowerShell: `$env:LEAN_NUM_THREADS=2; lake build`). This gives exactly two
  concurrent `lean.exe` processes. Do not start a second build or several
  `lake env lean` checks while a build is running, and remember that editor
  language servers for other repositories may already be holding memory.
- Full build (library plus axiom audit): `LEAN_NUM_THREADS=2 lake build`. A
  clean build of the `Surreal` library itself (roughly 250 modules) takes a
  while; Mathlib is never rebuilt when the cache below is used.
- Check a single file quickly: `lake env lean Surreal/Path/File.lean`
  (its imports must already be built), or build one module with
  `lake build Surreal.Path.File`.
- Lake prints nothing until the end when its output is redirected to a file,
  so a background build log may stay empty for a long time. Inspect running
  `lean.exe` processes (for example with PowerShell
  `Get-CimInstance Win32_Process -Filter "Name='lean.exe'"`) to see progress.

## Reusing a Lean package cache (no Mathlib download or rebuild)

The Git worktrees under `.claude/worktrees/` start without `.lake/`. Instead
of `lake exe cache get`, junction the packages directory to an existing
checkout that pins **identical** revisions of every package:

```powershell
New-Item -ItemType Directory -Force .lake | Out-Null
New-Item -ItemType Junction -Path .lake\packages -Target C:\ProveIt\.lake\packages
```

`C:\ProveIt` pins the same Lean `v4.32.0`, Mathlib `81a5d257…`, and the same
`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`,
`Qq`, `batteries` and `Cli` commits as this repository (verified by comparing
the `rev` fields of both `lake-manifest.json` files). Re-verify before reusing
after either repository bumps Mathlib. `C:\Forge\lean` uses Lean `v4.34.0`
and is **not** compatible. Only `.lake/packages` is shared; this repository's
own `.lake/build` and `vendor/combinatorial-games/.lake` are built locally.
`.lake/` is ignored by Git.

## Finding files: `es.exe` (Everything search)

`C:\tools\es.exe` queries the Everything index of all local drives, far faster
than recursive `find`. Examples:

```bash
es.exe -n 20 -regex 'Mathlib\.olean$'          # locate built Mathlib caches
es.exe -n 40 -regex '\\\.lake$'                 # locate Lake directories
```

Use it to locate other Lean checkouts or caches; confirm versions from their
`lean-toolchain` and `lake-manifest.json` before reuse.

## Searching Mathlib for lemma names

Recursive `grep -r` over Mathlib is very slow on this machine (often over two
minutes). The Mathlib package is a Git checkout, so use `git grep`, which
returns in seconds:

```bash
cd .lake/packages/mathlib && git grep -n "theorem det_vandermonde" -- 'Mathlib/*.lean'
```

Deprecated aliases are common at this Mathlib version (for example
`Finset.addAntidiagonal` is now `Finset.antidiagonal`, `push_neg` is now
`push Not`); with `warningAsError` a deprecation warning fails the build, so
check the alias line that `git grep` shows.

## Conventions for new Lean modules

- Follow the style of neighbouring modules: a module docstring `/-! # Title`
  naming the source labels it serves, `namespace Surreal` (or
  `Surreal.HahnSeries`), docstrings on the main theorems, and names that
  expose the manuscript correspondence.
- Prefer existing Mathlib constructions (`HahnSeries`, `PowerSeries`,
  `QuadraticAlgebra`, `IsRealClosed`, `IsAlgClosed`, `Matrix`, …) over
  rebuilding them.
- Never use `sorry`, `axiom`, `admit`, or impossible typeclass assumptions to
  close a gap. If a source statement is false or underspecified, record it as
  **Needs correction** in the ledger with the counterexample or the missing
  hypothesis, then formalize the corrected statement.
- Keep generic results (arbitrary ordered fields or Hahn fields) separate from
  their instantiation at actual surreals; a theorem about a fixed Hahn field
  does not by itself say anything about the class of all surreals.
- After adding a module: import it in `Surreal.lean`, run `lake build`, and
  add or update the corresponding row in `docs/FORMALIZATION.md` with the
  precise scope proved and what remains pending. Many commits also refresh
  the summary paragraphs of `README.md`.

## Git workflow

- Work on the session branch (`claude/<name>`), commit frequently with
  detailed messages in the style of `git log` (what was proved, at what
  generality, what remains pending, and the validation performed, such as the
  job count of `lake build` and the audit's declaration count).
- Sync: `git fetch origin && git merge origin/main`, rebuild, then publish the
  branch with a fast-forward push: `git push origin HEAD:main` (it must be a
  fast-forward of `origin/main`; never force-push `main`).
- `origin/main` often advances while a build runs (other sessions merge
  documentation and Lean work several times an hour), so the fast-forward
  push can be rejected. Repeat fetch, merge, rebuild, push until the push
  succeeds; skip the rebuild when the newly merged commits touch only
  `docs/` (check `git diff --name-only <old-HEAD> HEAD` for `Surreal/`,
  `Surreal.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`).
- The Git stash is shared across worktrees; do not use bare `git stash`.
- `.gitattributes` normalizes text files to LF; `.editorconfig` asks for
  UTF-8, LF, final newline and no trailing whitespace. Run
  `git diff --check` before committing.

## Source labels and practical pitfalls

- Report sources use cleveref's optional-argument form
  `\label[theorem]{wick:thm:main}` as well as plain `\label{...}`. Search
  with a pattern that allows both, for example
  `grep -rn 'label\(\[[a-z]*\]\)\?{wick:thm:main}' docs --include=*.tex`.
- Reports are revised upstream often (hypotheses corrected, labels added or
  renamed). After every `git merge origin/main`, check that each backticked
  source label cited in `docs/FORMALIZATION.md` and in Lean docstrings still
  exists in the current `.tex` sources, and re-read any statement whose
  report changed before claiming coverage of it.
- Files written by Windows tools may arrive with CRLF line endings. The
  checkout normalizes to LF, so after converting them `git status` can list
  files as modified while `git diff` is empty; `git add` those files to
  refresh the index.
- In Git Bash, a heredoc containing an apostrophe inside `'...'` quoting
  breaks the command; write Python or shell scripts to a scratch file with an
  editor tool and run the file instead.

## Other tools

- The Wolfram MCP server (`mcp__Wolfram__*`) can check symbolic identities
  (determinants, rational-function identities) before formalizing them; the
  separate `WolframEngine` server may fail to connect.
- Scratch files belong in the session scratchpad or under `.claude/`, never
  in `C:\` or the repository root.
