# Agents working in `Analysis/FabiusFunction`

Several agents develop this directory concurrently in separate worktrees.
The user has designated one coordinator for the current campaign.  The
operational rules below and the live
[`docs/registry/coordinator.md`](docs/registry/coordinator.md) board are current
project policy; [`docs/COLLABORATION.md`](docs/COLLABORATION.md) explains the
reasons and remains open for focused revision.

## Live coordination -- mandatory before writing

At the start of every work session, after every fetch, and before every merge
or push, read the coordinator board from the fetched `main`, even when your
worktree is dirty and cannot merge yet:

```sh
git fetch origin
git show origin/main:Analysis/FabiusFunction/docs/registry/coordinator.md
```

The board contains the pinned integration SHA, hot paths, integration queue,
build ownership, and branch-specific instructions.  An instruction addressed
to your exact branch is binding until the board releases it.  If your branch is
not listed, you have no write lease yet: inspect read-only, then publish a
status/claim in a new file named `docs/registry/<branch-with-slashes-replaced-by-dashes>.md`.

During the current collision-recovery checkpoint:

1. **Push feature branches, not `main`.** Only the coordinator advances
   `origin/main`.  Never force-push.  A rejected fast-forward is a signal to
   fetch and reread the board, not to retry blindly.
2. **One branch, one registry file.** Each worker edits only its own registry
   file.  Only the coordinator edits `docs/registry/coordinator.md`, this live
   section of `AGENTS.md`, the coordination notice in `README.md`, and the
   campaign-wide coordination documents.
3. **No implicit lease.** A write lease names exact paths and expected public
   declarations.  Topic names such as "asymptotics" or "documentation" do not
   lease a directory.  Do not expand the path set until the coordinator
   acknowledges the request on the board.
4. **Preserve before synchronizing.** If your worktree is dirty, do not stash,
   reset, or merge over it.  Stop expanding the edit, make a clearly labelled
   checkpoint commit on your feature branch when coherent (or an explicit WIP
   commit when necessary to preserve it), push that branch, and report the
   exact SHA and validation state in its registry file.
5. **Build tokens are per physical host.** On `codexbox`, no agent starts Lean,
   Lake, `pdflatex`, or another cache-mutating validation job unless the board
   assigns the token.  Let an already-running job finish; do not kill another
   worktree's process.  The other machine maintains the same one-owner rule
   independently and records its owner on the board.
6. **Binary PDFs are never conflict-resolved.** Freeze both sources, integrate
   the TeX semantically under one owner, then rebuild the PDF once with three
   passes.  Never take a PDF wholesale from either side of a conflict.

Status replies use the `SYNC Fabius` template in `docs/COLLABORATION.md`, are
committed only to the worker's feature branch, and are pushed promptly.  The
coordinator discovers them from advertised branch tips and updates the board.

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

6. **The primary exposition is a formalization-backed document, not a research
   notebook.** Every mathematical assertion placed in
   `docs/Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
   must have an actual proved Lean counterpart. This includes displayed
   theorems and equations, prose claims, numerical identities, bounds,
   convergence statements, algorithms and their correctness or complexity
   claims, and alleged consequences that may look immediate. Record the exact
   declaration name and module in the exposition's Lean guide or adjacent
   audit text. A suggestive definition, an uncompiled draft, a theorem with
   stronger hypotheses or a weaker conclusion, or an informal derivation is
   not a counterpart.

7. **Unformalized mathematics belongs on the research frontier.** If any part
   of a draft lacks an exact proved Lean counterpart, move that part to a
   LaTeX/PDF document under `docs/non-formalized-research-frontiers/`, with the
   missing formal obligation stated explicitly. Do this no matter how
   straightforward, standard, numerical, or plausible the claim appears. Do
   not weaken the wording until it merely resembles an existing theorem, and
   do not present frontier material as established by the project.

8. **Draft directories are temporary inboxes.** Material under
   `docs/Fabius_Function_and_Rvachev_Up/drafts/` must be dispositioned
   claim-by-claim: integrate the Lean-backed part without duplicating the main
   exposition, move the remainder to the research-frontier tree, preserve any
   necessary citations or provenance, then remove the processed draft. Delete
   the `drafts/` directory itself when it becomes empty; it is not an archive.

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
   `docs/non-formalized-research-frontiers/`, whose canonical TeX/PDF pair is
   `non-formalized-research-frontiers.*`.

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
   rebuilt `.pdf` is an incomplete commit. Before every push that sends a
   changed `.tex` file to `origin/main`, its matching rendered `.pdf` must
   already be rebuilt and committed. Never push a TeX/PDF mismatch to the main
   branch.

5. **Verify the rendered PDF, not the source.** Never write LaTeX through a
   shell heredoc or a Python patch script that round-trips through
   `unicode_escape`: both silently destroy backslashes and non-ASCII
   characters, and LaTeX does *not* error on the result — it renders
   something plausible and wrong. Use the editor tools, then check the page
   count and the log.

6. **Cross-reference the formalization.** A mathematical document should carry
   a table mapping its objects to the Lean names and modules that formalize
   them, and should state explicitly what is *not* claimed.

7. **Respect the exposition boundary.** The primary synthesis may contain only
   mathematics backed by proved Lean declarations. Research-frontier documents
   may discuss conjectural, heuristic, partially formalized, or refuted
   material, but must label that status and the outstanding proof obligations
   plainly. When auditing a draft, inspect the Lean source rather than relying
   on a declaration name, an `.olean` file, a previous agent's report, or a
   paper citation as evidence of formalization.

## Building Lean

Build one module per `lake` invocation, in topological order. `LAKE_JOBS=1` is
not enough: a single `lake build A B` still starts two `lean` processes, and on
this 13 GB machine both then die with a misleading
`failed to read file '….olean'`, which is an out-of-memory symptom rather than
a real error.

The module target needs a `+` prefix. `lake build FabiusFunction.Basic` fails
with `unknown target`; `lake build +FabiusFunction.Basic` is the working form.

**If you drive the serialization from a script, give the script a PID lock.**
Stopping the harness task that launched a background script kills the wrapper
but not the script, so relaunching leaves two serialized loops racing — which
is exactly the double-`lean` situation the serialization exists to prevent,
reintroduced by the tool meant to stop it. The symptom is an interleaved build
log: one module logged `OK` twice with different timings, two consecutive
`BUILD` lines for a single module, a count of completed modules that goes
*down* between polls, and free memory pinned near half a gigabyte. Confirm
with `Get-Process -Name lean,lake,sh` and kill the survivors by PID before
relaunching; do not trust the task's reported status.

A worktree without its own `.lake` would rebuild Mathlib from scratch. Give it
one whose `packages` is a directory junction to the shared
`C:\ProveIt\.lake\packages`, so the built Mathlib is reused while the Fabius
build outputs stay isolated per worktree:

```sh
mkdir -p .lake
cmd //c mklink //J ".lake\\packages" "C:\\ProveIt\\.lake\\packages"
```

### When to pay a root-module invalidation

Moving a declaration into `Arithmetic.lean`, `Basic.lean` or `Differential.lean`
invalidates essentially the whole corpus, so the placement question is really a
cost question. The rule that reconciles the two decisions taken in this
directory — one branch paid a 158-module invalidation to consolidate ten
byte-identical copies of a triangular-number identity into `Arithmetic.lean`,
another deliberately did not pay one to place new generic `expCoeff` lemmas in
`SaddleExpansionAlgebra.lean` — is:

> **Pay a root-module invalidation to remove duplication that already exists.
> Never pay one to pre-position a new declaration that has no duplicates yet.**

Removing `n` existing copies buys something that cannot be bought later without
paying the same price again. A new declaration that is merely in a
lower-than-ideal module costs one future `git mv`-scale edit, and nothing else.
Record the correct long-term home in a doc comment either way; recording is
free, moving is not.

### The defect a compiler cannot see: right formula, wrong prose about it

Every defect found in one night's work on the asymptotic layer that was *not*
found by the compiler had the same shape. The formula was correct, every number
computed from it was correct, and the false statement was a sentence
*summarising* the computation instead of performing it. Four variants, all real,
all from that one night:

- **Wrong label on a right object.** The jet weights were called "the signed
  Stirling numbers of the first kind". They are those shifted by one in each
  index, `c(n,m) = s(n+1,m+1)`. `s(n,0) = 0` for `n ≥ 1` but
  `c(n,0) = (-1)^n n!`, which carries the whole non-oscillatory part of the jet,
  so resolving the name would have deleted it. Every number in both documents
  was computed from the product, never from the name, so nothing numerical was
  wrong and nothing could have caught it.
- **A measurement reported as a property.** "`A_2` has mean about 0.5199 and
  peak-to-peak about 3e-3" was a description of a sample that spanned 41% of a
  period and missed the maximum. The true values are 0.5203422413 and 3.880e-3.
- **A size estimate reasoned to rather than computed.** "Products of derivatives
  of `Psi` are below 1e-11" — they reach 1.4e-7, for exactly the reason the same
  document argued two sections later. "`Psi` is tiny" and "differentiation
  cancels the smallness of `Psi`" sat in one document without either author
  noticing they contradict.
- **A derivation truncated and then described as complete.** A closed form for a
  mean was derived correctly, a third-order term was dropped as negligible
  mid-working, and the result was printed with an equals sign. The dropped term
  was 5.6e-22 — invisible, and the difference between an identity and an
  approximation.

The rule that would have caught all four:

> Any sentence stating a mean, a magnitude, a negligibility, or the name of a
> known object must be **computed, not reasoned to** — and the computation must
> be carried to exactness, not to the point where the answer stops changing.

Two practical corollaries. Quoting ten digits of a linearization is an
overclaim; say which object the digits belong to. And when comparing quantities,
state the convention in words — an amplitude is half a peak-to-peak swing, and a
row mixing the two survives every check whose ratios happen to double on both
sides.

Note what did find these: a purely numerical re-derivation, with no computer
algebra, run against the same claims. Two symbolic routes agreeing is weaker
evidence than it looks when the thing at issue is prose, because both routes
compute from the formula and neither reads the sentence.

### The defect a preflight cannot see: a tactic doing something else

The complement of the previous section. Reading catches wrong identifiers;
it does not catch a correctly-spelled tactic behaving differently from what the
author pictured. Every failure the compiler found in one night's new modules was
of that kind, and none was mathematical:

- a `field_simp` that **closed its goal**, so the following `ring` failed with
  `No goals to be solved`;
- a `simp` that **did not close** its goal, because `Polynomial.coeff_one` is
  not a simp lemma in this Mathlib;
- a `simp` that **unfolded a definition** — `Nat.doubleFactorial` is declared
  `@[simp] def`, and simp first normalized `2 * (j + 1)` to `2 * j + 2`, which
  then matched the `k + 2` equation, dissolving the double factorial before it
  could be used. Use `rw`, or `simp [-Nat.doubleFactorial]`;
- a `simp only [map_add]` that **reached into a second homomorphism**.
  `Polynomial.C` is itself a ring hom, so `map_add` rewrote `C (a + b)` into
  `C a + C b` inside the coefficients, and `(C a + C b) * X ^ n` no longer
  matched the monomial lemma.

The last one deserves its generalisation, which is not specific to polynomials:

> A simp set that is **asymmetric in an algebraic structure** will silently do
> half a job, and *which* half is selected by a property of the data rather than
> of the goal.

There, the set carried `map_add` but not `map_sub`: of five monomials, the three
whose coefficients contained a subtraction survived intact and contracted
correctly, while the two that were pure sums were decomposed and left behind.
Nothing about the goal predicted the split.

Practical defences, in order of cost: prefer `rw` to `simp` where the rewrite
positions are known; state a helper lemma over **opaque variables**, so a simp
set has nothing to decompose (this is what fixed the last case); and when a
`simp` is genuinely wanted, prefer `simp only` with a named list.

### Preflight instead of building, when the build is scarce

A read-only preflight — one agent checking every identifier and tactic against
the real Mathlib sources at `C:\ProveIt\.lake\packages\mathlib\Mathlib`, then a
second agent instructed to *refute* each of its conclusions — is a real
substitute for a compiler when the compiler is contended. It needs no build
slot and runs while somebody else holds one.

The evidence from this directory, rather than the advice: a preflight over two
new modules found four blockers before any build — `∞` being `scoped[ContDiff]`
notation that does not leak through `import`, `Finset.range_subset` being the
wrong lemma for `n ≤ N`, `HasDerivAt.sum` producing the Pi-valued sum where
`HasDerivAt.fun_sum` is wanted, and one cancellation lemma being unable to serve
two different associations of the same expression. When those modules were
finally compiled, the compiler found exactly one further defect, and it was one
the same preflight had already listed as a risk: a `field_simp` that closes its
own goal, leaving the following `ring` with `No goals to be solved`. An earlier
preflight on a different branch found eight errors in six modules, every one
later confirmed by a build.

So: preflight before committing uncompiled Lean, and say in the commit message
that you did.

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
