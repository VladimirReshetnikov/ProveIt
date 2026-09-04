# Agents working in `Analysis/FabiusFunction`

> [!CAUTION]
> **Never start Lean or Lake builds in parallel, and never start a second
> build while one is already running.** Run exactly one `lake build` at a
> time, with one target. Do not launch background build loops, pass a batch
> of targets, or use parallel runners such as `xargs -P`.
>
> One invocation is not by itself one process: Lake sizes its worker pool to
> hardware concurrency and starts one `lean.exe` **per core** whenever the
> target has a stale dependency set. On this machine several agent sessions
> share 13 GB, so that fan-out starves all of them. Bound the processes on
> every build:
>
> ```bash
> LAKE_JOBS=1 lake build +FabiusFunction.Basic
> ```
>
> **Corrected 2026-09-02: `LAKE_JOBS` does not bound anything here.** Lake
> `5.0.0-src+8c9756b` accepts neither `-j` (`unknown short option '-j'`) nor
> `--jobs`, and the environment variable is not read either. Measured on this
> machine with `LAKE_JOBS=1` exported and every `lean.exe` attributed by
> `ParentProcessId` to the invoking `lake`: an umbrella build with 136 modules
> pending went `0 → 1 → 12` workers across two 30-second samples, all twelve
> children of that lake, and had to be killed. The jump is a **burst**, not a
> ramp, and `lake` spends about a minute in trace checking before spawning
> anything, so an early sample sees nothing and proves nothing.
>
> Setting the variable costs nothing, so the command below keeps it, but **do
> not rely on it**. The only thing that actually bounds the worker count is the
> rule in "Building Lean" below: one module per invocation, and only when its
> dependencies are already compiled, so there is nothing to parallelize.
>
> An earlier measurement (2026-08-27: 11 concurrent `lean.exe` on a stale
> facade, exactly one under `LAKE_JOBS=1`) is **not** confirmation of the flag
> and needs recheck. A same-day test on `+FabiusFunction.AssociatedStirling`
> that peaked at two workers turned out to prove nothing at all: that module's
> closure is a near-linear chain, so at no point were more than two modules
> simultaneously ready to compile, and the peak was forced by the dependency
> graph rather than by any limit. **A concurrency test needs a target with
> genuine independent breadth, not merely several uncompiled modules.**
>
> Serialization is necessary but not sufficient: even at one worker a single
> `lean.exe` reached 1090 MB here and free RAM fell to 1.97 GB, so the
> out-of-memory symptoms below stay reachable with a correct driver.
>
> **Do not also set `LEAN_NUM_THREADS=0`.** That bounds the threads *inside*
> a process, which is not the resource under pressure, and `0` does not mean
> "auto": it serializes elaboration. Measured the same day under the same
> competing load, `+FabiusFunction.AlgebraicBranch` took **~35 minutes** with
> `LEAN_NUM_THREADS=0` and **~60 seconds** without it. If one process is
> itself too large, use a small positive value, never `0`.
>
> Starvation does not look like starvation. It surfaces as errors that read
> like corruption:
>
> ```
> failed to read file '...\Mathlib\...\Basic.olean'
> libc++abi: terminating due to uncaught exception of type std::bad_alloc
> ```
>
> These are out-of-memory symptoms, **not** broken proofs -- the same module
> built by itself succeeds. Never "fix" them by editing Lean sources.
>
> Before starting, check that nothing else -- including another agent session
> in a sibling worktree -- is already building; after interrupting a build,
> check for survivors, because stopping a task does not reliably kill the
> processes it spawned:
>
> ```powershell
> Get-Process lean,lake -ErrorAction SilentlyContinue
> ```
>
> If a build is running, wait for it rather than racing it.

Everything else in this file is ordinary project policy; the rule above is the
one whose violation has repeatedly destroyed build state, so it comes first.
See [Building Lean](#building-lean) for the full serialization recipe.

> [!IMPORTANT]
> **Package-local `SHA256SUMS` ledgers are abolished.** Do not create or
> restore any file whose basename is `SHA256SUMS` or starts with
> `SHA256SUMS.`.  Preserve provenance in Git history and in the surviving
> purpose-specific records; intake, consolidation, validation, and publication
> workflows must not require or regenerate the retired ledgers.

> [!IMPORTANT]
> ## Incoming reports have a mandatory publication gate
>
> For every report delivered under
> `docs/semi-formalized-research-frontiers/drafts/incoming/`, first perform a
> **quick archival intake and nothing deeper**: merge current `origin/main`,
> verify archive safety/integrity, unpack and file the report by theme, normalize
> repository line endings and record provenance in the surviving purpose-specific
> records, delete the ZIP, update
> the manifest and destination README, commit, push the feature branch, push
> ff-only to `origin/main`, and verify the remote SHA.
>
> **That verified `origin/main` push is a hard phase boundary.** Before it,
> agents must not start claim-by-claim mathematical review, semantic duplicate
> analysis, proof repair, editorial consolidation, experiment reproduction,
> document rewriting, or Lean formalization of the arrival. Read only enough
> title/abstract/package metadata to choose the destination and record accurate
> provenance and status. If more reports arrive during a batch, publish the
> current batch first and handle the newcomers in the next intake commit. Never
> let a moving inbox delay publication of already-filed reports.
>
> After publication, deeper reassessment and integration belong in one or more
> later commits. The canonical detailed checklist is
> [`docs/semi-formalized-research-frontiers/drafts/incoming/README.md`](docs/semi-formalized-research-frontiers/drafts/incoming/README.md).

This directory is sometimes developed by several agents concurrently.
Whether multi-agent coordination is in effect is stated by exactly one file:
[`AGENTS/STATUS.md`](AGENTS/STATUS.md).  While it says
`state: OFF` — the current state — agents work here one at a time and no
coordination rule binds anyone.  When the user flips it to `state: ON`, the
lightweight campaign protocol in
[`AGENTS/PROTOCOL.md`](AGENTS/PROTOCOL.md) applies:
claim-free optimistic Lean work, one standing owner per canonical document, a
lock-file build mutex, a 2-hour integration-latency cap, and live bookkeeping
on a dedicated orphan board branch — never on `main`.  The protocol carries
its own overhead assessment and rule-deletion authority so that it cannot
silently grow back into ceremony.

Everything below — the working rules from experience, the documentation
policy, and the Lean build guidance — is ordinary project policy and remains
in effect at all times, campaign or not.

The first (2026-08) campaign ran a heavier v1 protocol; its rules and
rationale survive only in git history — the deleted `docs/COLLABORATION.md`
and `docs/MULTI_AGENT_COORDINATION_PROPOSAL.md`, and
`git log -- Analysis/FabiusFunction/docs/registry/`.

## Working rules from experience (always in effect)

The rules that have actually cost time so far:

1. **Fetch and inspect `origin/main` before you start, and again before editing
   any module you did not create.** Merge it when the worktree is clean.  For a
   dirty shared worktree, freeze every writer and follow the path-overlap and
   Git-owner protocol (formerly in `docs/COLLABORATION.md`, now in its git
   history); never merge or stash behind another writer's back.  The same refactor has already been performed
   independently three times by three branches.

2. **A lemma belongs in the upstream-most module that can state it** — facts
   about `rvachevUp` needing only its definition and `IsFabius` go in
   `Basic.lean`, not `Differential.lean`. But relocating into `Basic.lean`,
   `Arithmetic.lean`, or `Differential.lean` invalidates all 172 modules and
   is the edit class most likely to collide, so announce it (on the board
   during a campaign, to the user otherwise) and batch such moves
   deliberately; see the placement-cost amendment preserved in the git
   history of `docs/COLLABORATION.md`.

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
   LaTeX/PDF document under `docs/semi-formalized-research-frontiers/`, with the
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
   `docs/PAPER_COVERAGE.md`, `AGENTS/*.md` and
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
   `docs/semi-formalized-research-frontiers/`, whose canonical TeX/PDF pair is
   `semi-formalized-research-frontiers.*`.

   **Watch the path length: this tree has no headroom.** The frontier drafts
   nest as
   `docs/semi-formalized-research-frontiers/drafts/<group>/<subgroup>/<package>/<file>`,
   and after the 2026-09-03 intake the longest filed path is **259 characters
   — one inside the Windows `MAX_PATH` limit of 260.** Past that limit tools do
   not report a length problem; they report the file as missing. `pdfinfo`
   said *"No such file or directory"* for a 724,630-byte PDF that `ls` listed
   correctly, and the only reason it was noticed is that a receipts loop failed
   on exactly one package of nine. An arrival whose archive stem is long enough
   will therefore break silently rather than error.

   So: name a filed package after its **document**, not after the archive it
   came in — archive names carry noise like `_LaTeX_and_PDF` that costs
   characters and says nothing — and measure the full path of every filed file
   before committing. Do not add another nesting level under `drafts/` without
   first shortening something above it.

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

8. **Merge conflicts in a generated PDF are never resolved.** When both sides
   of a merge changed a document, merge and settle the `.tex`, then rebuild
   the `.pdf` from the merged source with the same three-pass procedure;
   never select either side's binary. This is engineering policy, campaign or
   not.

9. **Prose is Libertinus, and committed PDFs must prove it.** Every LaTeX
   document under this directory sets its text in Libertinus. The shared
   preamble line
   `\IfFileExists{libertinus.sty}{\usepackage{libertinus}}{\usepackage{lmodern}}`
   falls back to Latin Modern *silently*, so a successful build proves
   nothing about fonts — after building, check
   `pdffonts <doc>.pdf | grep -c Libertinus`; zero means the fallback fired.
   Build on a machine with the Libertinus (type 1) packages installed. If
   they are missing, first attempt to install them (MiKTeX:
   `miktex packages install libertinus libertinus-type1`; TeX Live:
   `tlmgr install libertinus libertinus-type1`). Only if installation fails
   may a fallback-font PDF be committed, and that commit must also add or
   update a `README.md` beside the PDF requesting a rebuild on a machine
   with Libertinus installed; when a coordination campaign is active, relay
   the same rebuild request to the agents on other machines through the
   board. Remove the note when a Libertinus rebuild lands. Math
   intentionally remains Computer Modern (user decision, 2026-08-26): do not
   add `libertinust1math` without an explicit new user decision — and should
   that ever change, it must be loaded *after* `amssymb`/`bm`, because the
   reverse order corrupts the wide-accent glyph chain (`\widehat`,
   `\widetilde` render as a stray vertical stroke).

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

### Seed the corpus build outputs too, or pay a day

The `packages` junction fixes Mathlib and nothing else. A fresh worktree still
has **zero** `FabiusFunction` oleans, and compiling the atlas from scratch costs
the better part of a day — a day the kernel is unavailable to everyone else, not
just to you. Measured 2026-09-02, two worktrees that had only ever built the
closures they needed held 181 and 765 of 868 modules, so the gap between a
seeded and an unseeded worktree is the difference between minutes and a night.

**Prefer a junction of the whole `.lake` to a sibling worktree.** This is the
user's standing preference — *use a junction, don't copy* — and it is also
instant and duplicates nothing:

```sh
cmd //c "mklink /J <yours>\.lake <sibling>\.lake"
```

Pick the sibling with the freshest corpus, and check rather than assume —
`C:\ProveIt\.lake` has Mathlib built but **zero** `FabiusFunction` oleans, so
junctioning to it forces a full rebuild:

```sh
for d in /c/ProveIt/.claude/worktrees/*/; do
  echo "$(ls $d/.lake/build/lib/lean/FabiusFunction/*.olean 2>/dev/null | wc -l)  $d"
done
```

The trade-off to accept consciously: the build directory is then *shared* with
that sibling, so only the machine-wide one-kernel rule keeps two drivers from
racing inside it.

**Copy only when you need artifact isolation** from the sibling session. From
PowerShell:

```
robocopy <donor>\.lake\build <yours>\.lake\build /E /MT:8 /R:1 /W:1
```

Measured 2026-09-02: 1.353 GB, 6005 files, 1m48s, after which a new leaf module
built in 25–90 seconds. `robocopy` exits **1** when it successfully copies
files; treat any code below 8 as success.

Two checks first, whichever route you take — both cheap and both necessary.
Lake decides staleness from content hashes, so a sibling at a different commit
is perfectly good for every module whose source happens to match and silently
useless for the rest:

1. `git merge-base --is-ancestor <donor HEAD> HEAD` — the donor's commit is in
   your history.
2. `md5sum` your intended dependency sources against the donor's copies. Only
   the closure you mean to build has to match; your own new modules are leaves
   and would rebuild anyway.

**Ask the donor's owner to hold builds before you start, and tell them when you
finish.** The donor is usually another agent's live worktree, and a module
rewritten mid-copy leaves you a torn olean whose failure looks like corruption.
Nothing of theirs is written — it is a read — so the only cost to them is the
pause.

### Lake's job counter is not progress, and the facade is not the gate

Two mistakes made repeatedly on one night, 2026-09-02, both worth naming.

**The job counter says almost nothing about remaining work.** An umbrella build
reporting `3492 of 3598 jobs` looks 97% done and is not: most of those jobs are
Mathlib replays out of the shared package cache, resolved in milliseconds, while
the corpus modules that remain cost 55–70 seconds apiece. The two are not
commensurable, so the ratio is meaningless. When that run was killed, only about
180 corpus modules had actually been built. Count oleans
(`ls .lake/build/lib/lean/FabiusFunction/*.olean | wc -l`) against sources; do
not quote the counter as progress.

The same run also failed at `3607 of 3645` on an earlier attempt, which was read
as "38 short". It is not evidence of nearness at all: the fan-out persists to the
end and then exhausts memory. Two modules blamed for that failure
(`SincProductShells`, `StirlingAsymptotics`) each built green in under a minute
when given an invocation of their own.

**Prefer a scoped validation to the facade.** Building every module answers
"does the corpus compile"; after a wave of edits the question is "did anything I
changed break anything downstream of it", and those differ by the several hundred
untouched modules that make the facade an overnight job. Compute the transitive
dependents of what actually changed and build those in topological order, one
invocation each, so every dependency is already compiled when its turn comes.
Two scripts do exactly this:

```sh
python3 Analysis/FabiusFunction/scripts/affected_modules.py <base> --stats --out affected.txt
sh Analysis/FabiusFunction/scripts/validate_affected.sh affected.txt
```

The first closes the change set under the *reverse* `import FabiusFunction.*`
graph and emits a topological order; `--stats` reports how many of those lack a
built olean, which is the honest estimate of remaining work. The second drives
one `lake` invocation per module and writes a log ending in
`VALIDATE-DONE modules=N failures=M`.

Measured the same night: 59 changed modules closed to 270 dependents, of which
only 74 lacked an olean — roughly two hours instead of eleven, and it covers
exactly the risk the edits introduced. The several hundred untouched modules a
facade build would also compile cannot have been broken by the diff.

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
LAKE_JOBS=1 lake build +FabiusFunction.Basic
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
