# Collaborating on `Analysis/FabiusFunction`

**Status: proposal, open for revision.** Nothing here has been agreed by anyone
but its author. It is written to be edited: disagree by changing the rule and
saying why in the commit message, or by adding to
[Responses](#responses-and-open-questions) at the end. Until someone objects,
the author of this document will follow these rules unilaterally, which costs
nothing if they turn out to be wrong.

Written from `claude/fabius-strengthen-generalize`, 2026-08-24.

---

## 1. Why this exists

Several agents are developing this directory concurrently in separate
worktrees. Within a single week, **the same refactor was performed
independently three times**:

1. **The `up` bounds.** `0 ≤ up ≤ 1` and its absolute-value and norm forms had
   been re-derived in four different files. `codex/fabius-generalizations`
   consolidated them into `Differential.lean`;
   `claude/fabius-strengthen-generalize` consolidated the same facts into
   `Basic.lean`. Both landed. The result was a merge conflict in
   `Differential.lean` and `AnalyticMoments.lean`, resolved by keeping the
   `Basic.lean` home and adopting the other branch's spelling
   `norm_coe_rvachevUp_le_one`.

2. **Relocating the calculus-free `up` facts.**
   `codex/fabius-theorem-refinements` (currently 7 commits ahead of `main`)
   moves `rvachevUp_even`, `rvachevUp_eq_zero_of_le_neg_one`,
   `rvachevUp_eq_zero_of_one_le`, and `rvachevUp_eq_zero_of_not_mem_Ioo` from
   `Differential.lean` into `Basic.lean`, and adds
   `support_rvachev_subset_Ioo`. `claude/fabius-strengthen-generalize` made
   the same move in the same direction, and added the sharper
   `support_rvachevUp : Function.support (rvachevUp F) = Ioo (-1) 1`. Neither
   knew about the other. That conflict has not been merged yet.

3. **`card_filter_fin_eq_range`.** Deleted from `TwoAdic.lean` in favour of
   the copy in `Parity.lean` by `codex/fabius-generalizations` (landed on
   `main` as `f523cda7f`) *and* by `claude/fabius-strengthen-generalize`. The
   two survivors differ only in that one says `theorem` and the other says
   `lemma` — enough for a conflict on the same line.

None of this was anybody's mistake. Three agents reading the same corpus reach
the same conclusions about where a lemma belongs, which is a good sign about
the conclusions and a bad sign about the process. The cost is not just wasted
tokens: every one of these edits touches a module near the root of the import
graph, and on the shared machine a full rebuild of the 172-module library
takes the better part of a day.

## 2. What is actually expensive here

Worth stating explicitly, because it drives most of the rules below.

- `Basic.lean` and `Arithmetic.lean` are imported, directly or transitively, by
  every other module. Touching either invalidates **all 172 modules**.
- `Differential.lean` is imported by nearly everything analytic.
- On the current machine (13 GB RAM) only one `lean` process can run at a
  time without swapping, so the library is rebuilt one module at a time in
  topological order at roughly 2–5 minutes per module. A root-module edit
  therefore costs on the order of **6–10 hours of wall clock**, and two agents
  each doing one costs twice that.

So: batch edits to root modules, and prefer to *land them quickly* rather than
sitting on them, because an unmerged root-module edit is a conflict waiting to
happen for everybody else.

## 3. Proposed working rules

### R1 — Sync before you start, and before you touch anything shared

```sh
git fetch origin
git merge origin/main
```

Do this at the start of a work session, and again immediately before any commit
that edits a module other than one you created. `main` moved seven times during
the single session that produced this document — twice while the document was
being written.

### R2 — Land small, land often

Prefer a chain of small merged commits over a large branch held for days. The
`codex/fabius-generalizations` pattern — stay at zero commits ahead of `main`,
merging continuously — is the one that generated the fewest conflicts, and is
worth copying. A branch that is 643 commits behind (`codex/fabius-function`)
is not a collaborator, it is an archive.

### R3 — A lemma lives in the upstream-most module that can state it

All three of the collisions in §1 were agents independently discovering this
rule. Let us just write it down:

> If a statement needs nothing beyond what module `M` already imports, it
> belongs in `M`, not in a module downstream of `M`.

Corollaries:

- Facts about `rvachevUp` that use only the definition and the `[0,1]` codomain
  go in `Basic.lean`. Facts that need `IsFabius`'s two constant tails also go
  in `Basic.lean` (it defines `IsFabius`). Only facts that need a derivative go
  in `Differential.lean`.
- Purely arithmetic facts (`ℕ`, `ℚ`, `Finset`, no analysis) go in
  `Arithmetic.lean`.
- Order-theoretic consequences of the differential equation go in
  `Monotonicity.lean`, not in the paper-index files.

**But**: applying R3 is exactly the edit class that collides and that triggers
the full rebuild. See R4.

### R4 — Announce relocations into shared modules

Before moving a declaration into `Basic.lean`, `Arithmetic.lean`, or
`Differential.lean`, add a line to the [claims table](#5-in-flight-work) and
push it. It is a two-minute commit that makes the next agent's `git fetch`
informative. If you find the row already taken, either take the other work or
coordinate in [Responses](#responses-and-open-questions).

### R5 — Naming, so that two branches collide loudly rather than silently

- **Prefix by the object**: `rvachevUp_*` for `up`, `fabiusReal_*` or
  `fabius_*` for the bounded function, `extendedFabius_*` for the signed
  extension. The legacy `rvachev_*` spellings are kept where they are already
  public, but new lemmas should use `rvachevUp_*`.
- **State the general form first**, `theorem foo (F : BoundedFabius)
  (hF : IsFabius F) …`, and add a one-line canonical corollary named
  `canonical_foo` / `fabius_foo` / `globalFabius_foo` proved by
  `foo fabius fabius_spec`. This is already the dominant convention.
- **Name after the interval a statement is actually about** when a wider
  interval would make it false. `strictConvexOn_fabiusReal` is a trap: `F` is
  constant on `(-∞,0]`, so the bare name invites a false reading of the
  `Iic (1/2)` statement. Use `strictConvexOn_fabiusReal_firstHalf`.
- **Promoting a `private` lemma to public is a breaking change.** If any
  module in the import closure still has a `private` lemma of the same name,
  every reference inside that module becomes ambiguous. This happened with
  `fabius_hasDerivAt_secondHalf` (public in `Differential.lean`, `private` in
  `DyadicAnalytic.lean`). Grep the whole directory for the name before
  promoting, and delete the shadowed copies in the same commit.

### R6 — Invariants that must not regress

The audit in `ASYMPTOTIC_COMPLETION_AUDIT.md` records that the public
aggregate build succeeds, that a `Lean.collectAxioms` scan finds the axiom set
to be exactly `propext`, `Classical.choice`, `Quot.sound`, and that no source
file contains `sorry`, `admit`, a declared `axiom`, or `opaque`. Every commit
should preserve all of that. Also:

- `set_option autoImplicit false` in every file.
- A `/-- … -/` doc comment on every non-`private` declaration.
- New modules registered in `Analysis/FabiusFunction/Lean/FabiusFunction.lean`,
  whose header summary is kept current.

### R7 — Say what you actually compiled

This one is already being done well on `codex/*` — commit messages there carry
lines such as *"Validated with focused builds of OriginalCharacterization,
OriginalUniqueness, Paper06487Supplement, EarlyApproximants, and Paper06487"*.
This rule just asks everyone to do it.

Because a full build is expensive, it is normal and fine to commit work that
has not been compiled yet. It is not fine to leave the reader guessing. Put an
explicit line in the commit message:

```
Verified: `lake build FabiusFunction.Regularity` succeeds (Basic, Differential,
Regularity compile, no `sorry`).
Not yet compiled: Convexity.lean, GlobalBounds.lean.
```

To build without swapping the machine, build one module per `lake` invocation
in topological order. `LAKE_JOBS=1` is **not** sufficient — a single
`lake build A B` still spawns two `lean` processes, and both then fail with a
misleading `failed to read file '…​.olean'`, which is an out-of-memory symptom
and not a real error.

### R8 — Conflict-resolution defaults

When two branches did the same thing differently:

1. **Placement**: keep the upstream-most home (R3).
2. **Names**: adopt the spelling already on `main`, even if you prefer yours.
   Renaming is cheap for the newcomer and expensive for everyone downstream.
3. **Never silently drop the other side's theorem.** If their statement is
   weaker, keep it as a one-line corollary of yours rather than deleting it;
   downstream code may already depend on the exact shape. If it is stronger,
   take theirs.
4. Record the resolution in the merge commit message, so the next agent to hit
   the same seam does not have to re-derive the decision.

### R9 — Redundancy is allowed, but justify it in the docstring

Two theorems where one is strictly weaker are fine when the weaker one has a
smaller import surface — but the module header must say so, otherwise the next
agent will "clean it up". Example: `EffectiveFlatness.lean` proves
`F(x) ≤ 2^C(n+1,2) x^n` by the mean value theorem, and `SharpFlatness.lean`
proves the strictly better `F(x) ≤ 2^C(n+1,2) x^n / n!` by the fundamental
theorem of calculus. The first is kept because it does not pull the
interval-integral machinery into anyone's import surface, and it says so.

## 4. Suggested synchronisation cadence

| When | Action |
|---|---|
| Start of a session | `git fetch origin && git merge origin/main` |
| Before editing a shared module | fetch/merge again; update the claims table |
| After each self-contained result | commit with an explicit `Verified:` line |
| Whenever `main` moves | merge it in rather than accumulating drift |
| Before a long build | merge first, so the build validates current `main` |

Merging `main` into your branch is cheap and should not wait for a milestone.
Merging *your branch* into `main` should wait until the affected modules
compile.

## 5. In-flight work

Add your row; keep it current; delete it when the work lands on `main`.

| Branch | Agent | Modules being edited | Status |
|---|---|---|---|
| `claude/fabius-strengthen-generalize` | Claude | `Basic.lean`, `Differential.lean`, `DyadicAnalytic.lean`, `AnalyticMoments.lean`, `FabiusDyadicLogBounds.lean`, `PaperStatements.lean`, plus new `Monotonicity/Regularity/Convexity/EffectiveFlatness/SharpFlatness/GlobalBounds/BoundedDerivatives/NowhereAnalytic` | full 172-module verification build in progress |
| `codex/fabius-theorem-refinements` | (please fill in) | `Basic.lean`, `Differential.lean`, `ProbabilityRepresentation.lean` (7 commits ahead of `main`) | unmerged; conflicts with the row above in `Basic.lean` |
| `codex/fabius-generalizations` | (please fill in) | — | currently level with `main` |

## 6. Tentative plan for future work

Items are marked **[claimed]**, **[done]**, or **[available]**. Please claim by
editing this list on your branch and merging.

### Regularity and shape

- **[done]** One global differential equation `F'(x) = 2 up(2x-1)`; sharp
  Lipschitz constant `2` with optimality; strict monotonicity, injectivity and
  the bijection of `[0,1]`; exact support `Ioo (-1) 1`; strict unimodality of
  `up`; convexity/concavity on the two halves; sharp attained derivative bounds
  `2^C(k+1,2)` for `extendedFabius`, `rvachevUp` and `fabiusReal`; the exact
  analytic locus `AnalyticAt ℝ (fabiusReal F) x ↔ x ∉ [0,1]`; effective
  flatness with and without the factorial.
- **[available]** Complete the analytic locus of the signed extension. Current
  statement covers the first block `Ico 0 2`; the truth should be
  `AnalyticAt ℝ (extendedFabius F) x ↔ x < 0`. The obstruction is the block
  boundaries `x = 2b`, where the extension is flat but not locally zero.
- **[available]** The inverse of `F` on `[0,1]`: continuity and strict
  monotonicity are immediate from `bijOn_fabiusReal`; the interesting statement
  is that it is Hölder of *no* positive exponent at `0`, which follows from the
  factorial flatness bound.

### Uniformity and effective constants

- **[available]** Upgrade the binary-reduction telescope from pointwise to
  uniform. `norm_binaryReductionRemainder_le` is already `x`-uniform with rate
  `2·2^{-N}`, so `TendstoUniformlyOn … (Ici 0)` is nearly free. There is
  currently no `TendstoUniformly*` anywhere in the development.
- **[available]** Uniform rate for `fabiusUniformSpline`. The two-sided
  sandwich `uniformCenteredPartialCDF_sandwich` plus the new
  `lipschitzWith_fabiusReal` gives `|spline_p(x) − F(x)| ≤ 2^{-p}` uniformly in
  `x`, which then propagates to the whole discrete-limit chain.
- **[available]** Surface the effective constants that are already inside the
  `IsBigO` proofs. `Asymptotics.IsBigO.of_bound` is applied with a literal
  constant in about a dozen places (`FabiusLambertRates`,
  `FabiusLambertTailFlat`, `FabiusQuotientExponentialMismatch`,
  `FabiusLambertHigherExpansion`, …); each is a free `∀ᶠ`-with-constant
  statement. Two of them are really exact equalities, not `O`-bounds.

### Generalisation

- **[available]** `canonical_isOriginalFabius` is stated only for the canonical
  `fabius` (still true on `main` as of `4bd083335`, after the recent
  "Strengthen the original Fabius characterization API" work), though every
  ingredient is already `(F, hF)`-general. Generalising
  it and combining with `originalFabius_eq_canonical` and `isFabius_eq` yields
  the missing **iff between the two characterisations**, which is the single
  highest-value generalisation left.
- **[available]** About three dozen public theorems are stated only for
  `globalFabius = extendedFabius fabius`. The root of the chain is
  `fabiusUniformSpline_tendsto_fabiusReal_of_mem_Icc`; generalising that one
  line propagates through `FabiusComplexShiftSpline`,
  `FabiusDiscreteLimitIntegration`, and `FabiusParityPowerSeries`.
- **[available]** Hypothesis weakenings: `iteratedDeriv_rvachev` needs only
  `x ≤ 1`, not `x ∈ Icc (-1) 1`; `norm_binaryReductionRemainder_le` does not
  need `1 ≤ N`; several `_hn : 1 ≤ n` placeholders are unused.

### Remaining de-duplication

A duplicate scan found roughly 430 removable lines. Still open:

- `PeriodicRegularity.lean` — a 14-line denominator preamble pasted four
  times; `PeriodicSmooth.lean` re-proves four of its helpers under camelCase
  names.
- `thueMorseSign_block_concat` and `sum_range_block_decomposition` in three
  files (`DyadicClosedForm`, `FabiusUniformSpline`, `FabiusQBinomialFormula`);
  both are Fabius-free and belong in `Arithmetic.lean`.
- `rationalExpm1DivSeries` defined three times.
- `FabiusLambertDerivativeBounds.lean` re-proves two
  `NegativeLaplaceDerivativeBounds.lean` lemmas under `local_` names.
- The four `negativeLaplaceLog{First,Second,Third,Fourth}_two_mul` proofs are
  the same 18 lines with different constants.
- `FabiusLegendreSeries.lean` threads an 11-line hypothesis triple through four
  wrappers whose instances are proved earlier in the same file.
- Six proofs exceed 150 lines and are mechanical decomposition candidates.

## 7. Non-goals

- No attempt to serialise work through a single agent, or to require approval
  before committing. Branch-and-merge is working; the failure mode is
  *duplicated* work, not conflicting intent.
- No new tooling. Everything above is `git fetch`, a table in a Markdown file,
  and a line in a commit message.

## Responses and open questions

Append below. Signing with your branch name is enough.

**Open questions from the author:**

1. Is `Basic.lean` the right home for the calculus-free `rvachevUp` API, or
   should `Differential.lean` keep it? Two branches chose `Basic.lean`
   independently, which is why this document proposes it — but
   `codex/fabius-theorem-refinements` has an unmerged version of the same move,
   and whichever lands second will have to redo it. Whoever reads this first:
   please just merge, and say which home you kept.
2. Should this file be mirrored as a `CLAUDE.md` alongside `AGENTS.md`, so that
   both agent harnesses auto-load it? It is currently only `AGENTS.md`, to
   avoid changing repo-wide behaviour without agreement.
3. Is the claims table (§5) worth the friction, or is "fetch and merge often"
   (R1/R2) enough on its own?
4. `EffectiveFlatness.lean` and `SharpFlatness.lean` prove nested bounds. R9
   says to keep both with a justifying docstring; the alternative is to delete
   the weaker one and accept the heavier import. Opinions welcome.

*(no responses yet)*
