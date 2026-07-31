# Catalog of known Lean and Rocq type-system defects and kernel loopholes

Working registry for the goal stated in [`README.md`](README.md): that this
directory eventually represents *every* known type-system defect and
implementation loophole in Lean and Rocq/Coq.

**How to read the coverage column.**

| Mark | Meaning |
| --- | --- |
| **artifact** | A machine-checked exhibit lives in this directory, with a control and a pinned-toolchain matrix. |
| **report** | A written analysis lives in [`Reports/`](Reports/), pinned to toolchain versions. |
| **noted** | Recorded here only: understood and cited, no local artifact yet. |
| **gap** | Not represented at all. Candidate work. |

**Verification status is stated separately from coverage.** "Verified here"
means it was reproduced on this machine with an explicitly pinned toolchain
(`elan run leanprover/lean4:<v> lean --trust=0 <file>`) during the survey dated
in the row. Everything else is recorded from the upstream tracker and is *not*
independently confirmed — say so when citing it.

Last survey: **2026-07-30** (Lean and Rocq trackers, Lean Zulip, and the blog
posts listed in §5, chiefly Tristan Stérin's
[*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood),
which reports a systematic AI-driven search for proofs of `False` in both
systems).

---

## 1. Lean 4 — official kernel

### 1.1 Defects that yield an axiom-free `False`

| Issue | Defect | Status upstream | Coverage |
| --- | --- | --- | --- |
| [#14484](https://github.com/leanprover/lean4/issues/14484) | The checked path for `Declaration.opaqueDecl` does not reject free variables in the body. With the inference cache, a safe metaprogram adds an opaque constant of type `False` whose value is an unbound `fvar`. `#print axioms` reports nothing; `leanchecker --fresh` replays it. | Fixed by PR #14498, merged 2026-07-22; shipped in `v4.32.2`. | **report** — [`Reports/2026-07-29-lean-4.33-backport-gap.md`](Reports/2026-07-29-lean-4.33-backport-gap.md) |
| [#14576](https://github.com/leanprover/lean4/issues/14576) | In `elim_nested_inductive_fn`, nested-inductive parametric arguments are substituted by `instantiate_pi_params` **without being type-checked**; they never appear in the auxiliary declaration, so they escape all kernel checking. A wrong-structure projection is inserted there, hidden behind a deliberate `Expr.hash` + `approxDepth` collision. Found while reviewing a claimed 300-line Collatz proof. | Fixed by PR #14577, merged 2026-07-28; shipped in `v4.32.2`. | **report** — same file |

The report's own finding: **`v4.33.0-rc1` predates both fixes and accepts both
proofs of `False`**, because the 4.33 branch was cut before either landed and
neither was cherry-picked.

### 1.2 Live defects (not fixed as of the survey)

| Issue | Defect | Status | Coverage |
| --- | --- | --- | --- |
| [#12746](https://github.com/leanprover/lean4/issues/12746) | `Expr.proj` indices are narrowed from `size_t` to C++ `unsigned` in `infer_proj`, `reduce_proj`, and `lazy_delta_proj_reduction`, guarded only by `is_small()` (`< 2^63`, not `< 2^32`). Index `2^32 + k` silently becomes `k`, so the kernel infers, reduces, and **accepts** projections that are out of range for the structure. Not a `False` by itself — truncation is applied consistently, and reaching it needs a structure with 2^32 fields. | OPEN, `P-medium`, filed 2026-03-01 (Opus 4.6). [#13602](https://github.com/leanprover/lean4/issues/13602) is the same defect reported as an accepted theorem; closed as a duplicate. | **artifact** — [`Lean/ProjIndexTruncation.lean`](KernelSoundness/Lean/ProjIndexTruncation.lean). **Verified here** present on `v4.32.0`, `v4.32.2`, `v4.33.0-rc1`; control (small out-of-range index) rejected on all three. |
| [#12747](https://github.com/leanprover/lean4/issues/12747) | `Level.normalize` does not canonicalize when an `imax` collapses to a `max`: outer `succ`s are not distributed, and the C++ kernel does not re-sort/flatten. `Level.isEquiv` and the kernel's `is_equivalent` therefore return `false` for denotationally equal universe levels. **Incompleteness, not unsoundness** — valid statements are rejected. | OPEN, `P-low`, filed 2026-03-01 (Opus 4.6). | **noted** + related artifact. **Verified here** on `v4.32.0`: `example (A : Sort u) (B : Sort v) (C : Sort w) : Sort (imax v (imax u w)) := A → B → C` is rejected with `Sort (imax u v w)` vs `Sort (imax v u w)`. This is very likely the same phenomenon our [`Fuzz/LevelFuzzer.lean`](KernelSoundness/Fuzz/LevelFuzzer.lean) independently counted as **162 incompleteness cases / 0 unsound** — a pairing worth confirming case-by-case (**gap**). |

### 1.3 Out-of-scope by upstream policy

| Issue | Substance | Resolution |
| --- | --- | --- |
| [#13626](https://github.com/leanprover/lean4/issues/13626) | A `prelude` module defining its own `Bool` (with `true` at constructor index 0) plus the free name `Lean.reduceBool` gets the kernel to accept `Eq (Lean.reduceBool t) Bool.false`. This is exactly the mechanism of our `ReduceBoolFreeName.lean`, independently reported 2026-05-03. | Closed 2026-05-04 as **COMPLETED / working-as-intended**: *"The kernel assumes that the official prelude is used. If you use `prelude` you are responsible for making sure it matches the kernel's expectations, i.e. It is not supported to write arbitrary code after `prelude`."* |

This is the **authoritative upstream position on the entire accelerator family**
documented in [`KernelSoundness/`](KernelSoundness/) — the `Nat` accelerators,
the free-name variants, `Lean.reduceBool`, and `StringLitFabrication`. Every one
of those exhibits is a `prelude` module (including `NatGcdFreeName.lean`, which
redefines nothing but is still `prelude` + `import Init.Prelude`), so the policy
covers them. It supersedes the Manifold-comment citation those files were
written against, and it means the family is **not** going to be fixed.

### 1.4 Hardening fixes (defensive, no published derivation of `False`)

Closed 2026-05-03/04 after an audit sweep; recorded for completeness. Coverage:
**noted** for all.

| Issue | Substance |
| --- | --- |
| [#13615](https://github.com/leanprover/lean4/issues/13615) | `.olean` files lack integrity checks and bypass kernel type checking on import. |
| [#13616](https://github.com/leanprover/lean4/issues/13616) | `declaration.h` getters call `get_small_value()` without an `is_small()` guard (13 sites). |
| [#13617](https://github.com/leanprover/lean4/issues/13617) | `compacted_region::read()` deserialization has memory-corruption vectors in release builds. |
| [#13618](https://github.com/leanprover/lean4/issues/13618) | `nparams + idx` unsigned wraparound in `reduce_proj_core`. Closed as duplicate (of the #12746 family). |
| [#13620](https://github.com/leanprover/lean4/issues/13620) | `cheap_beta_reduce` unsigned underflow when `bvar_idx >= i` in release builds. |

### 1.5 Findings originating in this repository

| Finding | Nature | Coverage |
| --- | --- | --- |
| `Nat` accelerator family (`Nat.add`, `Nat.beq`, and the nine free names under `Init.Prelude`) | Kernel normalizer extensions keyed on *names only*, tried before delta-reduction; two disagreeing reduction rules give `False`. | **artifact** + **report** — [`Reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md`](Reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md). Out of scope upstream per §1.3. |
| `StringLitFabrication` | Expanding a *string literal* makes the kernel assemble a term by name and hand it to a recursor rule **without type-checking it**, fabricating an inhabitant of `Empty`. Most severe failure mode of the family. | **artifact**. Out of scope upstream per §1.3. |
| Comparator `accepted/` | [`leanprover/comparator`](https://github.com/leanprover/comparator) checks only that challenge and solution *agree* on kernel primitives, never that the primitives are genuine; a challenge that does not import `Init` gets no protection. Comparator's own suite contains the class of construction (`tests/projects/primitive_issue`). | **artifact** — [`Comparator/`](KernelSoundness/Comparator/) |
| Def-eq history dependence | `equiv_manager`'s union-find turns the non-transitive def-eq relation into its transitive closure, consulted whenever two expressions share a 32-bit `Expr.hash`. Acceptance of `X =?= Z` depends on unrelated earlier checks in the same declaration. **Not unsoundness** — every link is individually valid. | **artifact** + **report** — [`Reports/2026-07-29-defeq-history-dependence.md`](Reports/2026-07-29-defeq-history-dependence.md) |

### 1.6 Historical defects, fixed before 2026

Recorded because both are direct ancestors of exhibits in this directory.
Coverage: **noted** for both.

| Defect | Substance | Fix |
| --- | --- | --- |
| **`reduceBool` / `native_decide` leakage** (2023) | `Lean.reduceBool` runs compiled code, and compiled code could be nondeterministic: a definition calling `IO.getRandomBytes` gave `rfl` proofs of both `Lean.reduceBool foo = false` and `Lean.reduceBool foo = true`, combined by `nomatch` into `False`. `#print axioms` reported no axioms. The root cause was that `IO.RealWorld` was not opaque, so several "real worlds" could coexist. Demonstrated by Mario Carneiro; discussed in the Lean Zulip topic *soundness bug: native_decide leakage*. | [PR #2654](https://github.com/leanprover/lean4/pull/2654), in `v4.2.0-rc2`: `reduceBool`/`reduceNat` now depend on an explicit `trustCompiler` axiom, and `IO.RealWorld` was made opaque. `lean4checker` never accepted these proofs, having no compiled-code support. |
| **`Expr.Data` / `Level.Data` overflow** (2025) | `Expr` and `Level` pack aggregate data (loose-bvar bound, depth) into a fixed-size computed field. Overflow was handled with `assert!`/`panic!`, which do **not** abort — execution continued with the field's default `0`, so `hasFVar`, `hasMVar`, `hasLevelParam`, and `hasLooseBVars` all silently returned `false` for terms that did have them, i.e. they stopped being conservative. Reported by Mario Carneiro. | [PR #8559](https://github.com/leanprover/lean4/pull/8559) and [PR #8560](https://github.com/leanprover/lean4/pull/8560), both merged 2025-05-31. ([PR #8554](https://github.com/leanprover/lean4/pull/8554) was the original, closed in favour of those two.) |

Both have present-day descendants worth noting:

* Our [`ReduceBoolFreeName.lean`](KernelSoundness/Lean/ReduceBoolFreeName.lean)
  shows the 2023 axiom-tracking hole **reappearing** when the *name*
  `Lean.reduceBool` is free: the `trustCompiler` dependency is attached to
  core's declaration, not enforced by the kernel's hook, so a module that
  defines the name itself gets the native hook with no axiom recorded.
* The 2025 `hasFVar`-non-conservativity defect is the same *kind* of failure as
  [#14484](https://github.com/leanprover/lean4/issues/14484) (§1.1), where the
  checked `opaqueDecl` path simply never asked whether the body had free
  variables.

### 1.7 Paradoxes (negative results about type theory, not Lean defects)

Girard/Hurkens and Coquand–Paulin, stated as implications from an ingredient
Lean withholds. **artifact** — [`Hurkens/`](Hurkens/) and
[`KernelSoundness/Mathematical/`](KernelSoundness/Mathematical/).

---

## 2. Lean — non-official kernels

Both were found by the same AI-driven search and landed as regression tests in
the Lean FRO's kernel arena. Coverage: **gap** for both; neither is reproduced
here.

| Kernel | Result | Reference |
| --- | --- | --- |
| `nanoda` | 2 proofs of `False` | [lean-kernel-arena PR #16](https://github.com/leanprover/lean-kernel-arena/pull/16), merged 2026-03-04 |
| `lean4lean` | 1 proof of `False`, via level normalization | [lean-kernel-arena PR #17](https://github.com/leanprover/lean-kernel-arena/pull/17), merged 2026-03-04 |

The `lean4lean` derivation being a *level normalization* bug is notable next to
§1.2's #12747: the same area of the theory is an incompleteness in the official
kernel and a soundness hole in an independent implementation.

---

## 3. Rocq / Coq

Coq has historically seen roughly one soundness bug per year; the 2026 AI sweep
found seven at once. Coverage lives in [`Coq/`](Coq/) and is verified on
**Rocq 9.2** by [`Coq/verify.ps1`](Coq/verify.ps1); the four exhibits present
are all **fixed upstream**, so each is a *regression witness* — it must be
rejected, and acceptance would signal a regression.

### 3.1 Proofs of `False` (all CLOSED / fixed)

| Issue | Defect | Coverage |
| --- | --- | --- |
| [#21682](https://github.com/rocq-prover/rocq/issues/21682) | Guard checker: cross-calls in nested mutual fixpoints. `find_uniform_parameters` inspected only self-calls, so a parameter growing through a cross-call was misclassified as uniform. | **artifact** — [`Coq/GuardChecker/NestedMutualCrossCall.v`](Coq/GuardChecker/NestedMutualCrossCall.v); rejected on Rocq 9.2 with the exact message the upstream patch predicted |
| [#21683](https://github.com/rocq-prover/rocq/issues/21683) | Guard checker: a fixpoint passes itself as a higher-order argument to another fixpoint, which applies it to a non-subterm. Makes `russell 1` convertible with its own negation. | **artifact** — [`Coq/GuardChecker/HigherOrderFixpoint.v`](Coq/GuardChecker/HigherOrderFixpoint.v); rejected on Rocq 9.2 |
| [#21685](https://github.com/rocq-prover/rocq/issues/21685) | `Module Alias := M` reached through a multi-step alias chain corrupts the delta-resolver, identifying two different functor instantiations. | **artifact** — [`Coq/ModuleSystem/AliasChainDeltaResolver.v`](Coq/ModuleSystem/AliasChainDeltaResolver.v); rejected on Rocq 9.2 (`Unable to unify`) |
| [#21701](https://github.com/rocq-prover/rocq/issues/21701) | Guard checker: recursive calls appearing without arguments (`let`-bound aliases) were ignored when computing uniform arguments. | **artifact** — [`Coq/GuardChecker/UniformArgsLet.v`](Coq/GuardChecker/UniformArgsLet.v); rejected on Rocq 9.2 |
| [#21690](https://github.com/rocq-prover/rocq/issues/21690) | Missing stack conversion for `caseinvert`. | **gap** |
| [#21694](https://github.com/rocq-prover/rocq/issues/21694) | Incorrect discharge of squashing info. | **gap** |
| [#21702](https://github.com/rocq-prover/rocq/issues/21702) | Incorrect `with Definition` universe-constraint handling. | **gap** |
| [#21736](https://github.com/rocq-prover/rocq/issues/21736) | Universe polymorphism + VM/native compilation + `Register Inline`. *(Not in the blog's list; found in this survey.)* | **gap** |

Concentration is informative: **three of eight are guard-checker bugs and three
are module-system bugs**, matching the blog's description of "relatively
orthogonal soundness bugs (mainly in the guard checker and module system)".
Lean has neither a guard checker (it compiles recursion to recursors) nor Coq's
module system, which is a structural rather than accidental difference —
discussed further in [`Coq/README.md`](Coq/README.md). All three guard-checker
bugs turn out to be failures of the *same* analysis (uniform arguments for
nested mutual fixpoints) reached three different ways, which is why they are
grouped in one directory.

### 3.2 Related non-`False` bugs from the same sweep (CLOSED)

| Issue | Defect |
| --- | --- |
| [#21691](https://github.com/rocq-prover/rocq/issues/21691) | Missing substitution for binder relevance in `lazy`. |
| [#21692](https://github.com/rocq-prover/rocq/issues/21692) | Missing substitution for array instance in `lazy`. |
| [#21693](https://github.com/rocq-prover/rocq/issues/21693) | Incorrect module substitution of retroknowledge. |

### 3.3 Further soundness-relevant issues found in this survey

| Issue | State | Defect |
| --- | --- | --- |
| [#21733](https://github.com/rocq-prover/rocq/issues/21733) | **OPEN** | `imitate` (evar instantiation) is unsound in the presence of subtyping. |
| [#22024](https://github.com/rocq-prover/rocq/issues/22024) | **OPEN** | Guard is inconsistent with univalence: fixpoints can alter rtrees and aren't rechecked. |
| [#22110](https://github.com/rocq-prover/rocq/issues/22110) | **OPEN** | Pattern-matching emulation for primitive records weakens typability. |
| [#21497](https://github.com/rocq-prover/rocq/issues/21497) | **OPEN** | Wrong computation of non-uniform parameters breaks generation of nested eliminators. |
| [#21750](https://github.com/rocq-prover/rocq/issues/21750) | closed | Modules forget elimination constraints. |
| [#21751](https://github.com/rocq-prover/rocq/issues/21751) | closed | Engine unifies global (rigid) sorts. |
| [#21839](https://github.com/rocq-prover/rocq/issues/21839) | closed | Incorrect environment passed to reduction during guard checking. |

This section is a *search result, not an audit*: it is what a keyword sweep of
the 2026 tracker surfaced, and is certainly incomplete. Rocq's historical
soundness record (pre-2026) is not covered at all.

---

## 4. Outstanding work

1. **Remaining Coq artifacts.** Four of §3.1's eight proofs of `False` are
   covered ([`Coq/`](Coq/)); #21690, #21694, #21702, and #21736 are still
   `gap`, as is all of §3.2 and §3.3 — including the four *open* issues in
   §3.3, which are the only live Coq soundness items known here.
2. **Pair #12747 with `LevelFuzzer`.** Confirm case-by-case that the fuzzer's
   162 incompleteness cases are instances of the `imax`-to-`max` normalization
   defect, or isolate any that are not.
3. **Non-official Lean kernels.** Reproduce the `nanoda` and `lean4lean`
   derivations (§2) against the vendored arena tests.
4. **Pre-2026 history.** Two Lean items are now recorded (§1.6); Coq's earlier
   yearly incidents are still absent, as is anything before 2023 on the Lean
   side.
5. **Re-survey cadence.** Both trackers move. This file records its survey date;
   anything added later should update it.

---

## 5. Sources, and how the 2026 wave unfolded

The 2026 cluster came from deliberately pointing a strong model at kernel
internals, so the primary sources are as much narrative as tracker entries.

| Source | What it contributes |
| --- | --- |
| Tristan Stérin, [*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood) | The search itself: Opus 4.6 run against both kernels with expert pointers, producing 7 proofs of `False` in Coq plus 3 further bugs, 0 in the official Lean kernel with 4 other bugs, and proofs of `False` in the non-official `nanoda` (2) and `lean4lean` (1). Origin of §1.2, §2, §3.1, §3.2. |
| Leonardo de Moura, [*Who Watches the Provers?*](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) (2026-03-16) | The Lean FRO's position: multiple independent kernels are the defence, and a bug that one kernel accepts and another rejects is the design working. Cites a 2022 arithmetic defect the official kernel accepted and `nanoda` rejected, fixed within a day. |
| Lawrence Paulson, [*Broken proofs and broken provers*](https://lawrencecpaulson.github.io/2026/01/15/Broken_proofs.html) (2026-01-15) | Longer view from outside both systems: Isabelle/HOL (2025 normalisation-by-evaluation, 2015 and 2005 overloaded-definition defects), HOL88, LCF, PVS. Argues the practical impact of soundness bugs has been small and that inadequate *models* matter more than unsound *kernels*. Out of this catalog's Lean/Coq scope, but the right context for it. |
| Lean Zulip, *soundness bug: native_decide leakage* | The 2023 defect in §1.6. |

**One timeline point is worth stating plainly.** De Moura's March 2026 post
observes that Opus 4.6 "did not manage to find a proof of false in the Lean
official kernel", in contrast to seven in Coq — a fair summary of the evidence
then available, and consistent with the blog. Four months later, in July 2026,
**two** axiom-free proofs of `False` in the official Lean kernel were reported
and fixed within hours each ([#14484](https://github.com/leanprover/lean4/issues/14484),
[#14576](https://github.com/leanprover/lean4/issues/14576), §1.1) — the second
found while reviewing an AI-assisted Collatz proof, i.e. as a side effect of
the same wave of activity rather than a targeted kernel search.

The reasonable conclusion is not that one system is sounder than the other.
It is that both trackers now move faster than any static catalog, which is why
this file carries a survey date and §4 ends with a re-survey item.
