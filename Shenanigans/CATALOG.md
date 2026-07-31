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

Last survey: **2026-07-30** (Lean tracker, Rocq tracker, and Tristan Stérin's
[*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood),
which reports a systematic AI-driven search for proofs of `False` in both
systems).

---

## 1. Lean 4 — official kernel

### 1.1 Defects that yield an axiom-free `False`

| Issue | Defect | Status upstream | Coverage |
| --- | --- | --- | --- |
| [#14484](https://github.com/leanprover/lean4/issues/14484) | The checked path for `Declaration.opaqueDecl` does not reject free variables in the body. With the inference cache, a safe metaprogram adds an opaque constant of type `False` whose value is an unbound `fvar`. `#print axioms` reports nothing; `leanchecker --fresh` replays it. | Fixed by PR #14498, merged 2026-07-22; shipped in `v4.32.2`. | **report** — [`Reports/2026-07-29-lean-4.33-backport-gap.md`](Reports/2026-07-29-lean-4.33-backport-gap.md) |
| [#14576](https://github.com/leanprover/lean4/issues/14576) | In `elim_nested_inductive_fn`, nested-inductive parametric arguments are substituted by `instantiate_pi_params` **without being type-checked**; they never appear in the auxiliary declaration, so they escape all kernel checking. A wrong-structure projection is smuggled in, hidden behind a deliberate `Expr.hash` + `approxDepth` collision. Found while reviewing a claimed 300-line Collatz proof. | Fixed by PR #14577, merged 2026-07-28; shipped in `v4.32.2`. | **report** — same file |

The report's own finding: **`v4.33.0-rc1` predates both fixes and accepts both
proofs of `False`**, because the 4.33 branch was cut before either landed and
neither was cherry-picked.

### 1.2 Live defects (not fixed as of the survey)

| Issue | Defect | Status | Coverage |
| --- | --- | --- | --- |
| [#12746](https://github.com/leanprover/lean4/issues/12746) | `Expr.proj` indices are narrowed from `size_t` to C++ `unsigned` in `infer_proj`, `reduce_proj`, and `lazy_delta_proj_reduction`, guarded only by `is_small()` (`< 2^63`, not `< 2^32`). Index `2^32 + k` silently becomes `k`, so the kernel infers, reduces, and **accepts** projections that are out of range for the structure. Not a `False` by itself — truncation is applied consistently, and exploiting it needs a structure with 2^32 fields. | OPEN, `P-medium`, filed 2026-03-01 (Opus 4.6). [#13602](https://github.com/leanprover/lean4/issues/13602) is the same defect reported as an accepted theorem; closed as a duplicate. | **artifact** — [`Lean/ProjIndexTruncation.lean`](KernelSoundness/Lean/ProjIndexTruncation.lean). **Verified here** present on `v4.32.0`, `v4.32.2`, `v4.33.0-rc1`; control (small out-of-range index) rejected on all three. |
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

### 1.4 Hardening fixes (defensive, no known exploit published)

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
| `StringLitFabrication` | Expanding a *string literal* makes the kernel assemble a term by name and hand it to a recursor rule **without type-checking it**, fabricating an inhabitant of `Empty`. Worst failure mode of the family. | **artifact**. Out of scope upstream per §1.3. |
| Comparator `evade/` | [`leanprover/comparator`](https://github.com/leanprover/comparator) checks only that challenge and solution *agree* on kernel primitives, never that the primitives are genuine; a challenge that does not import `Init` gets no protection. Comparator's own suite contains the attack class (`tests/projects/primitive_issue`). | **artifact** — [`Comparator/`](KernelSoundness/Comparator/) |
| Def-eq history dependence | `equiv_manager`'s union-find turns the non-transitive def-eq relation into its transitive closure, consulted whenever two expressions share a 32-bit `Expr.hash`. Acceptance of `X =?= Z` depends on unrelated earlier checks in the same declaration. **Not unsoundness** — every link is individually valid. | **artifact** + **report** — [`Reports/2026-07-29-defeq-history-dependence.md`](Reports/2026-07-29-defeq-history-dependence.md) |

### 1.6 Paradoxes (negative results about type theory, not Lean defects)

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

The `lean4lean` exploit being a *level normalization* bug is notable next to
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
   exploits (§2) against the vendored arena tests.
4. **Pre-2026 history.** Neither system's earlier soundness record is
   represented. Lean 4's fixed kernel bugs and Rocq's yearly incidents are both
   in scope for the stated goal.
5. **Re-survey cadence.** Both trackers move. This file records its survey date;
   anything added later should update it.
