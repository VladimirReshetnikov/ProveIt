# Catalog: every known way to prove `False` in Lean 4 and Rocq/Coq

The completeness ledger for [`README.md`](README.md)'s claim that this directory
represents every currently known route to `theorem Paradox : False` in both
systems. §1 is the taxonomy and is meant to be exhaustive by *mechanism*. §§2–4
are the defect ledgers and are exhaustive only as far as the sources in §6 go.

**How to read the coverage column.**

| Mark | Meaning |
| --- | --- |
| **artifact** | A machine-checked exhibit lives here, with a control and a pinned-toolchain matrix. |
| **report** | A written analysis lives in [`Reports/`](Reports/), pinned to toolchain versions. |
| **noted** | Recorded here only: understood and cited, no local artifact. |
| **gap** | Not represented. Candidate work. |

**Verification status is stated separately from coverage.** "Verified here" means
it was reproduced on this machine with an explicitly pinned toolchain during the
survey dated below. Everything else is recorded from an upstream source and is
*not* independently confirmed — say so when citing it.

Last survey: **2026-07-31**, against the Lean and Rocq trackers, the
[Lean Kernel Arena](https://arena.lean-lang.org/), Rocq's own
[`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md),
Lean's release-note corpus, `lean4lean`'s `bugs-found.md` and `divergences.md`,
and the blog posts in §6. Local exhibits verified on Lean `4.32.0` and Rocq `9.2`.

---

## 1. The taxonomy: every mechanism, both systems

This is the part that is meant to be complete. A route that is not here is
either unknown to the survey or a special case of one of these.

### 1.1 Assume what the theory withholds — [`Paradoxes/`](Paradoxes/)

The `False` is conditional; the hypothesis is in the statement; the audit is
clean. These are permanent facts about type theory.

| Mechanism | Lean | Rocq | Coverage |
| --- | --- | --- | --- |
| `Type : Type` / a second impredicative sort (Girard 1972, Hurkens 1995) | not expressible as a flag; hypothesised as `pi`/`lam`/`app`/`beta` | stdlib `Hurkens.Generic`, `TypeNeqSmallType`, `PropNeqType` | **artifact** — [`Paradoxes/Lean/…/Girard.lean`](Paradoxes/Lean/TypeTheoryParadoxes/Girard.lean), [`Paradoxes/Coq/Hurkens.v`](Paradoxes/Coq/Hurkens.v) |
| Tarski-style internal universe (`El`/`code` with a section) | `no_internal_universe` | `NoRetractToImpredicativeUniverse` | **artifact** — same files |
| Retract of a large universe into a small one (the general pattern) | — | `NoRetractFromTypeToProp`, `NoRetractFromSmallPropositionToProp`, `NoRetractToModalProposition`, `NoRetractToNegativeProp` | **artifact** (two of six) + **noted** |
| Non-strict positivity (Coquand–Paulin 1990) | `coquand_paulin` | same statement | **artifact** — [`CoquandPaulin.lean`](Paradoxes/Lean/TypeTheoryParadoxes/CoquandPaulin.lean) |
| Negative occurrence (Curry) | kernel refuses; `#guard_msgs`-checked | reachable via a flag, see §1.2 | **artifact** — [`Blockers.lean`](Paradoxes/Lean/TypeTheoryParadoxes/Blockers.lean) §5 |
| Powerset retract (Cantor) | `no_powerset_retract` | `Reynolds.v` in `rocq-archive/paradoxes` | **artifact** (Lean); **noted** (Rocq) |
| Data-carrying elimination out of a proof-relevant `Prop` | `no_large_elim_of_or`, `no_witness_extraction` | refman's `exProp` / `Squash` examples | **artifact** — [`LargeElimination.lean`](Paradoxes/Lean/TypeTheoryParadoxes/LargeElimination.lean) |
| Reynolds 1984 (no set-theoretic model of System F) | not statable — `Type u` is predicative | `Reynolds.v`, refuting `Iinject : Prop → Heyt` | **gap** |
| Burali-Forti (ordinal of ordinals) | Mathlib `ZFSet.isOrdinal_notMem_univ` | `BuraliForti.v` | **gap** |
| Berardi (EM ⟹ proof irrelevance) | harmless; Lean has definitional PI | stdlib `Berardi` — note its only hypothesis is **excluded middle**, not prop-ext | **noted** |
| Diaconescu (choice ⟹ EM) | `Classical.em` in core — a *derivation*, not a paradox | stdlib `Diaconescu` | **noted** |
| Univalence + UIP / Streicher K / `eq_rect_eq` / `JMeq_eq` | inconsistent: `Eq` is a singleton-eliminating `Prop`, so Lean has K outright | inconsistent for the *global* axiom; UIP on a decidable type is a theorem (Hedberg, `Eqdep_dec`) | **gap** |
| Univalence + unrestricted `LEM∞ := ∀ A, A + ¬A` | — | inconsistent (HoTT book Cor. 3.2.7); LEM for h-props is *consistent* | **gap** |
| Chicli–Pottier–Simpson (proof-relevant quotients + impredicativity) | blocked: `Quot` at `u = 0` is a subsingleton | reachable, see §1.2 | **artifact** (Rocq) |

### 1.2 Use a sanctioned escape hatch — [`EscapeHatches/`](EscapeHatches/)

The `False` is closed, but something discloses the cost.

| Mechanism | System | What the audit says | Coverage |
| --- | --- | --- | --- |
| `sorry` — explicit | Lean | `sorryAx` | **artifact** — [`Sorry.lean`](EscapeHatches/Lean/Sorry.lean) §1 |
| `sorry` — **synthetic**, from a failed tactic or a type error | Lean | `sorryAx`; the declaration still enters the environment | **artifact** — same file §2 |
| `axiom` | Lean | the axiom, by name | **artifact** — [`Axioms.lean`](EscapeHatches/Lean/Axioms.lean) |
| `Admitted` / `Axiom` / `Parameter` / `Hypothesis` / `Conjecture` | Rocq | the assumption, by name. Trap: an `Axiom` inside a `Section` is **not** discharged at `End`, unlike `Variable` | **artifact** — [`Assumptions.v`](EscapeHatches/Coq/Assumptions.v) |
| `Program` + `Admit Obligations` | Rocq | `<name>_obligation_N` | **artifact** — same file |
| `unsafe def f : False := f` | Lean | **blocked by the kernel** at the use site: `(kernel) invalid declaration, it uses unsafe declaration` | **artifact** — [`Unsafe.lean`](EscapeHatches/Lean/Unsafe.lean) §1 |
| `partial def` | Lean | **blocked**: needs `Inhabited`/`Nonempty` of the return type. With a bogus `Nonempty False` axiom it works, and the axiom is reported | **artifact** — same file §2 |
| `unsafeCast` / `lcProof` / `lcCast` / `lcUnreachable` | Lean | `lcProof` is literally `unsafe axiom {α : Prop} : α`. `#print axioms` on an `unsafe` definition using `unsafeCast` reports `[lcProof]`; the kernel gate stops it reaching a theorem | **noted** |
| `@[implemented_by]` + `native_decide` | Lean | a fresh per-use axiom `<thm>._native.native_decide.ax_N_M` (since `v4.29.0`, [RFC #12216](https://github.com/leanprover/lean4/issues/12216)) | **artifact** — [`NativeDecide.lean`](EscapeHatches/Lean/NativeDecide.lean) |
| `@[extern]` + `native_decide` | Lean | same. Needs a shared library, so it is harder to exhibit in one file | **noted** |
| `@[csimp]` + `native_decide` | Lean | **under-reports**: axioms used in the `csimp` proof are not propagated ([lean4#7463](https://github.com/leanprover/lean4/issues/7463), OPEN). Worse, an *honest* `rfl` csimp lemma pointing at an `@[implemented_by]`-replaced constant gives `False` with no extra axiom at all | **noted** |
| `set_option debug.skipKernelTC true` + hand-built `addDecl` | Lean | **nothing** — the only Lean route invisible to `#print axioms`. `leanchecker` rejects it | **artifact** — [`Metaprogramming.lean`](EscapeHatches/Lean/Metaprogramming.lean), and used as the control in [`KernelDefects/Lean/Controls/`](KernelDefects/Lean/Controls/) |
| `Unset Guard Checking` / `#[bypass_check(guard)]` | Rocq | `loop is assumed to be guarded.` | **artifact** — [`TypingFlags.v`](EscapeHatches/Coq/TypingFlags.v) §1 |
| `Unset Positivity Checking` / `#[bypass_check(positivity)]` | Rocq | `Curry is assumed to be positive.` | **artifact** — same file §2 |
| `Unset Universe Checking` / `-type-in-type` / `#[bypass_check(universes)]` | Rocq | `… relies on an unsafe hierarchy.` plus, *while the flag is off*, `Theory: Type hierarchy is collapsed` | **artifact** — same file §3–4 |
| `Symbol` + `Rewrite Rule` | Rocq | the symbols, plus `Theory: Rewrite rules are allowed (subject reduction might be broken)`. Confluence and termination are **not checked at all** | **artifact** — [`RewriteRules.v`](EscapeHatches/Coq/RewriteRules.v) |
| `-impredicative-set` + decidability in `Set` | Rocq | `Theory: Set is impredicative`, plus `classic` and `dependent_unique_choice` | **artifact** — [`ImpredicativeSet.v`](EscapeHatches/Coq/ImpredicativeSet.v) |
| `vm_compute` / `native_compute` | Rocq | **nothing.** Both are kernel-level conversion machines, not tactics; `native_compute` puts the OCaml toolchain in the TCB. Both ignore `Opaque` | **gap** |
| `Extraction` with `Extract Constant` | Rocq | nothing; the spliced OCaml *"is currently not checked at all by extraction, even for syntax errors"* | **gap** |
| `Declare ML Module` | Rocq | nothing. Loads OCaml into the kernel's own process | **gap** |
| Tampered or stale `.vo` / `.olean` | both | nothing. Neither system re-typechecks on import | **noted** — [lean4#13615](https://github.com/leanprover/lean4/issues/13615) (closed as by-design); Rocq hardened its `coqchk` path in 8.19 |
| A statement that does not mean what it reads as | both | `Closed under the global context` / no axioms — **correctly** | **artifact** — [`Spoofing.lean`](EscapeHatches/Lean/Spoofing.lean), [`Spoofing.v`](EscapeHatches/Coq/Spoofing.v) |
| An over-general statement (`autoImplicit`, a missing side condition, an instance argument quantifying over all structures) | Lean | nothing | **artifact** — [`Axioms.lean`](EscapeHatches/Lean/Axioms.lean) §4 |

### 1.3 Exploit an implementation defect — [`KernelDefects/`](KernelDefects/)

Closed `False`, clean audit, no flag. Ledgers in §§2–4.

### 1.4 Things commonly believed to be routes, and are not

Worth recording so they are not chased again.

| Claim | Reality |
| --- | --- |
| `Quot.sound` on a non-equivalence relation is unsound | No. `Quot.lift f h` demands `h : ∀ a b, r a b → f a = f b`, and `=` is an equivalence, so anything liftable already respects the equivalence closure of `r`. Carneiro's model interprets `Quot r` as classes of that closure. |
| `partial def` alone gives `False` | No. The `Inhabited` obligation is real and is recorded in the opaque's *value*, so `#print axioms` reports it. |
| `noncomputable` is a soundness device | No. It is a code-generation annotation. |
| `Ltac`/`Ltac2` can produce an ill-typed term | No — `Qed` re-checks the whole term. Even `exact_no_check` and `change_no_check` are caught. |
| `Print Assumptions` is unreliable | Mostly false, and better than its reputation: it reports every `bypass_check` flag by name. Its real blind spots are ML plugins, extraction, `vm_compute`/`native_compute`, notation, and `.vo` provenance — plus two open functor bugs, [#12155](https://github.com/rocq-prover/rocq/issues/12155) and [#16646](https://github.com/rocq-prover/rocq/issues/16646). |
| A sort disagreeing with a reference sort is a library bug | Not necessarily — and this bit during the sweep above. `Array.qsort` takes a **strict** `lt`; passing `≤` violates its precondition and silently yields unsorted output that looks exactly like a defect. `List.mergeSort` takes a non-strict `le`. Using each function's `autoParam` default avoids the trap. No proof depends on the output, so this is a correctness hazard for programs, not a soundness one. |
| Berardi assumes propositional extensionality | No — its only hypothesis is excluded middle. The prop-ext ⟹ proof-irrelevance result is `ClassicalFacts.ext_prop_dep_proof_irrel_cic`. |
| `JMeq_eq` is axiom-free in modern Rocq | No. It is a `Theorem` now, but the file still `Require`s `Eqdep`, so `Print Assumptions` reports `Eqdep.eq_rect_eq`. |
| Univalence rejects classical logic | Only *unrestricted* classical logic. LEM for mere propositions is consistent with univalence (simplicial model). |

---

## 2. Lean 4 — official kernel

Lean 3's record for contrast: *"for the entire release history of Lean 3, there
were no soundness bugs reported against the kernel"*
([Lean4Lean paper](https://arxiv.org/abs/2403.14064)). Lean 4's bugs come almost
entirely from the three kernel *extensions* Lean 3's FAQ told you to disable with
`-t0` — GMP `Nat` arithmetic, structure eta, nested inductives — plus C++
fixed-width integer fields.

### 2.1 Live defects (not fixed as of the survey)

| Issue | Defect | Coverage |
| --- | --- | --- |
| [#14582](https://github.com/leanprover/lean4/pull/14582) | **The live one.** Follow-up to #14577 by Arthur Adjedj: a datatype being declared can occur applied to arguments that are *not* the parameters of the mutual declaration, hidden in the parametric arguments of a nested inductive, which are dropped from the generated auxiliary declaration and so escape type checking. Adds `check_uniform_params`. **OPEN as of 2026-07-31.** | **gap** |
| [#12746](https://github.com/leanprover/lean4/issues/12746) | `Expr.proj` indices narrowed `size_t`→C++ `unsigned` in `infer_proj`, `reduce_proj`, `lazy_delta_proj_reduction`, guarded only by `is_small()` (`< 2^63`, not `< 2^32`). Index `2^32 + k` silently becomes `k`. Not a `False` by itself — truncation is consistent, and a collision needs a structure with 2^32 fields. [#13602](https://github.com/leanprover/lean4/issues/13602) is the same defect reported *with* an axiom-free accepted theorem, closed as a duplicate. OPEN, `P-medium`. | **artifact** — [`Projections/ProjIndexTruncation.lean`](KernelDefects/Lean/Projections/ProjIndexTruncation.lean). **Verified here** present on `v4.32.0`, `v4.32.2`, `v4.33.0-rc1`; control rejected on all three. |
| [#12747](https://github.com/leanprover/lean4/issues/12747) | `Level.normalize` does not canonicalize when an `imax` collapses to a `max`. **Incompleteness, not unsoundness.** OPEN, `P-low`. | **artifact** (as incompleteness) — [`DefEq/LevelNormalizeIncomplete.lean`](KernelDefects/Lean/DefEq/LevelNormalizeIncomplete.lean). **Verified here** on `v4.32.0`. |
| [#7637](https://github.com/leanprover/lean4/issues/7637) | Primitive projections are not conservative over recursors. OPEN. | **artifact** — [`Audits/Lean/Metatheory/ProjBeyondRecursor.lean`](Audits/Lean/Metatheory/ProjBeyondRecursor.lean), which reaches the same conclusion independently |
| [#8982](https://github.com/leanprover/lean4/issues/8982) | An unsound `unif_hint` makes everything defeq and crashes Lean. Elaborator-level. OPEN; fix PR #8988 unmerged. | **gap** |
| [#7463](https://github.com/leanprover/lean4/issues/7463) | `@[csimp]` does not propagate axioms used in its proof through `native_decide`. OPEN, `P-low`. | **noted** — §1.2 |
| [#10760](https://github.com/leanprover/lean4/issues/10760) | Visibility of section variables not verified correctly under the module system. OPEN. | **gap** |

### 2.2 Fixed defects that yielded an axiom-free `False`

Chronological. Every one of these was accepted by the *checked* kernel.

| Issue / PR | Defect | Fixed |
| --- | --- | --- |
| [#1433](https://github.com/leanprover/lean4/issues/1433) | `lean_nat_mod` truncates `size_t`→`unsigned`, so `2^65 % (2^33+1)` reduces to `1`. **Proof of `False` by plain `rfl`** — no metaprogramming, no `native_decide`. | same day, 2022-08-06 |
| [#1781](https://github.com/leanprover/lean4/pull/1781) | `imax u v + N` normalized to `imax u v` regardless of `N`. Title is literally *"fix: bug in level normalization (soundness bug)"*. Does not exist in Lean 3. | 2022-10-26 |
| [#2125](https://github.com/leanprover/lean4/issues/2125) | Self-referential index: `inductive C : Bool → Type | c : C (f (C false))` with `f α := Nonempty α`. **The only one exploitable from plain surface Lean.** Lean 3 had this check; Lean 4 lost it. | next day, 2023-02-28 |
| [#8060](https://github.com/leanprover/lean4/pull/8060) | `reduce_pow` interpreted an expression as an `mpz` without checking it was a `Nat` literal. Found by fuzzing with GMP and mimalloc disabled. | 2025-04-23 |
| [#8554](https://github.com/leanprover/lean4/pull/8554) family | `Expr.Data`/`Level.Data` overflow handled by `panic!`, which **does not abort** — execution continued with the field's default `0`, so `hasFVar`, `hasMVar`, `hasLevelParam`, `hasLooseBVars` all stopped being conservative. Found by Carneiro *via lean4lean*, by failing to prove a theorem and working backwards. #8554 closed unmerged; fixed by [#8559](https://github.com/leanprover/lean4/pull/8559)/[#8560](https://github.com/leanprover/lean4/pull/8560). | 2025-05-31 |
| [#14484](https://github.com/leanprover/lean4/issues/14484) | The checked `Declaration.opaqueDecl` path did not reject free variables in the body; with the inference cache, a safe metaprogram adds an opaque `False` whose value is an unbound fvar. | 2026-07-22, `v4.32.1` |
| [#14576](https://github.com/leanprover/lean4/issues/14576) | Nested-inductive parametric arguments substituted **without being type-checked**; a wrong-structure projection hidden behind a deliberate `Expr.hash` + `approxDepth` collision. Found while reviewing an AI-assisted Collatz proof. **Exploitable even through `comparator`** — the release notes say so. | 2026-07-28, `v4.32.2` |
| [#14613](https://github.com/leanprover/lean4/pull/14613) | `type_checker::is_prop` compared `whnf(infer_type(e))` against `Prop` **syntactically**. `Sort (imax 1 0)` really *is* a proposition, so proof irrelevance applies — but `is_prop` said no, and `infer_proj` skipped its `Prop` restriction, letting a `Bool` be projected out of a proof. | 2026-07-31 |
| [#14616](https://github.com/leanprover/lean4/pull/14616) | A declaration naming one of the kernel's `_nested` auxiliary types: `restore_nested` can hand a stored constructor a type in a *different universe* than it was checked against. Notable because it **cannot be captured as an arena export test** — the exploit depends on transient `equiv_manager` state. | 2026-07-31 |
| [#14607](https://github.com/leanprover/lean4/pull/14607) | Missing `check_no_metavar_no_fvar` in `inductive.cpp`: nested inductive declarations containing fvars/mvars. | 2026-07-30 |
| [#14608](https://github.com/leanprover/lean4/pull/14608) | The kernel did not check that declarations in a `mutual` block use the same universe parameters. | 2026-07-30 |
| [#14609](https://github.com/leanprover/lean4/pull/14609) | Module system: an exported definition's axiom stub computed `isUnsafe` as `defn.safety == .unsafe`, which is **false for `.partial`** — so a `partial def` crossed a module boundary as an ordinary *safe* axiom. | 2026-07-30 |

**Only two releases in Lean 4's history were cut specifically for kernel
soundness: `v4.32.1` and `v4.32.2`, eight days apart in July 2026.**

Two further kernel bugs found by lean4lean verification with no demonstrated
exploit: [#10475](https://github.com/leanprover/lean4/issues/10475) (`infer_let`
ignores dependencies in a let-binding's *type*, so `Kernel.check` returns an
expression with a loose fvar) and
[#10492](https://github.com/leanprover/lean4/issues/10492). Plus
[#10577](https://github.com/leanprover/lean4/issues/10577) (uninitialized memory
in `lazy_delta_reduction_step`, found by fuzzing) and
[#8695](https://github.com/leanprover/lean4/issues/8695) (a constructor named
`I.rec` silently **overwrites** the recursor).

### 2.3 Out-of-scope by upstream policy

| Issue | Substance | Resolution |
| --- | --- | --- |
| [#13626](https://github.com/leanprover/lean4/issues/13626) | A `prelude` module defining its own `Bool` plus the free name `Lean.reduceBool` gets the kernel to accept `Eq (Lean.reduceBool t) Bool.false`. Exactly the mechanism of our `ReduceBoolFreeName.lean`, independently reported 2026-05-03. | Closed 2026-05-04 as **working-as-intended**. |

This is the authoritative upstream position on the **entire accelerator family**
in [`KernelDefects/Lean/Accelerators/`](KernelDefects/Lean/Accelerators/) — the
`Nat` accelerators, the free-name variants, `Lean.reduceBool`, and
`StringLitFabrication`. Every one is a `prelude` module, so the policy covers
them, and the family is **not** going to be fixed. `lean4lean` documents the same
assumption from the other side in
[`divergences.md`](https://github.com/digama0/lean4lean/blob/master/divergences.md).

### 2.4 Compiler / `native_decide` trust-base defects (not kernel bugs)

Each yields `False` via `native_decide`, and each is a divergence *in Lean core*
between a reference implementation and its compiled counterpart — so the bug
does not have to be yours. Coverage: **noted** for all.

| Issue | Substance | Fixed |
| --- | --- | --- |
| [#1825](https://github.com/leanprover/lean4/issues/1825) | `mpz` integer overflows | `v4.0.0` |
| [#4306](https://github.com/leanprover/lean4/issues/4306) | `UIntN.toNat` constant folding without modular reduction | 2024-05-30 |
| [#5818](https://github.com/leanprover/lean4/issues/5818) | `UInt64.modn` miscompilation | 2024-10-23 |
| [#6086](https://github.com/leanprover/lean4/issues/6086) | `Nat.ble 0 0 = false` | same day, 2024-11-15 |
| [#10213](https://github.com/leanprover/lean4/issues/10213) | `@[csimp]` ignored universe parameters — the demo overrides `Classical.choice` | 2025-09-02 |
| [#11773](https://github.com/leanprover/lean4/issues/11773) | `Array.foldlM` vs `foldlMUnsafe` disagree on an out-of-range `stop` | 2025-12-22 |
| [#8840](https://github.com/leanprover/lean4/issues/8840) | **Trust-accounting bug**: `collectAxioms` did not collect axioms referenced by *other* axioms, so a `native_decide` proof did not report `Lean.trustCompiler`. `#print axioms` was itself under-reporting the TCB. | 2025-06-17 |

Historical, and the ancestor of the whole family: the **2023 `native_decide`
leakage**. `Lean.reduceBool` ran compiled code, and compiled code could be
nondeterministic — a definition calling `IO.getRandomBytes` gave `rfl` proofs of
both `Lean.reduceBool foo = false` and `= true`, combined by `nomatch` into
`False`, with `#print axioms` reporting **nothing**. Root cause: `IO.RealWorld`
was not opaque, so several "real worlds" could coexist. Demonstrated by Mario
Carneiro; fixed by [PR #2654](https://github.com/leanprover/lean4/pull/2654) in
`v4.2.0-rc2`. `lean4checker` never accepted these proofs, having no compiled-code
support. Coverage: **noted**; the descendant mechanism is
[`ReduceBoolFreeName.lean`](KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean).

### 2.5 Hardening fixes (defensive, no published derivation of `False`)

Closed 2026-05-03/04 after a systematic audit sweep. Coverage: **noted** for all.
The recurring theme is that `lean_assert`/`assert!`/`panic!` are debug-only or
non-aborting, so every "guarded" invariant is unguarded in a release build.

| Issue | Substance |
| --- | --- |
| [#13615](https://github.com/leanprover/lean4/issues/13615) | `.olean` files lack integrity checks and bypass kernel type checking on import |
| [#13616](https://github.com/leanprover/lean4/issues/13616) | `declaration.h` getters call `get_small_value()` without an `is_small()` guard (13 sites) |
| [#13617](https://github.com/leanprover/lean4/issues/13617) | `compacted_region::read()` deserialization memory-corruption vectors |
| [#13618](https://github.com/leanprover/lean4/issues/13618) | `nparams + idx` unsigned wraparound in `reduce_proj_core` — duplicate of the #12746 family |
| [#13619](https://github.com/leanprover/lean4/issues/13619) | integer overflow in the `.olean` deserializer's byte-size functions |
| [#13620](https://github.com/leanprover/lean4/issues/13620) | `cheap_beta_reduce` unsigned underflow when `bvar_idx >= i` |

### 2.6 Findings originating in this repository

| Finding | Nature | Coverage |
| --- | --- | --- |
| `Nat` accelerator family (`Nat.add`, `Nat.beq`, and the nine free names under `Init.Prelude`) | Kernel normalizer extensions keyed on *names only*, tried before delta-reduction; two disagreeing reduction rules give `False`. Out of scope upstream per §2.3. | **artifact** + **report** — [`Reports/2026-07-28-…`](Reports/2026-07-28-lean-kernel-nat-accelerator-unsoundness.md) |
| `StringLitFabrication` | Expanding a *string literal* makes the kernel assemble a term by name and hand it to a recursor rule **without type-checking it**, fabricating an inhabitant of `Empty`. The most severe failure mode of the family. | **artifact** |
| Comparator `accepted/` | [`leanprover/comparator`](https://github.com/leanprover/comparator) checks only that challenge and solution *agree* on kernel primitives, never that the primitives are genuine; a challenge that does not import `Init` gets no protection. | **artifact** — [`Comparator/`](KernelDefects/Lean/Comparator/) |
| Def-eq history dependence | `equiv_manager`'s union-find turns the non-transitive def-eq relation into its transitive closure, consulted whenever two expressions share a 32-bit `Expr.hash`. **Not unsoundness** — every link is individually valid. Notable in hindsight: this is exactly the mechanism #14576 and #14616 weaponise. | **artifact** + **report** — [`Reports/2026-07-29-defeq-…`](Reports/2026-07-29-defeq-history-dependence.md) |
| `Nat.shiftLeft` kernel abort | `reduce_nat` bounds `Nat.pow`'s exponent (`ReducePowMaxExp`) and declines gracefully above it, but applies no bound to `Nat.shiftLeft`; `lean_nat_shiftl` calls `lean_internal_panic` above `UINT_MAX`. `example : (1 : Nat) <<< 4294967296 = 0 := rfl` aborts `lean` (exit 1, uncatchable) on `v4.31.0` through `v4.33.0-rc1`, under `--trust=0`, from one line of ordinary source. **Robustness, not unsoundness** — the process dies rather than continuing with a wrong value. | **report** — [`Reports/2026-07-31-kernel-shiftleft-panic.md`](Reports/2026-07-31-kernel-shiftleft-panic.md); harness [`Audits/Lean/Fuzz/NatAcceleratorBoundaries.lean`](Audits/Lean/Fuzz/NatAcceleratorBoundaries.lean) |
| `v4.33.0-rc1` backport gap | The 4.33 branch was cut before #14484 and #14576 landed and neither was cherry-picked, so the release candidate accepts both proofs of `False`. | **report** — [`Reports/2026-07-29-lean-4.33-…`](Reports/2026-07-29-lean-4.33-backport-gap.md) |

---

## 3. Lean — non-official kernels and the Arena

[`leanprover/lean-kernel-arena`](https://github.com/leanprover/lean-kernel-arena)
(results at [arena.lean-lang.org](https://arena.lean-lang.org/), maintained by
Joachim Breitner) is now **the definitive catalog of kernel attacks**: a
CI-driven differential-testing harness running a standard corpus of
`lean4export` NDJSON test cases against every registered checker. This is de
Moura's *Who Watches the Provers?* argument made operational.

Coverage: **gap** for the entire section. None of these is reproduced here, and
the whole corpus is the single largest outstanding item in this catalog.

### 3.1 The attack corpus

| Test | Mechanism | Who fell for it |
| --- | --- | --- |
| `level-imax-leq` | `leq(imax(u,v)+1, imax(u,v))` accepted when the successor offset is ignored → a universe-collapsing `down` → cast `True`↔`False` | **nanoda** |
| `nat-rec-rules` | The checker compared imported recursor rules **against themselves** (`rec_rules.iter().zip(rec_rules.iter())`) instead of independently reconstructed ones | **nanoda** |
| `level-imax-normalization` | The normalizer drops the accumulated offset when decomposing `imax u (param v)`, so `imax 0 v ≡ succ (imax 0 v)` | **lean4lean** |
| `proj-of-prop` | Typing a projection by *inferring* rather than *checking* its structure argument | **nanoda** |
| `proj-of-imax-prop` | §2.2 / #14613 | **the official kernel** |
| `nested-unused-param` | §2.2 / #14576 | **the official kernel** |
| `nested-aux-name` | §2.2 / #14616 | **the official kernel** |
| `constlevels` | §2.2 / #10577 | **the official kernel** (4.28/4.29 segfault) |
| `large-elim-param` | If "is this level surely nonzero?" wrongly returns true for a *param*, `inductive MyBool.{u} : Sort u | tt | ff` gets a recursor that large-eliminates a `Prop`; proof irrelevance gives `tt = ff` | found by Anthony Wang using Aristotle |
| `ctor-num-fields` | Lie about a constructor's `numFields` so a 1-field structure looks unit-like; definitional eta then equates all inhabitants | trusted-metadata class |
| `rec-k-lie`, `nat-rec-k-lie` | Lie about `k` (K-like reduction) on a recursor | trusted-metadata class |
| `proj-non-structure` | Project out of a 2-constructor type, hoping the checker infers from the *first* constructor | generic |
| `k-rec-conv` | Broken K-like reduction makes `fun x => x ≡ fun _ => y` | regression test for a **sokonanoda** bug |
| `bogus1` | `debug.skipKernelTC` calibration case | — |

Plus 43 invalid `tutorial/*` tests giving a full taxonomy of what a kernel must
reject.

### 3.2 The `undecidability/` category — not anyone's bug

These score `either` because there is no right answer, and they are the arena's
statement of a permanent gap. From Carneiro's thesis: algorithmic conversion **is
not transitive** (`alg-conv-trans-acc`, via `Acc.rec` and proof irrelevance —
the checker would have to *invent* the middle term), and **subject reduction
fails** (`subject-reduction-redex`/`-reduct` — a term the kernel accepts reduces
to one it rejects). Our independent measurements of the same phenomena are in
[`Audits/Lean/Metatheory/`](Audits/Lean/Metatheory/).

### 3.3 The implementations

`lean4lean` (Carneiro, Lean — *"derived directly from the C++ kernel, and as such
likely shares some implementation bugs with it; it's not really an independent
implementation"*), `nanoda`/`nanobruijn` (Rust), `sokonanoda`, `still-nanoda`,
`zignodamus` (Zig), `nyaya` (OCaml), `rpylean` (RPython), `mini` (deliberately
naive, invites attacks), `vow-lean-kernel`, and `evmlean` — a Lean-kernel
fragment as a **Solidity smart contract**. `lean4checker` was archived 2026-03-25
and superseded by the `leanchecker` binary shipped in the toolchain since
`v4.28.0`; note it **shares Lean's own kernel** and so is not an independent
verifier. `trepplein` (Scala, Lean 3) is abandoned but historically important:
David Renshaw's 2021 fuzzing found inputs `leanchecker` rejected and `trepplein`
accepted, which is the direct intellectual ancestor of the arena.

---

## 4. Rocq / Coq

The canonical source is Rocq's own
[`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md)
— a 1000-line maintainer-curated ledger of every soundness bug since 8.0, with
introduced/impacted/fixed versions and risk assessments. It contains several bugs
with no GitHub issue at all. The tracker label is **`kind: inconsistency`**
("Proof of False accepted by the kernel and/or checker"), not `kind: unsoundness`.
`coq/coq` and `rocq-prover/rocq` are the same repository; issue numbers are
continuous.

Coq historically saw roughly one soundness bug per year. **Rocq 9.2.0 fixed ten
`kind: inconsistency` issues in a single release** — an unprecedented count, and
the direct output of the 2026 sweep.

### 4.1 Guard checker — by far the most productive source

| Issue | Mechanism | Affected | Fixed | Coverage |
| --- | --- | --- | --- | --- |
| [#21053](https://github.com/rocq-prover/rocq/issues/21053) | Guard vs propositional extensionality / univalence: a cast was treated as a subterm | **V6.1–9.0** | 9.0.1 | **gap** |
| [#20413](https://github.com/rocq-prover/rocq/issues/20413) | Non-structural fixpoint arguments unchecked | 8.16–9.0.0 | 9.0.1 | **gap** |
| [#20455](https://github.com/rocq-prover/rocq/issues/20455) | `match` on `match` wrongly detected as returning a subterm | 8.16–9.0.0 | 9.0.1 | **gap** |
| [#20555](https://github.com/rocq-prover/rocq/issues/20555) | Incorrect reduction across an inner fixpoint | 8.16–9.0.0 | 9.0.1 | **gap** |
| [#21682](https://github.com/rocq-prover/rocq/issues/21682) | Cross-calls in nested mutual fixpoints ignored by uniform-parameter analysis | 8.20–9.1 | 9.2.0 | **artifact** — [`NestedMutualCrossCall.v`](KernelDefects/Coq/GuardChecker/NestedMutualCrossCall.v) |
| [#21683](https://github.com/rocq-prover/rocq/issues/21683) | Fixpoint passed as a higher-order argument; axiom-free Russell paradox. **A regression introduced by the fix for #20555** | 9.0.1–9.1.1 | 9.2.0 | **artifact** — [`HigherOrderFixpoint.v`](KernelDefects/Coq/GuardChecker/HigherOrderFixpoint.v) |
| [#21701](https://github.com/rocq-prover/rocq/issues/21701) | Argument-less recursive calls (`let`-bound aliases) don't restrict uniform-argument computation | 8.20–9.1 | 9.2.0 | **artifact** — [`UniformArgsLet.v`](KernelDefects/Coq/GuardChecker/UniformArgsLet.v) |
| [#21797](https://github.com/rocq-prover/rocq/issues/21797) | `find_uniform_parameters` doesn't recurse into args of non-`fix` `Rel` applications | 8.20–9.1 | 9.2.0 | **gap** |
| [#21839](https://github.com/rocq-prover/rocq/issues/21839) | Reduction performed in the wrong environment; direct `Definition oops : False` | 8.16–9.2.0 | 9.2.1 / 9.3 | **gap** |
| [#22021](https://github.com/rocq-prover/rocq/issues/22021) | Lambda domains of unapplied nested fixpoints unchecked | 8.20–9.2.0 | 9.2.1 / 9.3 | **gap** |
| [#22024](https://github.com/rocq-prover/rocq/issues/22024) | Fixpoints alter their arguments' rtrees and aren't rechecked; relative inconsistency with univalence | 9.1 | **OPEN** | **gap** |

The pattern is striking and worth stating plainly: **PR
[#17986](https://github.com/rocq-prover/rocq/pull/17986) alone introduced four
separate proofs of `False`** (#21682, #21701, #21797, #22021), PR #15434
introduced three (#20413, #20455, #20555), and the *fix* for #20555 introduced
#21683. All three of our guard-checker artifacts are failures of the *same*
analysis — uniform arguments for nested mutual fixpoints — reached three
different ways, which is why they share a directory.

### 4.2 Module system

| Issue | Mechanism | Affected | Fixed | Coverage |
| --- | --- | --- | --- | --- |
| [#15838](https://github.com/rocq-prover/rocq/issues/15838) | Module subtyping allows contravariant `Prop ⊆ Type`, disrespecting squashing → Hurkens | ~7.4–8.15.0 | 8.15.1 | **gap** |
| [#18503](https://github.com/rocq-prover/rocq/issues/18503) | `Primitive` in a Module Type bypasses subtyping conversion | 8.11.0–8.18.0 | 8.19.0 | **gap** |
| [#21051](https://github.com/rocq-prover/rocq/issues/21051) | Missing substitution when strengthening functors; `Include` corrupts the delta-resolver → `true = false` | kernel 8.5–9.0.0 | 9.0.1 | **gap** |
| [#21685](https://github.com/rocq-prover/rocq/issues/21685) | Same, for **aliased** functors: a multi-step `Module Alias := M` chain corrupts the delta-resolver | kernel 8.5–9.1 | 9.2.0 | **artifact** — [`AliasChainDeltaResolver.v`](KernelDefects/Coq/ModuleSystem/AliasChainDeltaResolver.v) |
| [#21702](https://github.com/rocq-prover/rocq/issues/21702) | `check_with_def` stored the with-body's *weaker* universes → `Type@{u} → Type@{v}` with no `u ≤ v` → Girard | 8.5–9.1 | 9.2.0 | **gap** |
| [#21750](https://github.com/rocq-prover/rocq/issues/21750) | Subtyping ignored elimination constraints → unbox a `Box@{SProp}` → `true = false` | 9.2+rc1 | 9.2.0 | **gap** |
| [#22287](https://github.com/rocq-prover/rocq/issues/22287) | `ugraph` keeps a *copy* of the universe-checking flag; `Local Unset Universe Checking` in a module leaves it desynced on close → effective type-in-type → Hurkens, reported as **"Closed under the global context"** | master | **OPEN** (2026-07-16) | **gap** |
| [#12155](https://github.com/rocq-prover/rocq/issues/12155), [#16646](https://github.com/rocq-prover/rocq/issues/16646) | `Print Assumptions` under-reports inconsistent flags through `Parameter Inline` and functor application | V8.6–now / V8.11–now | **OPEN** | **noted** — [`TypingFlags.v`](EscapeHatches/Coq/TypingFlags.v) |

### 4.3 Universes, template polymorphism, sorts

Coverage: **gap** for all.

| Issue | Mechanism | Fixed |
| --- | --- | --- |
| [#9294](https://github.com/rocq-prover/rocq/issues/9294) | Template polymorphism breaks `Prop`/`Set` separation — side constraints not collected | 8.10.0 |
| [#11039](https://github.com/rocq-prover/rocq/issues/11039) | More template-poly missing constraints (same universe in params *and* constructor args) | 8.10.2 / 8.11 |
| [#3211](https://github.com/rocq-prover/rocq/issues/3211) | De Bruijn bug computing the allowed elimination principle | 2014 |
| [#8341](https://github.com/rocq-prover/rocq/issues/8341) | Universe polymorphism can capture global universes | — |
| [#15916](https://github.com/rocq-prover/rocq/issues/15916) | Variance inference for section universes ignored use in inductives | 8.16 |
| [#21694](https://github.com/rocq-prover/rocq/issues/21694) | Incorrect discharge of squashing info for a sort-polymorphic inductive in a section | 9.2.0 |
| [#21689](https://github.com/rocq-prover/rocq/issues/21689), [#21970](https://github.com/rocq-prover/rocq/issues/21970) | Double universe substitution in letins from match indices / constructor arguments | 9.2.0 / 9.2.1 |
| — | `Prop ≤ Set` conversion bug, **found by Georgi Guninski** | 8.3 / 8.2 (2010) |

### 4.4 Conversion machines (lazy / VM / native)

Coverage: **gap** for all. The whole class has no Lean analogue, because Lean has
no VM or native conversion machine in the kernel.

| Issue | Mechanism | Fixed |
| --- | --- | --- |
| [#4157](https://github.com/rocq-prover/rocq/issues/4157) | VM constructor tag collision above 256 constructors | 8.5 |
| [#14243](https://github.com/rocq-prover/rocq/issues/14243) | native: Coq→OCaml identifier translation not bijective (`α` and `__U03b1_` collided → identified `True`/`False`) | 8.5pl2 |
| [#11043](https://github.com/rocq-prover/rocq/issues/11043) | Lazy: de Bruijn handling in lambda relevance inference (SProp) → `0 = 1` | 8.10.1 |
| [#16645](https://github.com/rocq-prover/rocq/issues/16645) | native: `Prod`/`Prod` conversion compared the **wrong components**; risk assessed "systematic" | 8.16.1 |
| [#16831](https://github.com/rocq-prover/rocq/issues/16831), [#16829](https://github.com/rocq-prover/rocq/issues/16829) | η-expansion of cofixpoints in the wrong environment; conversion compared the *mutated* primitive array | 8.16.1 |
| [#16957](https://github.com/rocq-prover/rocq/issues/16957) | Tactic code could mutate a global cache of section variables. `priority: blocker` | 8.17.0 |
| [#21690](https://github.com/rocq-prover/rocq/issues/21690) | Missing stack conversion for irrelevant-to-relevant match; with `Definitional UIP`, `0 = 1` | 9.2.0 |
| [#21736](https://github.com/rocq-prover/rocq/issues/21736) | `Register Inline` + universe polymorphism: `genlambda.ml` fails to substitute the universe instance → `vm_cast_no_check` proves `Type@{v} = Type@{u}` → Hurkens. **Affected every patch release from 8.5 to 9.1, and coqchk too** | 9.2.0 |
| [#11321](https://github.com/rocq-prover/rocq/issues/11321) | Broken long multiplication in 32-bit primint emulation, **all three machines** | 8.11.0 |
| [#12483](https://github.com/rocq-prover/rocq/issues/12483) | An **incorrect `PrimFloat.leb` axiom shipped** → `False` straight from the library. `priority: blocker` | 8.11.x |

### 4.5 Library-axiom conflicts that shipped as bugs

Coverage: **noted** for all; these are the §1.1/§1.2 items that were once
reachable without a flag.

* **Description + decidability of equality on reals vs impredicative `Set`** —
  introduced 2002-06-20, shipped in **7.3.1 and 7.4**, found by Herbelin and
  Werner, fixed 2004-10-28 **by making `Set` predicative**. This is why the flag
  exists and is off by default.
* **Guard condition vs propositional extensionality in the `Sets` library** —
  *"technically speaking from V6.1 … which was then inconsistent from the very
  beginning without we knew it"*. Fixed 2014-10-28, and a second variant survived
  to **9.0**, fixed in 9.0.1. The clearest example of an axiom that was fine and
  a kernel that had to change.
* **AC + EM vs large *singleton* elimination to `Set`** — *"not a bug but a
  change of intended model"*, impacted strictly before 8.1, fixed 2007-02-09 by
  constraining singleton elimination, found by Benjamin Werner.

### 4.6 Currently open, soundness-relevant

Coverage: **gap** for all. #22287 and #22024 are the only ones with a known route
to `False`.

[#22287](https://github.com/rocq-prover/rocq/issues/22287) (universe-flag desync
on module close) · [#22024](https://github.com/rocq-prover/rocq/issues/22024)
(guard rtree mutation) · [#16891](https://github.com/rocq-prover/rocq/issues/16891)
(VM/native memory corruption on ill-typed terms via `exact_no_check`) ·
[#13439](https://github.com/rocq-prover/rocq/issues/13439) (VM buffer overflow) ·
[#12439](https://github.com/rocq-prover/rocq/issues/12439) (coqchk under-checks
primitive declarations) · [#12155](https://github.com/rocq-prover/rocq/issues/12155)
and [#16646](https://github.com/rocq-prover/rocq/issues/16646) (`Print
Assumptions` under-reporting) · [#21113](https://github.com/rocq-prover/rocq/issues/21113)
(`Private Inductive` check too weak) · [#21494](https://github.com/rocq-prover/rocq/issues/21494)
(kernel accepts PrimRecords with indices) · [#20016](https://github.com/rocq-prover/rocq/issues/20016)
(bad case inversion with `Set Definitional UIP`).

**Corrections to the previous survey.** Three issues this catalog previously
listed as soundness-relevant are not: [#21733](https://github.com/rocq-prover/rocq/issues/21733)
(`imitate` is unsound *in elaboration*; the kernel still rejects),
[#21497](https://github.com/rocq-prover/rocq/issues/21497) (wrong non-uniform
parameter computation breaks *eliminator generation*), and
[#22110](https://github.com/rocq-prover/rocq/issues/22110) (labelled
`kind: wish`; an incompleteness).

### 4.7 `coqchk` — measured asymmetry

Worth recording because a CI script that only checks the exit code proves less
than it appears to.

| Input `.vo` | `coqchk` |
| --- | --- |
| `Admitted` + axioms | exit 0, listed under `* Axioms:` |
| `Unset Guard Checking` | **exit 0 — accepted**, merely listed |
| `Unset Positivity Checking` | **exit 0 — accepted**, merely listed |
| `Unset Universe Checking` | **rejected** |
| `-impredicative-set` | rejected unless given the same flag |
| rewrite rules | exit 0, listed |

Its own escape hatches, from `--help`: `-admit module` (*"load module and
dependencies **without checking**"*) and `-norec module`. CompCert's actual
practice is to run `coqchk` *and separately confirm* that no guard conditions
were disabled — precisely because coqchk reports rather than rejects them.

---

## 5. Outstanding work

Ordered by value.

0. **lean4#14582 needs an instrumented kernel build, and this is now demonstrated
   rather than assumed.** The nested-inductive auxiliary declarations where the
   defect lives never enter the environment: they are created in a temporary
   kernel environment and rewritten by `restore_nested`, so a search from inside
   Lean re-checks only the surviving recursors. This is the same property that
   made lean4#14616's exploit uncapturable as an arena export test. Black-box
   probing cannot reach it; instrumenting `replace_if_nested`/`restore_nested` in
   a source build can.
1. **The Lean Kernel Arena corpus (§3).** Fourteen catalogued attacks, four of
   which the official kernel has fallen for, plus the `undecidability/` category
   that formalises what [`Audits/Lean/Metatheory/`](Audits/Lean/Metatheory/)
   measured independently. This is the single largest gap, and it is now the
   community's canonical artifact.
2. **Rocq's remaining proofs of `False` (§4).** Four of the 2026 sweep's eight
   are covered; #21690, #21694, #21702, #21736, #21797, #21839, #22021 and the
   whole pre-2026 history are `gap`. The two OPEN ones with a route to `False`,
   #22287 and #22024, are the highest priority.
3. **Rocq's untracked hatches (§1.2).** `vm_compute`/`native_compute`,
   `Extraction`, and `Declare ML Module` are the three routes `Print Assumptions`
   cannot see at all, and none has an artifact.
4. **Univalence + UIP (§1.1).** The one classical inconsistency with no exhibit
   in either system. Statable in both.
5. **Pair #12747 with `LevelFuzzer`.** Confirm case-by-case that the fuzzer's
   162 incompleteness cases are instances of the `imax`-to-`max` defect.
6. **Re-survey cadence.** Both trackers move faster than any static catalog —
   four of the Lean defects in §2.2 were fixed *on the day of this survey*. This
   file carries a survey date for that reason.

### 5.1 What the 2026-07-31 audit sweep ruled out

Recorded so the same ground is not re-covered. Each was a systematic search of a
Lean kernel surface against an explicit oracle; harnesses and counts are in
[`Audits/`](Audits/). All clean unless noted.

| Surface | Oracle | Result |
| --- | --- | --- |
| `Nat` accelerators at powers-of-two boundaries | compiled `Nat` | 39,510 applications, 0 divergence |
| `Level.geq` | denotational `≥` over valuations | 60,000 pairs, 0 unsound, 738 incomplete |
| Inductive field vs. struct universe admission | `m ≤ l` universally, or `l` denotationally `0` | 289 declarations, all correct |
| `nparams` in a raw `inductDecl` | parameter/index split | kernel validates it; lying is rejected |
| `Expr.proj` structure-name confusion, out-of-range index, partial constructor | `infer_proj` | all rejected |
| Subject reduction, and `e ≡ whnf e` | kernel's own `check` | 5,656 terms, 0 violations |
| `Array` `any`/`all`/`foldl`/`foldr` at out-of-range `start`/`stop` | compiled `Array` | 576 comparisons, 0 divergence |
| `UInt8`/`UInt64` arithmetic and shifts at word boundaries | compiled `UInt` | 9,582 comparisons, 0 divergence |
| `String` `get`/`next`/`prev`/`atEnd`/`extract` at invalid UTF-8 boundaries | compiled `String` | 320 comparisons, 0 divergence |
| `Nat.rec` on literals, `0` through `2^100` | expected constructor branch | 0 divergence |
| `Prop` inductives: subsingleton-elimination restriction | proof-relevance | 40 declarations, correctly restricted |
| Kernel-internal fvar leaks into inferred types | `_kernel_fresh` scan + re-check | none (i.e. #10475 is fixed) |
| Module boundary: `sorry`, private-in-public, section variables | `#print axioms`, visibility | all correctly guarded |
| `Expr.mdata` as a bypass: positivity, self-occurrence-in-index, `check_no_metavar_no_fvar` | the corresponding kernel check | every check strips `mdata`; all of `hasFVar`/`hasMVar`/`hasLooseBVars` propagate through it |
| `Nat.sqrt`, `nextPowerOfTwo`, `lcm`, `min`, `max`, `testBit` | compiled implementation | 10,638 comparisons, 0 divergence |
| Signed fixed-width arithmetic: `Int8`/`Int16`/`Int32`/`Int64`, ten ops each incl. `div`/`mod`/shifts at `minValue` | compiled implementation | 23,160 comparisons, 0 divergence |
| Unsigned `UInt16`/`UInt32` | compiled implementation | 3,940 comparisons, 0 divergence |
| `USize`/`ISize`, and word-size-dependent facts | kernel reducibility | kernel is correctly **stuck** — `System.Platform.numBits` is opaque, so even `(1 : USize) + 2 = 3` is not `rfl`-provable, and `numBits = 64` is undecidable. Sound: the theory fixes only `numBits = 32 ∨ numBits = 64` |
| Arbitrary-precision `Int`: `ediv`/`emod`/`fdiv`/`fmod`/`tdiv`/`tmod`/`bdiv`/`bmod`/`gcd` at ±2^32, ±2^64, ±2^70 | compiled implementation | 16,428 comparisons, 0 divergence |
| `BitVec` at width 8: `sdiv`/`smod`/`srem`/`udiv`/`umod`, shifts and rotates past the width, `setWidth`/`signExtend` up and down, signed and unsigned comparisons | compiled implementation | 5,070 comparisons, 0 divergence |
| **Every `@[implemented_by]` pair** in core + Batteries + Mathlib | the pair carries *no* proof obligation, so the two sides must be compared directly | 173 pairs; **166 have `unsafe` implementations** the kernel cannot reduce, and the remaining 7 bottom out in irreducible `USize` operations, so none is kernel-differentiable |
| `Nat.repr` vs `Nat.reprFast` across both of its internal boundaries (the 128-entry memo table, and `USize.size`) | an independent decimal conversion built from `Nat.div`/`Nat.mod` | 336 comparisons, 0 divergence. `reprFast` is correct by construction: it uses `USize.ofNatLT n h` with a proof `h : n < USize.size`, and falls back to the general path above it |
| `Declaration.mutualDefnDecl` — the one declaration path never probed | kernel acceptance by safety level | firewalled by design: `add_mutual` **rejects** a block whose safety is `safe` (`declaration is not tagged as unsafe/partial`), so every kernel-level mutual block is `unsafe`/`partial` and the `infer_constant` gate stops a safe declaration depending on it. Headers are checked before any body, and #14608's same-`lparams` requirement is enforced |
| `Float`: is anything *proved* about it anywhere in core or Mathlib? | IEEE-754 violates reflexivity (`NaN`) and congruence (zero vs. negative zero), so any lawfulness lemma would be false and `native_decide`-exploitable | **zero** `Lawful*` or `DecidableEq` instances mentioning `Float`/`Float32`; all 25 theorems that mention them are auto-generated structure lemmas (`.mk.inj`, `.mk.injEq`, `.sizeOf_spec`, `.ext`) or `Nonempty` instances. The "prove nothing, so nothing can be contradicted" discipline holds across the whole ecosystem |
| `Array.qsort`, `Array.insertionSort`, `List.mergeSort`, `Array.binSearch` — all with `unsafe` fast implementations | an independent insertion sort, and membership for the search | 197,604 comparisons over pseudorandom inputs at lengths 0–129, **0 divergences** |
| Large `Nat.shiftLeft` *below* the panic threshold — is `mul2k` correct at scale? | round trip through `shiftRight`, cross-check against the `Nat.pow` accelerator, popcount, and low-64-bit agreement with the compiled implementation, at shifts up to 2^24 | 95 checks, 0 divergence. This closes the `shiftLeft` finding from the other side: the value is **correct** everywhere it is computed, so the defect is purely the uncatchable abort above `UINT_MAX` and never a wrong result |
| Nested-inductive auxiliary declarations — can the missing re-check of lean4#14621 be exercised from inside Lean? | re-run `Kernel.check` on the type and value of every declaration the kernel generated for nine nested inductives, including the non-uniform shapes of #14582 | 240 surviving declarations re-checked, **0 failures** — but the test cannot reach the interesting artifacts: **zero** constants containing `_nested` persist in the environment. The auxiliary types are transient, built in a temporary kernel environment and mapped back by `restore_nested`, so only recursors, `below`/`brecOn`/`sizeOf`/`noConfusion` survive. Confirmed at the lowest level reachable from Lean: feeding a raw nested `inductDecl` to `Kernel.Environment.addDecl` and diffing the returned environment yields exactly four new constants — the type, its constructor, and the two recursors — and no `_nested` name at all |

Two things did turn up, neither a `False`. `Nat.shiftLeft`'s missing magnitude
guard is §2.6. And `Kernel.check` with a caller-supplied local context whose
fvar is named `_kernel_fresh.N` lets the kernel's own generated binder **capture**
it — `fun (y : False) => x` is typed `False → False` where the context binds
`x : Nat`, while the control (`_uniq.0`) is typed correctly. It is contained:
every `add_*` path in `environment.cpp` rejects fvars in values *before*
type-checking, so it cannot reach a closed declaration, and Lean's own name
generator never produces the reserved prefix.

---

## 6. Sources

| Source | What it contributes |
| --- | --- |
| Rocq, [`dev/doc/critical-bugs.md`](https://github.com/rocq-prover/rocq/blob/master/dev/doc/critical-bugs.md) | **The single most valuable source for either system.** Maintainer-curated, since 8.0, with introduced/impacted/fixed/found-by fields. Lean has no equivalent. |
| [Lean Kernel Arena](https://arena.lean-lang.org/) + [repo](https://github.com/leanprover/lean-kernel-arena) | The attack corpus of §3 and the live differential-testing results. |
| Lean release notes, in [`leanprover/reference-manual`](https://github.com/leanprover/reference-manual) `Manual/Releases/` | The only place `v4.32.1`/`v4.32.2` are described as soundness releases. Note the notes systematically *understate* compiler-TCB unsoundness. |
| [`lean4lean`](https://github.com/digama0/lean4lean) `bugs-found.md` and `divergences.md` | Bugs found by formalization, and the standing kernel assumptions that are not bugs — including the prelude assumption underlying all of §2.3. |
| Tristan Stérin, [*In search of falsehood*](https://tristan.st/blog/in_search_of_falsehood) | The 2026 sweep: Opus 4.6 against both kernels, producing 7 proofs of `False` in Rocq plus 3 further bugs, 0 in the official Lean kernel with 4 other bugs, and proofs of `False` in `nanoda` (2) and `lean4lean` (1). |
| Leonardo de Moura, [*Who Watches the Provers?*](https://leodemoura.github.io/blog/2026-3-16-who-watches-the-provers/) | The Lean FRO's position: multiple independent kernels are the defence. |
| Lawrence Paulson, [*Broken proofs and broken provers*](https://lawrencecpaulson.github.io/2026/01/15/Broken_proofs.html) | The view from outside both systems: Isabelle/HOL, HOL88, LCF, PVS. |
| [`nielsvoss/lean-pitfalls`](https://github.com/nielsvoss/lean-pitfalls) | The realistic failure modes — mis-stated theorems, `autoImplicit`, junk values — which are far commoner than any kernel bug. |
| Rocq stdlib `Logic/`: `Hurkens`, `Berardi`, `ClassicalFacts`, `Diaconescu`, `ChoiceFacts`, `Eqdep_dec` | The paradox library and the precise statements of §1.1. |
| [`rocq-archive/paradoxes`](https://github.com/rocq-archive/paradoxes) | `BuraliForti.v`, `Reynolds.v`, `Russell.v`, `Hurkens_Set.v`, `diaconescu.v` — the `gap` rows of §1.1. |
| Carneiro, *The Type Theory of Lean* (MSc thesis) and [Lean4Lean](https://arxiv.org/abs/2403.14064) | Relative consistency (ZFC + n inaccessibles, as a schema), and the acknowledged gaps in the metatheory. |

**One timeline point is worth stating plainly.** De Moura's March 2026 post
observes that Opus 4.6 *"did not manage to find a proof of false in the Lean
official kernel"*, in contrast to seven in Rocq — a fair summary of the evidence
then available. Four months later, **July 2026 produced five distinct axiom-free
proofs of `False` in the official Lean kernel** (#14484, #14576, #14613, #14616,
plus the #14609 module-system break), all found by AI-assisted auditing, all
fixed within hours to days, and one of them exploitable *through* `comparator`.
Three of the arena's independent checkers currently score a perfect 57/57 on the
attack corpus where the official kernel scores 56/57.

The reasonable conclusion is not that one system is sounder than the other, nor
that the situation has deteriorated. It is that the *rate of discovery* changed
in 2026, in both systems, for the same reason — and that a static catalog is now
a snapshot. Hence the survey date, and hence §5's last item.
