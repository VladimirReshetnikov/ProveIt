# Checker, representation, and object-arithmetic review

Reviewed source: `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.
All module paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## 1. Replace seven custom list inductions with the existing core API

**Ready first step.** Five copies prove that a successful optional lookup is
list membership; two copies construct an optional-lookup index from membership.
Lean 4.32.0 already provides exactly the required statements:

```lean
List.mem_of_getElem? h
List.getElem?_of_mem h
```

Locations: `AnnotatedProofChecker.mem_of_lookup` (177-187),
`AnnotatedRename.lookup_mem` (110-117), `AnnotatedBound.lookup_mem` (50-57),
`AnnotatedRuleSide.lookup_mem` (18-25) and `exists_lookup` (27-35),
`AnnotatedAssumption.lookup_mem` (40-47) and `exists_lookup` (49-57).
Retaining the private wrapper names avoids touching callers. Alternatively,
delete the wrappers and call the library lemmas directly, but the supplied patch
chooses the smaller integration change.

`list-library.patch` reduces those seven declarations from 61 to 21 physical
source lines, a net saving of 40. These counts include their unchanged
declarations. The exact generic signatures compile in `ListChecks.lean`; its
axiom audit reports only `propext`. `git apply --check` passed. The patch itself
has not yet had a complete module/dependency rebuild; the generic checks do not
establish the state of every dependent module.

This is more than stylistic compression: the repository no longer maintains
five independent proofs of an ordinary list fact. It does not alter the
certificate parser, accept invalid parent references, or change a theorem's
statement.

## 2. Rewrite under primitive recursion instead of proving congruence by induction

**Compiled complete-module replacements.** `ScalarPRCode.Realizes.prec`
(64-80) and `PRCode.Realizes.prec` (88-104) already have pointwise equations
for the supplied base and step programs. The existing proofs perform a second
induction merely to push those equations through `Nat.rec`.

The scalar proof after the unchanged subtype constructor is:

```lean
  intro packed
  simp only [eval, Nat.unpaired, p.property, q.property]
```

The vector proof uses `[eval, p.property, q.property]`. Simplification rewrites
the base and step *under the recursor*, including its lambda, so the induction
is unnecessary. The same observation reduces the `.prec` branch of
`ScalarPROptimizer.eval_optimize` (119-133) to:

```lean
  | prec f g hf hg =>
      simp only [optimize, eval_smartPrec, eval, hf, hg]
```

`pr-congruence.patch` saves 34 physical source lines: proof fragments of
12, 11 and 15 lines become 1, 1 and 2 lines. All three complete modified source
files compiled successfully, as did independent `PRProofChecks.lean` examples.
That file also proves by `rfl` that both replacement `Realizes.prec` definitions
have the same executable `.val` as their original counterparts. The axiom
reports contain only standard Lean axioms, but the footprint is not identical:
the old scalar `prec` is axiom-free, while the shorter proof uses `propext` and
`Quot.sound`; the old vector `prec` uses only `propext`, while the shorter proof
also uses `Quot.sound`. The optimizer already used all three standard axioms,
and its shortened proof retains that set. This is the cost of rewriting under
a function binder via function extensionality. If preserving the smaller
footprint is a goal, `RecursorCore.lean` supplies a kernel-checked, axiom-free
`rec_congr` proved once by a four-line induction; the two callers can reuse that
lemma instead. The file checks the generic lemma; it does not contain a tested
replacement patch using that fallback. These tests do not constitute a
whole-repository rebuild.

## 3. Move assignment transport to the representation boundary

**Checked common lemma and complete modified module.**
`Representation.reindex` (155-166), `conjunction` (170-198), and `disjunction`
(202-231) repeatedly prove function extensionality for a renamed natural
assignment. Conjunction and disjunction each repeat both a left and a right
version of the same calculation. Moreover, `QuarticCompiler` already has a
private `assignment_comp` at lines 95-98. The proposal is to generalize and
expose that existing idea in the earlier `Representation` module, not to add
another unrelated helper:

```lean
theorem natAssignment_comp_map
    (v : sigma' -> Nat) (w : tau' -> Nat)
    (f : sigma -> sigma') (g : tau -> tau') :
    natAssignment v w o Sum.map f g =
      natAssignment (v o f) (w o g) := by
  funext i
  cases i <;> rfl
```

The actual Unicode Lean declaration is in `AssignmentChecks.lean`, which
compiled and passed the standard-axiom audit. Then `Expr.eval_rename` and the
new lemma directly normalize the assignments. Use an explicit `simp only`
list at these proof sites first; a global simplifier attribute is not required.

`assignment-map.patch` preserves all witness counts and expressions and
changes their correctness proofs. It saves 25 lines in the whole module,
including the cost of the new general lemma. After a missing cached dependency was repaired, the complete modified module
compiled successfully with the pinned compiler and explicit dependency path.
The initial wrapper processes were stopped and the final direct compiler check
returned exit code 0. No downstream integration rebuild is claimed.

## 4. Share the scanner's iteration algebra without changing its executable code

The same `fuel.rec initial (fun _ acc => step acc)` appears in
`AnnotatedRenameScan` (29-55), `AnnotatedBoundScan` (25-48),
`AnnotatedLineScan` (32-57), and `AnnotatedContext` (91-119).
Each separately proves zero absorption, movement of the first step out of a
successor-length run, and retention of a completed state.

`ScannerCore.lean` proves three recursor-level facts once: `rec_fixed`,
`rec_succ_left`, and `rec_invariant`. It imports only `Init`; all three compile
on Lean 4.32.0 and their audits report no axioms. For example, an existing
`scan_zero` can keep its statement and become a direct application of
`rec_fixed step 0 step_zero fuel`; `scan_done` is the same lemma with the
appropriate terminal state. Existing scanner definitions can remain literally
unchanged, because their recursors are definitionally the expressions in the
lemmas. This avoids perturbing program size theorems or the supplied PR code.

The next, larger change is to isolate a one-step invariant and use
`rec_invariant` for `AnnotatedLineScan.scan_sound` (59-88). Its raw-input
invariant must still include the absorbing zero state and a history consisting
of actual provable judgments. The complete-list simulation in renaming and
bound scanning also has nearly identical induction structure, but that should
be a separate refactor with an explicit code/row correspondence. The core
lemma checks do not certify this larger refactor or claim a measured net line
saving after integration.

## 5. Strengthen the numeric classifier API from acceptance to value equality

`AnnotatedRenameLocal` and `AnnotatedBoundLocal` already prove both that
`localCheck` is zero or one and that its value is one exactly when a Boolean
row validator accepts. Later `step_cons` proofs reconstruct the rejecting case
from these two facts. See `AnnotatedRenameScan.step_cons` (57-69) and the
parallel `AnnotatedBoundScan.step_cons`.

Combine the facts once into the stronger reusable conclusion
`localCheck ... = truth (valid ...)`. The general lemma in `BooleanCore.lean`
states that `n=0 or n=1` plus `(n=1 iff b=true)` determines
`n = if b then 1 else 0`. It compiles with only `Init` and reports `propext`.
The scanner proof can then rewrite the numeric value directly before splitting
on the Boolean. This removes the negative-acceptance proof and repeated
`resolve_right` argument at each use.

Keep both premises: knowing only `n=1 iff b=true` does not determine `n` on a
rejecting input. Also keep the existing raw-natural Booleanity theorem; the
new equality theorem at encoded rows does not replace raw-code soundness.
The generic lemma is checked; the full scanner rewrites remain proposals.

## 6. Transport definable induction once, retaining the formula witness

The `Object*` modules repeatedly use `omega_ind` through an explicitly supplied
formula and its satisfaction equivalence. Examples include
`ObjectAdditionLaws.addRel_succ_left` (52-72), `addRel_comm` (86-105),
`addRel_assoc` (126-150), `ObjectMultiplicationLaws`, and `ObjectDistributivity`.
Their algebraic induction steps are meaningful; the repeated `Sat`/semantic
predicate conversions are administrative.

Add a lemma `omega_ind_of_spec` whose parameters include an actual `phi : Form`,
an environment `e`, and `forall n, Sat mem (scons n e) phi iff P n`.
It transports the base and successor hypotheses through that equivalence,
calls the existing `omega_ind`, and transports the result back. Each arithmetic
proof can then conduct the induction directly on its named semantic relation,
while continuing to display the formula witnessing definability.

This is a design proposal, not a checked file in this packet. Do **not** replace
it by unrestricted induction over arbitrary predicates on `Natural H`, nor by
external induction on Lean's `Nat`: neither supplies the required theorem in
nonstandard models. Likewise, `ObjectOmegaSemiring` already defines the
semiring interface; proposing to create that interface anew would duplicate
existing work. The useful new abstraction is below that interface.

## 7. Centralize the sealed-model completeness boilerplate

Many object-arithmetic endpoints begin by applying
`completeness_inf_context ZFCax_s [] ... Sentences_ZFC`, obtaining model data,
constructing `H := axioms_of_zfc_model ...`, and applying `seal_valid` before
their actual arithmetic argument. See the endpoints in `ObjectAdditionLaws`
(183-206), `ObjectDistributivity` (132-156), `ObjectMultiplication` (198-219),
and several `ObjectCode*` modules. `axioms_of_zfc_model` itself is currently
duplicated as a private lemma in `ObjectArithmetic` (143 onward) and a public
one in `ObjectMultiplication` (169 onward).

Move the model-extraction lemma to an appropriately early module and add one
semantic-validity-to-sealed-provability bridge. The bridge must quantify over
all models/environments required by the existing completeness theorem and
conclude the same sealed formula; callers then supply only their semantic
argument. Keep nonempty-context endpoints such as `ObjectConsistency`
separate unless a distinct context-aware bridge is proved.

This is an architectural proposal. It shortens many leaf endpoints, reduces
coupling to completeness details, and removes the duplicated model-extraction
proof. It does not prove a missing arithmetic/compiler link or a new internal
ZFC consistency statement.

## Artifact status

Checked: `PRProofChecks.lean`, `AssignmentChecks.lean`, `ScannerCore.lean`,
`ListChecks.lean`, `BooleanCore.lean`, `RecursorCore.lean`, and complete modified
copies of the three PR modules and `Representation` in `patched/`. Logs
accompany the checks.

Patch candidates: `pr-congruence.patch` (complete modified files compiled),
`list-library.patch` (exact helper signatures checked, applies cleanly),
`assignment-map.patch` (common lemma and complete modified module compiled).
The `sources/` directory contains temporary inspection copies and should not be
included in the final packet. The original checkout was not changed by this
review task.
