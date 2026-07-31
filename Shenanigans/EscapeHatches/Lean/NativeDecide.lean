/-!
# `native_decide` + `@[implemented_by]`: the documented boundary

The one route in this directory that produces a closed, `sorry`-free, `unsafe`-
free `theorem Paradox : False` out of nothing but two core attributes. It is not
a defect: `@[implemented_by]` is an *assertion* that the compiled behaviour
agrees with the logical definition, and asserting a false one is the user's
error. But it is the sharpest illustration of what leaving the kernel costs.

Category (see `../../README.md`): **escape hatch** — and the audit does fire,
though not in the way most write-ups (including an earlier version of this file)
say. See §2.

Toolchain: Lean 4.32.0. Verified by `../verify.ps1`.
-/

/-! ## 1. The derivation

`evil` and `secret` are two different `Bool`s. The kernel unfolds `secret` to
`false`; the compiler is told to run `evil`, which is `true`. -/

def evil : Bool := true

@[implemented_by evil]
def secret : Bool := false

/-- The kernel's answer, by δ-reduction. -/
theorem secret_false : secret = false := rfl

/-- The compiler's answer, by running native code. -/
theorem secret_true : secret = true := by native_decide

theorem Paradox : False :=
  Bool.noConfusion (secret_true.symm.trans secret_false)

theorem anything (P : Prop) : P := Paradox.elim

/-! ## 2. What the audit actually reports, as of Lean 4.32

The widely-quoted answer is `Lean.ofReduceBool`. That is no longer right, and
the change matters.

`Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool` and `Lean.ofReduceNat`
are all marked
`@[deprecated "in-kernel native reduction is deprecated; assert native
evaluations with axioms instead" (since := "2026-02-01")]`.
Under [RFC #12216](https://github.com/leanprover/lean4/issues/12216), accepted
2026-01-28, `native_decide` now runs the computation *in the tactic* and emits
**one fresh axiom per use**, named after the theorem that used it, instead of
routing through the kernel's compiled-code hook.

So the dependency below is not a shared, easily-allowlisted core axiom; it is a
per-site assertion that names its own origin. That is strictly better for
auditing — a reviewer sees which theorem asserted which computation — and it is
why the exhibit in `../../KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean`
documents a mechanism that is on its way out. -/

/-- info: 'Paradox' depends on axioms: [secret_true._native.native_decide.ax_1_1] -/
#guard_msgs in #print axioms Paradox

/-- info: 'anything' depends on axioms: [secret_true._native.native_decide.ax_1_1] -/
#guard_msgs in #print axioms anything

/-! ## 3. Why this is the contrast case for `../../KernelDefects/`

Everything here is visible. Compare the accelerator family in
`../../KernelDefects/Lean/Accelerators/`, where `#print axioms` reports
**nothing at all** — that is the difference between using a documented trust
extension and getting the kernel to believe something on its own authority.

Two further points worth recording:

* **`@[csimp]` is marketed as the safe alternative to `@[implemented_by]`, and
  it hides more.** [lean4#7463](https://github.com/leanprover/lean4/issues/7463)
  (open) shows that axioms used in a `csimp` proof are not propagated through
  `native_decide`: a `csimp` lemma proved from an explicit `axiom cheating :
  False` yields a theorem whose `#print axioms` does not mention `cheating`.
* **The bug does not have to be yours.** Divergences between a reference
  implementation and its `@[implemented_by]` counterpart *in Lean core* have
  produced this same contradiction several times —
  [#11773](https://github.com/leanprover/lean4/issues/11773) (`Array.foldl` with
  an out-of-range `stop`), [#4306](https://github.com/leanprover/lean4/issues/4306)
  (`UIntN.toNat` constant folding), [#10213](https://github.com/leanprover/lean4/issues/10213)
  (`@[csimp]` ignoring universe parameters). Mathlib forbids `native_decide`
  outright for this reason.

The Rocq counterparts are `vm_compute` and `native_compute`, which are worse in
one specific respect: they are kernel-level conversion machines rather than
tactics, so they leave **no trace in `Print Assumptions` at all**. See
`../Coq/TypingFlags.v` for what Rocq does track. -/
