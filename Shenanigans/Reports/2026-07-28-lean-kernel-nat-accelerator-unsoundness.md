# A zero-axiom proof of `False` in the Lean 4 kernel

*2026-07-28 — Lean `4.31.0` and `4.32.0`*

## Summary

The Lean 4 kernel accepts a proof of `False` that uses no `sorry`, no `unsafe`,
no `native_decide`, and **no axioms at all** (`#print axioms` reports none). The
resulting `.olean` also passes `leanchecker --fresh`, the independent replay
checker shipped with the toolchain.

> **Bottom line — Lean's official judge rejects all of these.** Every exhibit was
> run through [`leanprover/comparator`](https://github.com/leanprover/comparator)
> against a `theorem boom : False := sorry` challenge; all four are rejected,
> while an honest control is accepted. Comparator's *own regression suite*
> already contains this construction (`tests/projects/primitive_issue`, asserting
> `"exit_code": 1`), and it is essentially identical to `NatGcdFreeName.lean`.
> Details and exact messages:
> [`Shenanigans/KernelDefects/Lean/Comparator/README.md`](../KernelDefects/Lean/Comparator/README.md).
>
> Two gates are needed and neither suffices alone: with
> `set_option debug.skipKernelTC true` a bypassed declaration still reports
> *"does not depend on any axioms"*, and `leanchecker --fresh` happily replays a
> plain `axiom sneaky : False` (exit 0). This is precisely why comparator exists.

> **Prior art — this is a rediscovery.** The technique below (redefine `Nat.add`
> in a `prelude` module, then play the kernel's GMP accelerator off against
> delta-reduction) was demonstrated publicly by Joachim Breitner, a Lean core
> developer, in the comment thread of the Manifold market
> ["Is the Lean kernel unsound?"](https://manifold.markets/tfae/is-the-lean-kernel-unsound),
> where it was ruled out as a "shenanigan" because redefining core types and
> operations amounts to *replacing part of the system* rather than finding an
> inherent hole in it. That reading is reasonable and should be applied here.
> The contribution of this report is a minimal, self-contained, end-to-end
> verified reproduction plus the negative results and hardening observations in
> the later sections. There is no issue for it on the `leanprover/lean4` tracker,
> so the behaviour is unfixed — but it is known, and was not treated as a bug.

The cause is that the kernel's built-in `Nat` normalizer extension is keyed on
*names only* and is never validated against the declaration it fires on, while a
`prelude` module may legitimately own those names.

Artifacts: [`Shenanigans/KernelDefects/Lean/`](../KernelDefects/Lean/README.md).

## The mechanism

`src/kernel/type_checker.cpp` interns a fixed set of constants at start-up:

```cpp
g_nat_zero = new_persistent_expr_const({"Nat", "zero"});
g_nat_succ = new_persistent_expr_const({"Nat", "succ"});
g_nat_add  = new_persistent_expr_const({"Nat", "add"});
g_nat_beq  = new_persistent_expr_const({"Nat", "beq"});
/* also sub, mul, pow, gcd, div, mod, ble, land, lor, xor, shiftLeft, shiftRight */
```

and `type_checker::reduce_nat` dispatches on plain expression equality with
them:

```cpp
if (f == *g_nat_add) return reduce_bin_nat_op(nat_add, e);
```

`reduce_bin_nat_op` computes the answer with the runtime's GMP arithmetic. Two
properties matter:

1. **No validation.** Nothing checks that the constant named `Nat.add` denotes
   addition — or that `Nat` is the natural numbers. The soundness argument for
   the accelerator is "`Nat.add` is *the* core definition and GMP agrees with
   it", and that argument silently assumes nobody else can own the name.

2. **The accelerator wins over delta.** In `type_checker::whnf` the extension is
   tried *before* unfolding definitions:

   ```cpp
   expr t1 = whnf_core(t);
   if (auto v = reduce_native(env(), t1))      { ... }
   else if (auto v = reduce_nat(t1))           { ... }   // <-- accelerator
   else if (auto next_t = unfold_definition(t1)) { t = *next_t; }
   ```

   but it only fires once both arguments reduce to `Nat` literals. When the
   arguments are *free variables* the accelerator declines and the kernel falls
   through to delta-reduction, which uses the declared body.

So for a user-supplied `Nat.add` the kernel has **two reduction rules that
disagree**, and which one applies depends on whether the arguments are closed.
Both are reachable in one module.

A `prelude` module is the ingredient that lets a user own the names. `prelude`
suppresses the implicit `import Init`; it is a standard, supported feature and
is how `Init/Prelude.lean` itself is written. Nothing warns about it.

## The proof

Complete module (`Shenanigans/KernelDefects/Lean/Accelerators/NatAddAccelerator.lean`, elided):

```lean
prelude
universe u

set_option genCtorIdx false in
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

inductive False : Prop
inductive True : Prop where | intro : True

/-- A perfectly ordinary definition.  It simply is not addition. -/
def Nat.add (a : Nat) (_b : Nat) : Nat := a

/-- (1) Free variables ⇒ the accelerator declines ⇒ the kernel delta-reduces
        and agrees with the declaration. -/
theorem add_left (a b : Nat) : Eq (Nat.add a b) a := Eq.refl

/-- (2) Closed arguments ⇒ the built-in GMP `Nat.add` fires: `0 + 1 = 1`. -/
theorem add_lit : Eq (Nat.add Nat.zero (Nat.succ Nat.zero)) (Nat.succ Nat.zero) :=
  Eq.refl

/-- (3) Hence `0 = 1`. -/
theorem zero_eq_one : Eq Nat.zero (Nat.succ Nat.zero) :=
  @Eq.rec Nat (Nat.add Nat.zero (Nat.succ Nat.zero))
    (fun x _ => Eq x (Nat.succ Nat.zero))
    add_lit Nat.zero (add_left Nat.zero (Nat.succ Nat.zero))

def NZ (n : Nat) : Prop := @Nat.rec (fun _ => Prop) True (fun _ _ => False) n

/-- (4) `False`. -/
theorem boom : False :=
  @Eq.rec Nat Nat.zero (fun x _ => NZ x) True.intro (Nat.succ Nat.zero) zero_eq_one
```

No numeric literals appear in the source: `Nat.succ Nat.zero` is itself folded
to the literal `1` by the `nargs == 1` branch of `reduce_nat`, and `Nat.zero` is
accepted directly by `is_nat_lit_ext`. `set_option genCtorIdx false` is only
bootstrap hygiene, copied from `Init/Prelude.lean`'s own `Nat`.

`Shenanigans/KernelDefects/Lean/Accelerators/NatBeqAccelerator.lean` is a second, independent
instance through `Nat.beq`, whose accelerator (`reduce_bin_nat_pred`) returns the
constants named `Bool.true` / `Bool.false` — also by name.

## Strengthening: nothing has to be redefined

The objection above ("you replaced part of the system") turns out not to be
decisive. `Shenanigans/KernelDefects/Lean/Accelerators/NatGcdFreeName.lean` imports
`Init.Prelude` and uses the **genuine** core `Nat`, `Nat.add`, `Eq`, `rfl`,
`True`, `False`, `Nat.rec` and numeric literals, entirely unmodified. It only
*defines* `Nat.gcd`, which `Init.Prelude` does not claim — core defines it far
downstream in `Init.Data.Nat.Gcd`:

```lean
prelude
import Init.Prelude

def Nat.gcd (a : Nat) (_b : Nat) : Nat := a

theorem gcd_left (a b : Nat) : Eq (Nat.gcd a b) a := rfl   -- delta
theorem gcd_lit : Eq (Nat.gcd 0 1) 1 := rfl                -- GMP accelerator
theorem zero_eq_one : Eq 0 1 :=
  @Eq.rec Nat (Nat.gcd 0 1) (fun x _ => Eq x 1) gcd_lit 0 (gcd_left 0 1)
```

`Lean/FreeNameSurvey.lean` enumerates the surface: under `Init.Prelude` **nine**
kernel-special-cased names are free — `Nat.gcd`, `Nat.land`, `Nat.lor`,
`Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight`, `Lean.reduceBool`,
`Lean.reduceNat`, `eagerReduce`. The issue is therefore not "a module that
redefines `Nat`" but "a module that defines a name the kernel has already
claimed but the prelude has not yet reached".

Note the asymmetry with the compiler: a module *without* `prelude` always gets
the implicit `import Init` even when it lists explicit imports (verified), so
this needs `prelude` to control the import prefix — but no core declaration is
displaced.

## The most severe mechanism: the kernel fabricates an inhabitant of an empty type

`Shenanigans/KernelDefects/Lean/Accelerators/StringLitFabrication.lean` is not a "two rules
disagree" bug at all. `string_lit_to_constructor` (`src/kernel/inductive.cpp`)
assembles a term **entirely out of hard-coded names**:

```cpp
expr r = *g_list_nil_char;                     // List.nil.{0} Char
while (i > 0) { i--;
  r = mk_app(*g_list_cons_char,                // List.cons.{0} Char
             mk_app(*g_char_of_nat,            // Char.ofNat
                    mk_lit(literal(cs[i]))), r);
}
return mk_app(*g_string_mk, r);                // String.ofList
```

and `inductive_reduce_rec` (`src/kernel/inductive.h`) feeds it straight to the
recursor rule:

```cpp
else if (is_string_lit(major)) major = whnf(string_lit_to_constructor(major));
optional<recursor_rule> rule = get_rec_rule_for(rec_val, major);
...
rhs = mk_app(rhs, rule->get_nfields(), major_args.data() + nparams);
```

**Nothing type-checks the assembled term.** So `String.rec`'s minor premise is
applied to that character list whatever `String.ofList`'s field type actually is.
Declare it to be `Empty` — a type with no constructors — and the kernel hands you
an inhabitant:

```lean
prelude
inductive False : Prop
inductive Empty : Type
inductive String : Type where
  | ofList : Empty → String

noncomputable def Q (s : String) : Prop :=
  @String.rec (fun _ => Prop) (fun _ => False) s

theorem extract (s : String) : Q s :=
  @String.rec (fun s => Q s) (fun e => @Empty.rec (fun _ => False) e) s

theorem boom : False := extract "a"
```

`extract` is entirely legitimate — it only says "a `String` carries an `Empty`,
so eliminate it", which is vacuous in any honest environment. The unsoundness is
wholly on the kernel's side. Trigger: a bare string literal. No `Nat`, no
numerals, no `OfNat`, no arithmetic accelerator, and no `List` or `Char`
declarations at all — those names are never resolved, precisely because the
kernel never infers the type of the term it just built.

Verified: `lean` exit 0, `#print axioms boom` reports nothing, `leanchecker
--fresh` accepts.

For real Lean this is harmless, because core's `String.ofList` genuinely is that
constructor with that field type. But that is an *unchecked assumption about the
ambient environment* — the same root cause as the arithmetic accelerators, with a
strictly worse failure mode: not "arithmetic comes out wrong" but "the kernel
manufactures an inhabitant of an empty type".

The same shape applies to `nat_lit_to_constructor`, which builds
`Nat.succ (lit (n-1))` without checking `Nat.succ`'s signature.

## A different mechanism: the native hook, and an axiom-tracking hole

`Shenanigans/KernelDefects/Lean/Accelerators/ReduceBoolFreeName.lean` defines the free name
`Lean.reduceBool`. The kernel's `reduce_native` matches it by name, runs the
*compiled code* of a nullary constant argument, and believes the result — while
delta-reduction on a free-variable argument gives the declared body. Same
two-rule disagreement, different extension.

What makes this one interesting is what is missing: no `Lean.ofReduceBool`, no
`native_decide`, no `@[implemented_by]`, no `@[extern]`. The axiom
`Lean.ofReduceBool` exists precisely so that reliance on compiled code is visible
in `#print axioms`; owning the name bypasses that tracking entirely. `lean` exits
0 and `#print axioms boom` reports nothing.

This one does **not** survive `leanchecker`, which replays into an environment
where the interpreter cannot find `probe`:

```
leanchecker found a problem in ReduceBoolFreeName
uncaught exception: while replaying declaration 'rb_native':
(kernel) (interpreter) unknown declaration 'probe'
```

So it is an axiom-*tracking* hole rather than a kernel hole — closely related to
[lean4#7463](https://github.com/leanprover/lean4/issues/7463) (`@[csimp]` can
pass axioms by `#print axioms`), but reachable without any axiom at all.

## Verification

| Step | Result |
| --- | --- |
| `lean -o NatAddAccelerator.olean …` | exit `0`, no diagnostics |
| `#print axioms boom` | `'boom' does not depend on any axioms` |
| `leanchecker NatAddAccelerator` | exit `0` |
| `leanchecker --fresh NatAddAccelerator` | exit `0` |
| `leanchecker NegativeControl` (control) | `leanchecker found a problem`, exit `1` |

The control matters. `Shenanigans/KernelDefects/Lean/Controls/NegativeControl.lean` uses
`set_option debug.skipKernelTC true` to install a blatantly ill-typed
`bogus : False` into the environment; that module also builds with exit `0` and
also reports no axioms, but `leanchecker` rejects it. The unsound modules are not
rejected, so their acceptance is a real kernel judgement rather than a checker
that is doing nothing.

## Impact

This does not affect any development that imports `Init` — the names are taken
there, and no existing Lean code is retroactively unsound. What it does break is
the *auditing* story, which is exactly where it matters:

* `#print axioms` is the standard way to establish that a proof rests only on
  `propext` / `Classical.choice` / `Quot.sound`. Here it reports nothing at all.
* `leanchecker` (and, by the same reasoning, `lean4checker`, which reuses the
  kernel) is the standard way to detect "environment hacking" in a submitted
  `.olean`. It accepts this one.
* Consequently, a Lean artifact from an untrusted source cannot be validated by
  those two tools alone. Reviewing whether any module carries `prelude` is a
  necessary additional check, and to my knowledge is not part of anyone's
  documented workflow.

The kernel's `Nat` extension is documented as a trust assumption in the sense
that GMP is trusted to implement arithmetic; it is *not* documented that the
extension will apply itself to an unrelated declaration that happens to share a
name.

The counter-argument, and the reason this was dismissed when Breitner raised it,
is that a module which redefines `Nat` has replaced part of the system rather
than made use of it: the kernel's arithmetic extension is a *specification* that
the ambient environment is expected to satisfy, in the same way that
`kernel/quot.cpp` expects a particular `Eq`. The difference is that `quot.cpp`
actually *checks* its expectation (`check_eq_type`) before arming the feature,
and the `Nat` extension does not. So the disagreement is really about whether an
unchecked precondition counts as a soundness bug, not about the facts.

## Suggested remedies

Any of these closes it:

1. Have the kernel record, at the point the `Nat` extension is installed, that
   `Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, … have their expected declarations
   (shapes and bodies), in the style of `check_eq_type` in `kernel/quot.cpp`,
   which already validates `Eq` before enabling quotients. This is the closest
   fit to existing kernel practice.
2. Gate the extension on an explicit environment flag set by an `init_nat`-style
   command, mirroring `init_quot` / `is_quot_initialized`.
3. Failing either, make `prelude` modules visible to auditing tools — e.g. have
   `leanchecker` refuse, or loudly report, modules whose transitive imports do
   not reach `Init`.

## Negative results from the same audit

Recorded so the search is not repeated:

* **Universe levels are sound.** A fuzzer over 880 randomly generated level
  expressions in `u, v, w` (774,400 ordered pairs, 84,242 accepted by
  `Lean.Kernel.isDefEq`) compared the kernel's verdict against denotational
  equality on a `6³` box of assignments. **Zero** false positives; 162 pairs
  showed the known `imax` *incompleteness* (kernel rejects a semantically valid
  equation), which is not a soundness problem. Reading `kernel/level.cpp`
  agrees: every rewrite in `mk_max` / `mk_imax` / `normalize` is a semantic
  identity, and `is_equivalent` only ever concludes equality from syntactically
  identical normal forms.
* **Positivity and universe checks reject the classical paradoxes.** Direct and
  non-strictly-positive recursion, non-strict positivity laundered through a
  plain `def`, a `structure`, an `@[irreducible] def`, an `opaque`, `Subtype`,
  `Sigma`, `Quot`, and a mutual block; plus `Type`-in-`Type` via an `inductive`
  and via a `structure` field. All rejected, most by the kernel rather than the
  elaborator.
* **`isDefEq` never contradicted the kernel's own `whnf`.** A pool of 100 closed
  `Bool`-valued terms — honest projections, projections with 32-bit-truncating
  indices, projections carrying a *mismatched* `proj_sname`, `Nat.beq`/`Nat.ble`
  at accelerator boundaries, `Quot.mk`/`Quot.lift`, `Bool.rec`, and `Eq.rec`
  including K-like reduction — produced 3,354 ordered pairs whose kernel `whnf`
  values differ. `Lean.Kernel.isDefEq` accepted **none** of them. (Had it
  accepted one, `rfl : a = true` and `rfl : b = false` would both typecheck
  while `a ≡ b`.)
* **Compiler/kernel differential test found no divergence.** 72 closed
  `Bool`-valued terms over `String` (including UTF-8 boundary and out-of-range
  `Pos` cases), `Char`, `Nat` accelerator edge cases (`gcd 0 0`, `n / 0`,
  `n % 0`, `log2 0`, `0 ^ 0`, `2⁶⁴` boundaries), `Int` division variants,
  `UInt8/32/64`, `BitVec`, `List` and `Array` were evaluated both by
  `Lean.Kernel.whnf` and by the compiler via `Meta.evalExpr`. All agreed.
* **`Expr.proj` index truncation ([lean4#12746](https://github.com/leanprover/lean4/issues/12746)) is applied uniformly.** `infer_proj`
  and `reduce_proj` both truncate `size_t → unsigned`, so `proj S (2^32) e` is
  merely a verbose spelling of `proj S 0 e`; typing and reduction stay
  consistent and I could not build a type confusion from it.

## Hardening observations (not reachable as found)

* `equiv_manager::is_equiv_core` (`kernel/equiv_manager.cpp:103`) and
  `type_checker::is_def_eq_core` (`kernel/type_checker.cpp:1101`) compare `Proj`
  nodes on `proj_idx` alone and **do not compare `proj_sname`**, unlike
  `expr_eq_fn::apply` (`kernel/expr_eq_fn.cpp:90-94`) which does. Confirmed
  observable: `Kernel.isDefEq (proj Pair 0 x) (proj Other 0 x)` returns `true`.
  `reduce_proj_core` likewise ignores the structure name. This is currently
  unreachable in a well-typed term because `infer_proj` rejects a mismatched
  `proj_sname`, but the three sites disagreeing is fragile.
* `Lean.addDecl` accepts an `inductive` declared with `numParams = 2^32` and
  silently records `numParams = 0` (`m_nparams` is `unsigned` in
  `kernel/inductive.cpp`). The truncation is uniform, so no type confusion
  followed, but the declaration should be rejected rather than silently
  rewritten.
* `environment::add_opaque` omits the `check_no_metavar_no_fvar` call on the
  value that `add_definition` and `add_theorem` both perform. Currently harmless
  because `infer_type_core` rejects metavariables and unknown free variables
  anyway.

## For contrast: the already-documented loophole

`Shenanigans/EscapeHatches/Lean/NativeDecide.lean` derives `False` from
`@[implemented_by]` plus `native_decide`. This is the *known* trust boundary —
`Lean.reduceBool`'s docstring warns about it — and, unlike the `Nat` accelerator
hole, it is visible: on `4.32.0` `#print axioms` reports a generated
`…native_decide.ax_1_1` axiom. It is included only to show what a properly
*tracked* unsoundness looks like next to an untracked one.
