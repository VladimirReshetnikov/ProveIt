# Mathematical approaches: how close is Lean to Girard/Hurkens?

Nothing here is an implementation defect. This directory asks the *mathematical*
question: does Lean's type theory admit a paradox in the tradition of Girard,
Hurkens, or Coquand–Paulin? Every result is machine-checked, and the two headline
theorems report **no axioms at all**.

**Short answer: no, and the reason is precise and worth writing down.** Coquand's
counterexample needs three ingredients — impredicativity, a universe type, and
non-strictly-positive inductive types. **Lean has the first two outright.** Only
the third is denied. The two files here pin that down, both machine-checked with
`#print axioms` reporting *no axioms at all*.

## `HurkensBlocker.lean` — where Hurkens stops, exactly

Lean's function-type rule is `(A → B) : Sort (imax u v)`. That single rule is
impredicative in one direction and predicative in the other, and Hurkens needs
both directions:

* **Impredicativity is present, and is as strong as System U in this direction.**
  Because `imax u 0 = 0`, a quantifier landing in `Prop` *stays* in `Prop`, no
  matter how large the domain. Measured:

  ```
  fun X p => ∀ (x : X), p x : (X : Type 5) → Pw X → Prop
  ```

  Quantifying over `Type 5` still yields a `Prop`.

* **But `Prop` is not closed under powerset.** The *type of predicates* is
  `X → Prop : Sort (imax u 1) = Sort (max u 1)`, which is never `Prop`. So
  `Pw True : Type`.

Hurkens' `U := ∀ X : Prop, ((℘℘X → X) → ℘℘X)` is therefore forced up to `Type`,
and the self-application `σ s := s U (…)` — which must instantiate the bound
`X : Prop` at `X := U` — cannot be typed. Lean's report:

```
error: Function expected at s
  but this term has type U
```

That is the whole story: **Lean's impredicativity is one-directional**, and
Hurkens needs a universe closed under both quantification *and* powerset.

## `CoquandPaulin.lean` — the positivity guard is load-bearing

With impredicativity and a universe type both available, the *only* thing left
standing between Lean and Coquand's paradox is strict positivity. This file
proves that, axiom-free:

```lean
def Phi (α : Type) : Type := (α → Prop) → Prop      -- positive, not strictly positive

theorem coquand_paulin
    (A : Type) (introA : Phi A → A) (matchA : A → Phi A)
    (beta : ∀ x, matchA (introA x) = x) : False
```

```
'coquand_paulin' does not depend on any axioms
```

A retraction of `Phi A` into `A` is all it takes. The proof is the classical one:
`introA` is injective by `beta`; `x ↦ (· = x)` injects `A` into `A → Prop`;
composing gives an injection of the powerset of `A` into `A`; then Russell's set
`D x := ∃ P, f P = x ∧ ¬ P x` gives `D (f D) ↔ ¬ D (f D)`.

The companion theorem states the same phenomenon without the operator:

```lean
theorem no_powerset_retract (A : Type) (g : (A → Prop) → A) (g' : A → (A → Prop))
    (hg : ∀ p, g' (g p) = p) : False
```

also axiom-free.

**And this is exactly the hypothesis the kernel denies.** Writing

```lean
inductive Bad where | mk : Phi Bad → Bad
```

gives

```
(kernel) arg #1 of 'Bad.mk' has a non positive occurrence of the datatypes being declared
```

— from the *kernel*, not the elaborator. `Bad` would supply `introA := Bad.mk`
together with `matchA` and `beta` from its recursor, and `coquand_paulin` would
then yield `False` outright. So the positivity check is not defensive
belt-and-braces; it is the single load-bearing guard, and its necessity is
provable inside Lean.

## Results, and a correction

See [`Findings.md`](Findings.md) for the full account. Headlines:

* **No paradox** — expected.
* **A correction to the usual framing.** Lean's consistency is
  *not* a settled theorem: Carneiro's Conjectures 2.7 and 2.9 were **downgraded
  from theorems to conjectures**, because the stratification of the typing
  judgment used to break the mutual induction between typing and definitional
  equality does not and cannot respect substitution. The model construction
  stands; the metatheoretic bridge has an acknowledged gap, sitting exactly where
  the extra kernel rules live.
* **Verified: `Expr.proj` is strictly stronger than the recursor.** For the
  kernel-level inductive `I2 (a : Sort u) : Sort u | mk : a → I2 a`, `I2.rec` is
  restricted to `Prop` motives while `Expr.proj` eliminates into `Sort v`. Sound,
  but it refutes the "proj = recursor application" desugaring that Lean4Lean's
  specification of `Expr.proj` relies on. See `ProjBeyondRecursor.lean`.
* **Verified: the kernel's `is_def_eq` is not transitive** — `A ≡ B`, `B ≡ C`,
  `A ≢ C`. Incompleteness, the safe direction, and already implied by the thesis's
  undecidability result.
* The `Acc` + proof-irrelevance anomaly is **self-refuting**: its precondition is
  the negation of its own hypothesis (`acc_irrefl`, axiom-free).
