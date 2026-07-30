# Results of the mathematical line

**No paradox was found.** That was the expected outcome. But the line produced
three things worth keeping, two of them verified directly and one of them a
correction to how Lean's metatheoretic status is usually stated.

## 1. Correction: Lean's consistency is *not* a settled theorem

It is commonly said — and I said it myself while setting this investigation up —
that "Lean's core theory has a consistency proof relative to ZFC + countably many
inaccessibles (Carneiro, *The Type Theory of Lean*)". **That overstates the
record.**

Conjectures 2.7 and 2.9 were **downgraded from theorems to conjectures** in later
work, because of an error in a technical lemma: the proof constructs a
stratification of the typing judgment in order to break the mutual induction
between typing and definitional equality, and *that stratification does not and
cannot respect substitution*.

So the set-theoretic model construction stands, but the metatheoretic bridge
between it and the typing judgment has an acknowledged gap — and the gap sits
exactly at the interaction between typing and definitional equality, which is
precisely where the extra kernel rules live. That is a more interesting state of
affairs than "proved consistent", and it should be stated accurately.

Related published result, directly on the `Acc` + proof-irrelevance line:
Abel and Coquand, [*Failure of Normalization in Impredicative Type Theory with
Proof-Irrelevant Propositional Equality*](https://arxiv.org/pdf/1911.08174) —
normalisation genuinely fails in this setting. The anomalies below are not
folklore; they are the expected shape.

## 2. Verified: `Expr.proj` is strictly stronger than the recursor

`ProjBeyondRecursor.lean`. Feeding the kernel this declaration directly:

```lean
I2 (a : Sort u) : Sort u  |  mk : a → I2 a
```

(the elaborator *frontend* rejects it — "resulting universe may be `Prop` for some
parameter values" — but it is a legitimate kernel-level inductive) produces:

```
@I2.rec : ∀ {a : Sort u_1} {motive : I2 a → Prop}, …      ← motive restricted to Prop
proj eliminates into: a                                    ← Sort v, parametric
eta-struct isDefEq (x) (I2.mk a x.1) = true
I2.out : (a : Sort u_1) → I2 a → a
'I2.out'    does not depend on any axioms
'I2.eta'    does not depend on any axioms
'I2.out_mk' does not depend on any axioms
```

Because `u` *might* be `0`, `elim_only_at_universe_zero` (inductive.cpp:479)
conservatively restricts `I2.rec` to `Prop` motives. But `is_non_rec_structure`
(inductive.cpp:27) asks only for 1 constructor / 0 indices / non-recursive, and
`infer_proj` (type_checker.cpp:221) guards the field universe only when the
structure's type is *syntactically* `Sort 0`. So `Expr.proj` — and structure eta —
apply at a parametric level, eliminating into `Sort v` where **no recursor with
that motive exists**.

**It is sound.** `check_constructors` (inductive.cpp:439) admits a field at level
`m` in an inductive at level `l` only if `is_geq l m` holds universally or `l` is
syntactically `0`. Here `m = l = u`, so any substitution making the structure a
`Prop` also makes the field a `Prop`: `proj` never carries data out of a `Prop`.

**But it refutes a specification.** The desugaring "a projection is equivalent to
an application of the recursor" is false for this type — and that desugaring is
what Lean4Lean's specification of `Expr.proj` rests on
([arXiv:2403.14064](https://arxiv.org/html/2403.14064v3)). This is a gap between
the kernel primitive and its intended meaning, not an unsoundness.

## 3. Verified: the kernel's `is_def_eq` is not transitive

With `R a b := a+1 = b` on `Nat`, `Racc : ∀ n, Acc R n`, and
`cnt : Acc R x → Nat` defined by `Acc.rec` at `motive := fun _ _ => Nat` (a
genuine large elimination of a `Prop`), for closed `A B C : Acc R 3 → Nat`:

```
A := fun h => cnt h        B := fun _ => cnt (Racc 3)        C := fun _ => 3

[KERNEL ACCEPT] A =?= B
[KERNEL ACCEPT] B =?= C
[KERNEL REJECT] A =?= C
```

`A =?= B` succeeds without ever unfolding `cnt`: both sides are applications of
the same definition, so the optimisation at type_checker.cpp:917-929 tries
`is_def_eq_args`, the indices match, and the *proof* arguments are identified by
`is_def_eq_proof_irrel`. `A =?= C` has no such shortcut — `cnt h` must delta-unfold
to a **stuck** `Acc.rec F h` (`h` is an fvar, `Acc` is not a K-target since
`Acc.intro` has two fields, and `to_cnstr_when_structure` explicitly refuses
structure eta for `Prop`s), so irrelevance never propagates into the recursor.

This is **incompleteness, the safe direction**: Lean's *declared* judgmental
equality is a congruence and does contain `A ≡ C`, and `A = C` is recoverable
propositionally by chaining. The kernel simply decides a strictly smaller
relation. Carneiro's thesis §3.1 already establishes that definitional equality is
undecidable, by this very mechanism.

## 4. Why the `Acc` anomaly cannot escape

The anomaly can be pushed to a defeq chain giving `n ≡ n+1`, and hence
`cnt0 h = (cnt0 h).succ`, hence `¬ Acc R0 ()` — axiom-free, but an independently
*true* theorem, since `R0 := fun _ _ => True` is total and therefore not
well-founded.

It cannot be made to bite in a consistent context. The only way to make `Acc.rec`
grow is the "dishonest eta" `h ≡ Acc.intro x (fun y _ => h)`, which needs
`Acc r y ≡ Acc r x` for a *fresh* `y`, and hence `y ≡ x`, and hence an inhabitant
of `r x x`. But that is impossible for an accessible `x`:

```lean
theorem acc_irrefl {α : Sort u} {r : α → α → Prop} {x : α} (hx : Acc r x) : r x x → False :=
  Acc.rec (motive := fun z _ => r z z → False) (fun z f ih hz => ih z hz hz) hx
```

axiom-free. **The anomaly's precondition is the negation of its own hypothesis.**

## 5. The frontier map

Keeping two questions apart, since conflating them is how one overclaims:

* **(M)** is the rule true in the intended model? A failure here is unsoundness.
* **(A)** is the kernel's *decision procedure* complete/transitive/terminating? A
  failure in the incomplete direction is harmless.

| Rule | (M) | (A) |
| --- | --- | --- |
| β, ζ, δ, ι; function eta | valid | covered |
| `imax` level arithmetic, no cumulativity | valid | covered |
| Definitional proof irrelevance | valid (`Prop` is subsingleton-valued) | covered |
| Strict positivity | valid, and deliberately *more* conservative than needed | covered |
| Subsingleton large elimination, incl. `Acc` | valid — in the model the proof slot is inert: `rec_acc(A,R,e) = (x ↦ (h ↦ F(x)))`, `F` independent of `h` | covered |
| K-like reduction | valid; the kernel's version is *narrower* than the thesis rule | covered |
| `Quot`, incl. `Quot r : Prop` at `u = 0` eliminating into `Type` | valid — `⟦α⟧ ⊆ {∅}` so the quotient has ≤1 element and `lift` is trivially well-defined | covered |
| **Eta for structures** | valid (surjective pairing) | **not in the 2019 thesis** |
| **Eta for unit-like types** | valid — see below | **not in the 2019 thesis** |
| **Kernel `is_def_eq` as an algorithm** | n/a | **gap, and demonstrably non-transitive (§3)** |

Unit-like eta is valid because `is_valid_ind_app` (inductive.cpp:338) compares the
constructor's conclusion parameters against the parameter fvars *structurally*, so
with `nindices == 0` the sole constructor is forced to be `I.mk : ∀ p⃗, I p⃗` —
total. Hence `I p⃗ ≅ {∗}` for every `p⃗`, at every universe. The near-miss is
instructive: a 0-field type *can* be empty, but only with **indices**
(`inductive W3 : Nat → Type | mk : W3 0` makes `W3 1 → False` provable), and
`nindices == 0` excludes exactly that.

## 6. Which ingredient each classical paradox is denied

| Paradox | What Lean denies it |
| --- | --- |
| **Girard** (System U) | a *second* impredicative sort. `∀ α : Type u, F α` computes to `Sort (imax (u+2) (u+1)) = Type (u+1)` — the universe bumps. There is exactly one impredicative sort and it is `Prop`. |
| **Hurkens** | `Prop` closed under powerset. Denied arithmetically: for `X : Prop`, `X → Prop : Sort (imax 0 1) = Type 0`. Impredicativity lives only in the codomain (`imax u 0 = 0`). |
| **Coquand–Paulin** | non-strict positivity — and only that. `CoquandPaulin.lean` proves the guard load-bearing, axiom-free. |
| **Reynolds** | set-theoretic semantics for polymorphism; irrelevant to a type theory with a set-theoretic model. |
| **Berardi** | harmless: it derives proof irrelevance, which Lean already has definitionally. |
| **Chicli–Pottier–Simpson** | proof-relevant quotients. Lean's `Quot` at `u = 0` is a definitional isomorph of a subsingleton. |

The unifying statement: **Lean pairs impredicativity with proof irrelevance and
never with proof relevance.** Every paradox in this family needs impredicativity
*plus* a data-carrying elimination out of the impredicative sort, and
`elim_only_at_universe_zero` is exactly that barrier. The two constructions that
look like exemptions — `Acc` and `Quot` — turn out to *satisfy* the subsingleton
criterion rather than bypass it.
