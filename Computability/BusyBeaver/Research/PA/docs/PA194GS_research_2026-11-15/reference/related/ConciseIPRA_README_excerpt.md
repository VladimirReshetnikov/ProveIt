# Concise presentations of intuitionistic primitive recursive arithmetic

This project collects the research packages that look for a very small
complete presentation of a theory bi-interpretable with full first-order
intuitionistic primitive recursive arithmetic (iPRA), and the Lean
formalization of the most concise of them.

**The article:** [concise_ipra.pdf](https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/main/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/concise_ipra.pdf)

- [`docs/Article/`](docs/Article/) is the unified article
  ([`concise_ipra.pdf`](https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/main/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/concise_ipra.pdf)): the
  written mathematics of all delivered packages merged into eleven chapters,
  each result stated and proved once. New proposals are integrated there.
- [`Artifacts/`](Artifacts/) holds the executable part of the delivered
  packages, one directory each: the Python proof checkers, certificates,
  fixtures and evidence. Their written reports are merged into the article
  and are not kept separately (they remain in the history of this
  repository). Frozen copies of other packages' sources and the larger
  matched controls that a package's own checkers supersede were deleted.
- `Lean/` is the formalization (see [Lean formalization](#lean-formalization)).

## The question

Every package measures a *complete standalone proof checker*: one Python
module that reads a JSON certificate and accepts exactly the theorems of the
presented calculus. The size coordinates are significant tokens, AST nodes and
UTF-8 bytes of the source after `ast.unparse` normalization (CPython 3.12.14);
gzip sizes are reported for information only. A presentation qualifies only if
its ordinary realization is bi-interpretable with iPRA with both numerical
domains whole, equality actual, and both composites the identity graph `x = y`.

## The native scalar core

All of the smallest checkers implement one calculus, the *native scalar core*
(the "Choice-DI calculus" of the reports). Its inventory is short.

**Terms.** One numerical sort:

    t ::= x | 0 | S(t) | I(n, a; u.h)

where only `u` is bound in `h`. The iterator satisfies

    I(0, a; u.h)    = a
    I(S(n), a; u.h) = h[I(n, a; u.h)/u]

**Formulas.** `A ::= (s = t) | Q_y A | D_{x,y} A`, with the designated
contradiction `0 = S(0)`. The ordinary readings are

    Q_y B(y)       :=  B(0) → ∀y B(y)
    D_{x,y} B(x,y) :=  ∃x (B(x,0) → ∀y B(x,y))

**Rules.**

| Rule | Premises | Conclusion |
| --- | --- | --- |
| Hyp | `A` retained in `Γ` | `Γ ⊢ A` |
| Tr | `Γ ⊢ s = t`, `Γ ⊢ F(s)` | `Γ ⊢ F(t)` for every native template `F` |
| QE | `Γ ⊢ Q_y B(y)`, `Γ ⊢ B(0)` | `Γ ⊢ B(t)` |
| DE | `Γ ⊢ D_{x,y} B`, and `Γ, Q_y B(b,y) ⊢ A` with `b` fresh | `Γ ⊢ A` |
| DI, case | `Γ, B(t,0) ⊢ B(t,S z)` with `z` fresh | `Γ ⊢ D_{x,y} B(x,y)` |
| DI, progress | `Γ, E(t,z) ⊢ E(t,S z)` with `z` fresh, `E` a literal equation | `Γ ⊢ D_{x,y} E(x,y)` |

together with the two computation equations. No other logical, successor,
equality or induction axiom is primitive: reflexivity comes from
`I(0, t; u.0) = t`, implication, conjunction, disjunction and the two
quantifiers are macros over `D` built from the selector
`C(v, a, b) := I(v, a; u.b)`, and numerical case distinction and induction for
equations are derived rules.

**Two rules can be weakened.** The Lean kernel (see
[Lean formalization](#lean-formalization)) takes weaker forms of Tr and of DI
by progress as primitive, and proves that the derivable sequents are the same
(`iprf_iff_nprf`):

| Rule | Premises | Conclusion |
| --- | --- | --- |
| Tr, one term | `Γ ⊢ s = t`, `Γ ⊢ h(s) = u` | `Γ ⊢ u = h(t)` |
| QI, progress | `Γ, E(z) ⊢ E(S z)` with `z` fresh, `E` a literal equation | `Γ ⊢ Q_y E(y)` |

- *Transport in one term.* Transport has one term template `h` and a crossed
  conclusion. Reflexivity, symmetry, transitivity and congruence are each one
  application of the rule, with no side condition: reflexivity transports
  `I(0, t; u.u) = t` along itself. Transport in an equation template,
  `a(s) = b(s)` to `a(t) = b(t)`, is two applications, and transport never has
  to look inside a `Q` or a `D`: for a compound template it follows by
  induction on the template from QE, DE and DI by cases. This is the rule of
  [`one_context`](Artifacts/one_context/).
- *Direct closure.* Progress introduces the closure `Q_y E(y)` itself, with
  no existential witness and one bound variable fewer; the witnessed rule
  follows by QE and DI by cases. This is the proposal of
  [`direct_closure`](Artifacts/direct_closure/) and
  [`direct_closure_qprogress`](Artifacts/direct_closure_qprogress/).

- *No literal-zero source, for free.* The source `s` of a transport may be
  restricted to terms other than the literal `0`, and for the one-term rule
  this costs nothing (`oprf_iff_nprf`): a constant template reverses any
  equation in one step, because the major premise can be
  `I(0, 0; u.0) = 0`; a term provably zero is joined to the anchor
  `I(0, 0; u.0)` by one transport of `I(0, p; u.0) = p`; and transport along
  `0 = t` is transport along `t = 0` followed by transitivity. No induction,
  numerical case distinction or successor computation is used; the argument
  needs the first computation equation and the rule itself (class `OKernel`).
  This is the theorem of
  [`one_sided_transport`](Artifacts/one_sided_transport/), and it lets the
  source of an elimination select its major premise
  ([`source_dispatch`](Artifacts/source_dispatch/)).

- *One introduction rule.* The two introductions can be replaced by one,

      DI:  Γ, B(t, η) ⊢ B(t, S z)  with z fresh   ⟹   Γ ⊢ D_{x,y} B

  where `η` is `z` if `B` is a literal equation and `t` is the literal `0`,
  and `0` otherwise. That calculus has seven rules and derives the same
  sequents (`wprf_iff_nprf`). This is the idea of
  [`witness_rule`](Artifacts/witness_rule/); the case it removes, an equation
  by cases at the witness `0`, is recovered at the witness `I(0, 0; u. 0)`.

- *All together.* One-term transport at sources other than the literal `0`,
  with the single introduction, is a calculus of seven rules, `MPrf`: Hyp,
  the two computation equations, Tr, QE, DE and DI. It derives the same
  sequents as the calculus of the reports (`mprf_iff_iprf`), and full
  transport is recovered in it without induction.
- *Six rules, closed under substitution.* Eval and the diagonal introduction
  combine: hypothesis, reflexivity, Eval, QE, DE and the introduction whose
  mode is read off the diagonal shape. This calculus, `SPrf`, has no
  computation axiom, no template, no normalization and no test on a witness or
  on a transport source; it derives the same sequents as the kernel
  (`sprf_iff_nprf`) and is closed under substitution by a direct induction on
  derivations (`SPrf.subst`). None of the packages states this combination.
- *Five rules, with clauses in place of `Q`.* The formulas are equations and
  `D` only. A context is a list of clauses `[A; y.B(y)]`, read
  `A → ∀y B(y)`, an ordinary assumption `A` being `[0 = 0; v.A]`. The rules are
  Refl, Eval, Use (from `A` infer `B(t)` for a clause of the context), Elim
  (open `D_{x,y} B` at a fresh `b`, which adds the clause
  `[B(b,0); y.B(b,y)]`) and Intro. This calculus, `CPrf`, derives only
  `Q`-free formulas from `Q`-free clauses (`CPrf.qfree`), agrees with the
  kernel on `Q`-free sequents (`cprf_iff_nprf_of_qfree`), and derives the
  `Q`-free form of every native sequent, with `Q_y B` rewritten as `D_{x,y} B`
  with `x` unused (`cprf_iff_nprf`). This is the raw clause calculus of
  [`raw_clausal`](Artifacts/raw_clausal/) and its successors.
- *One body per context entry.* A clause needs no antecedent field. In
  `OBPrf` a context entry is one body `B(y)`, read `B(0) → ∀y B(y)`, which is
  the kernel formula `Q_y B`; Use infers `B(t)` from `B(0)`, Open adds the
  body `B(b, y)`, and the assumption of Intro is stored as the gate body
  `gate_v A`, the formula `A` with `sel(v, 0, ·)` on both sides of its
  equation. `obprf_iff_nprf : OBPrf (Γ.map gb) A ↔ NPrf Γ A` on `Q`-free
  sequents, `obprf_unQ_iff_nprf` in general, and `obprf_iff_cprf` against
  `CPrf` (`NativeOneBody`). An opened clause of `CPrf` is already one body,
  so the translation is literal except where an assumption is used. There
  the gate body gives `gate_1 A` by Use, and `A` follows by conversion along
  `sel(1, 0, s) = s` under the binders of `A`; conversion at a binder needs
  access one level down, so the two are proved together by induction on the
  number of binders (`OBPrf.conv`, `OBPrf.access`). No cut or weakening of
  `OBPrf` is used. This is the calculus of
  [`one_body`](Artifacts/one_body/).
- *Evaluation at the discharge.* The two cases of Eval and the elimination
  of `D` fuse into one rule. `E3Prf` has Use, Intro and Discharge: from
  `D_{x,y} B`, and from `E` and `F` under the clause of a fresh `b`, infer
  `ρ_E(F)` if `b` does not occur in it, where `ρ` is one evaluation step:
  `ρ_{s = t}(I(0, s; u.h) = r)` is `r = t`,
  `ρ_{I(c, a; u.h) = t}(I(S c, a; u.h) = r)` is `r = h[t/u]`, and `ρ_E(F)` is
  `F` otherwise. Its graph `Rho` is functional and total
  (`Rho.functional`, `Rho.total`). `e3prf_iff_vprf : E3Prf Γ A ↔ VPrf Γ A`
  on every clause context, hence `e3prf_iff_nprf_of_qfree` with the
  reflexivity clause (`NativeEvalDischarge`). An elimination is a discharge
  whose auxiliary formula is `D_{x,y} (0 = 0)`, which is compound and selects
  the identity; an Eval step is a discharge of that formula whose branches
  are its premises moved under the fresh variable, so the translation
  carries a renaming and an extension of the context through its induction.
  This is the raw calculus of
  [`evaluation_discharge`](Artifacts/evaluation_discharge/).
- *Five rules, closed under substitution.* The clause calculus with the
  diagonal introduction in place of the witness-tested one is `KPrf`: Refl,
  Eval, Use, Elim and Intro on Eq/D formulas with clause contexts. No rule
  inspects a witness, a transport source or a normal form, so it is closed
  under substitution by a direct induction (`KPrf.subst`); it agrees with the
  kernel on `Q`-free sequents (`kprf_iff_nprf_of_qfree`). None of the packages
  states this combination.
- *Four rule families.* If a clause may have no antecedent, reflexivity need
  not be a rule: every context contains the fixed clause `[; y. y = y]`, an
