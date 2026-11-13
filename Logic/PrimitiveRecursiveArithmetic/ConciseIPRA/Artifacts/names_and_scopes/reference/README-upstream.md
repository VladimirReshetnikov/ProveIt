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
  ordinary assumption is `[; v.A]`, and Use takes the antecedents of a clause,
  none or one. With Eval, Elim and Intro this is `VPrf`; with the reflexivity
  clause in the context it derives what `CPrf` derives (`vprf_iff_cprf`,
  `vprf_iff_nprf_of_qfree`). This is the calculus of
  [`uniform_clauses`](Artifacts/uniform_clauses/).
- *One computation rule.* The zero computation `I(0, a; u.h) = a` can be
  moved from the rules into the syntax. Call a term zero-normal if no iterator
  in it has the literal `0` as its counter, and let every substitution of a
  rule be followed by the contraction of such iterators. The kernel without
  the zero computation rule, `NZPrf`, has seven rules, derives only
  zero-normal formulas from zero-normal hypotheses (`NZPrf.normal`), and
  derives the normal form of a sequent exactly when the kernel derives the
  sequent (`nzprf_iff_nprf`). Reflexivity then comes from successor
  computation: `I(S 0, t; u.u) = t` is an instance, because its right-hand
  side `I(0, t; u.u)` is contracted. This is the proposal of
  [`zero_normal`](Artifacts/zero_normal/); the normalization is part of the
  specification of the calculus.
- *No computation rule.* Both computations can be moved into the syntax.
  Every term has a full normal form, in which no iterator has a counter `0`
  or `S c`. The normalizer is defined by evaluation and needs no termination
  argument: `Tm.nbe t ρ` evaluates `t` in an environment of terms by
  structural recursion on `t`, and the iterator is evaluated by a recursion
  on the value of its counter, which unfolds a numeral prefix and leaves a
  neutral counter in place (`Tm.recV`); `Tm.full t` is the value in the
  identity environment. Its laws are four lemmas about evaluation (renaming
  of the target and of the source, substitution, composition), from which
  idempotence and the coherence of normalization with substitution follow
  (`Tm.full_subst_congr`, `NFm.full_subst_congr`); the kernel proves a term
  equal to its normal form (`NPrf.eqFull`). On full normal forms the two
  sides of each computation equation are the same term, so the kernel
  without either computation rule, with reflexivity in their place, derives
  the full normal form of a sequent exactly when the kernel derives the
  sequent (`FNPrf`, `fnprf_iff_nprf`). This is the kernel form of
  [`full_normalization`](Artifacts/full_normalization/) and
  [`computation_normal`](Artifacts/computation_normal/).
- *Six rules on full normal forms.* With no computation rule and one
  introduction whose mode is read off the matrix and the witness, the
  calculus is Hyp, Refl, Tr, QE, DE and that introduction (`F6Prf`,
  `f6prf_iff_nprf`). QI by progress is the introduction of `D_{x,y} E(y)` at
  the literal `0` followed by DE. DI by cases for an equation at a witness
  with the normal form `0` cannot be made at that witness, which selects
  progress, and on full normal forms no other term is provably `0`; it is
  made in two steps (`F6Prf.dIZero`): with `T(x) = sel(x, 0, 0)`, the formula
  `D_{x,y} B(T(x), y)` is introduced at the witness `1` in case mode, opened
  at a fresh `b`, and `D_{x,y} B` is introduced at the neutral witness
  `T(b)` from the opened closure. This is the calculus of
  [`full_normalization`](Artifacts/full_normalization/) and
  [`computation_normal`](Artifacts/computation_normal/).
- *Opening with an inferred witness.* On full normal forms the elimination
  of `D_{x,y} B` need not be told anything: it reads its witness off the
  matrix. If `B(b, 0)` is literally `0 = 0` and `B(b, 1)` is literally
  `b = r` at the fresh `b`, the closure is opened at `r`, and otherwise at `b`
  (`NFm.owit`). With this rule in place of DE the kernel on full normal forms
  is `FOPrf`, and it derives the full normal form of a sequent exactly when
  the kernel derives the sequent (`foprf_iff_nprf`). Soundness: the selected
  rows make the closure at `b` yield `b = r`, and the closure at `r` follows
  by transport (`NPrf.owitQ`). Completeness translates a kernel derivation
  under an arbitrary substitution, and at DE sends the fresh variable to the
  selected witness of the normalized matrix, whatever it is
  (`NPrf.toFO`); the test is not stable under substitution, and no case
  distinction on it is needed. This is the rule of
  [`inferred_witness`](Artifacts/inferred_witness/),
  [`deterministic_opening`](Artifacts/deterministic_opening/),
  [`first_instance`](Artifacts/first_instance/) and
  [`clause_discharge`](Artifacts/clause_discharge/), on the kernel.
- *Substitution for a variable only.* On full normal forms one equality rule
  suffices, with no template and no joining of two equations: from `x = t`,
  for a variable `x`, and `u = v` infer `v = u[t/x]` (`VSPrf`,
  `vsprf_iff_nprf`). Transport from `s = t` and `h(s) = u` to `u = h(t)` is
  recovered by a naming packet: the matrix
  `sel(y, 0, sel(P(y), x, h(x))) = sel(y, 0, sel(P(y), t, u))`, with `P` the
  parity iterator, has the rows `0 = 0`, `h(x) = u` and `x = t` at
  `y = 0, 1, 2` as full normal forms; `D` of it is introduced at the witness
  `s` by numerical cases on a parity, and opened at a fresh `b`, whose rows
  give `h(b) = u` and `b = t`, so that one substitution for `b` gives
  `u = h(t)` (`VSPrf.packet`). This is the rule of
  [`variable_substitution`](Artifacts/variable_substitution/). On raw terms the
  rows are not literal, and the nearest statement there is Param above. The
  source can be restricted to the newest variable (`V0Prf`,
  `v0prf_iff_nprf`).
- *Equality at the discharge of a witness.* On full normal forms one rule,
  Name, replaces both transport and DE: from `D_{x,y} B`, and from `b = t` and
  `F` in the context opened at a fresh `b`, infer `F[t/b]`, provided it does
  not mention `b`. With `t = b` it is DE. The kernel then has six rules, Hyp,
  Refl, Name, QE, DI by cases and QI by progress (`NMPrf`, `nmprf_iff_nprf`).
  The naming packet gives `b = t` and `h(b) = u` in the opened context, and
  Name exports `h(t) = u`: transport without the crossing
  (`NMPrf.packet`). At the template `x` with a reflexive equation that is
  symmetry, and the transport of the kernel follows. This is the rule of
  [`witness_discharge`](Artifacts/witness_discharge/).
- *Five rules.* On full normal forms the two reductions above combine: Name
  in place of transport and DE, and one introduction in place of DI by cases
  and QI by progress. The calculus is Hyp, Refl, Name, QE and that
  introduction (`N5Prf`, `n5prf_iff_nprf`, `n5prf_iff_pra`), with lists of
  formulas as contexts and `Q` in the language: no computation rule, no
  transport, and no separate elimination of `D`. Among the calculi proved
  here whose contexts are formulas it has the fewest rules; the clause
  calculi also have five (`CPrf`, `ZCPrf`) or four families (`VPrf`, `ZVPrf`),
  with clauses in their contexts. This combination is not taken from a
  package.
- *Three rule families.* With clauses in the contexts the five rules become
  three families. `WDPrf` has formulas built from equations and `D` over full
  normal forms, clauses with at most one antecedent, the fixed reflexivity
  clause `[; y. y = y]`, and the rules Use, Intro and Name; Name opens
  `D_{x,y} B` by adding the clause `[B(b, 0); y.B(b, y)]`. There is no `Q`, no
  computation rule, no transport, no reflexivity rule and no separate
  elimination of `D`. `wdprf_iff_nprf` proves that the kernel derives a
  sequent exactly when `WDPrf` derives the full normal form of its `Q`-free
  form from the reflexivity clause and the corresponding assumptions, and
  `wdprf_iff_nprf_of_qfree` is the same statement on `Q`-free sequents. This
  is [`witness_discharge`](Artifacts/witness_discharge/) in its own form, and
  the calculus with the fewest rule families proved here.
- *Three rule families with an inferred witness.* `OCPrf` has the same
  formulas, clauses and reflexivity clause, and the rules Use, Intro and Open.
  Open has one premise fewer than Name and no parameter: from `D_{x,y} B` and
  a derivation of `A` under the clause `[B(r, 0); y.B(r, y)]` it infers `A`,
  where `r` is read off the rows of `B` at a fresh `b` (`b = r` if `B(b, 0)`
  is literally `0 = 0` and `B(b, 1)` is literally `b = r`, and `b` itself
  otherwise). `ocprf_iff_nprf` proves the same equivalence with the kernel
  as for `WDPrf`. Transport is recovered from a packet with the rows `0 = 0`,
  `x = T`, `H(x) = U`, on which Open selects `T`; ordinary elimination of `D`
  is not a derived rule, so kernel derivations are translated under an
  arbitrary substitution. This is
  [`inferred_witness`](Artifacts/inferred_witness/) and
  [`deterministic_opening`](Artifacts/deterministic_opening/) in their own
  form.
- *Three rule families with a deterministic discharge.* `XCPrf` has Use, Intro
  and Discharge: from `D_{x,y} B` and one derivation of `F` under the clause
  `[B(b, 0); y.B(b, y)]` it infers `F[r/b]`, with the same `r` read off the
  rows of `B`. The clause is opened at the fresh variable and the selected
  witness is substituted in the exported formula. Here the ordinary
  elimination of `D` is a derived rule, since the substitution does nothing
  to a formula that does not mention `b`; so `xcprf_iff_nprf` is proved by a
  rule-by-rule translation of the six-rule calculus `F6Prf`, and soundness by
  reading Discharge as Name at the selected witness. This is
  [`first_instance`](Artifacts/first_instance/) and
  [`clause_discharge`](Artifacts/clause_discharge/) in their own form.
- *Five rules with substitution for the newest variable.* `VCPrf` is the
  forward clause calculus of
  [`variable_substitution`](Artifacts/variable_substitution/): Refl, Sub, Use,
  Elim and Intro on full normal forms, with clauses `[A; y.B(y)]` in the
  context and no `Q`. Sub infers `v = u[t/x]` from `x = t` and `u = v` for the
  newest variable `x` only. That rule is not stable under weakening by a new
  variable, so derivations of `VCPrf` cannot be weakened or renamed;
  `vcprf_iff_nprf` is proved by translating the six-rule calculus `F6Prf`
  under an arbitrary renaming of the source, with a context invariant that is
  a membership and not a derivability (`Cl.Inv`, `F6Prf.toVC`).
- *Seven uniform rules, with another reading of `Q`.* `RPrf` is the calculus
  of [`uniform_progress`](Artifacts/uniform_progress/): hypothesis, the two
  computations, transport in an equation template, and QE, DE, DI whose mode
  is read off the root of the matrix alone. No rule looks at a witness, so
  substitution in derivations is a direct induction. The price is the meaning
  of `Q`: at a literal equation it is progressivity, `∀y (E(y) → E(S y))`.
  So `RPrf` is not the kernel on the same formulas; it is equivalent to it
  through a translation. `NFm.emb` pads every equation below a binder to a
  compound formula, and `rprf_emb_iff` proves that the kernel derives a
  sequent exactly when `RPrf` derives its translation. Equation induction
  and transport in arbitrary formulas are derived inside `RPrf`
  (`RPrf.eqInd`, `RPrf.leibniz`). The reading is faithful as well:
  `rprf_iff_rd` proves that `RPrf` derives a sequent exactly when the kernel
  derives its progressive reading, and every formula of `RPrf` is
  interderivable in `RPrf` with the translation of its reading
  (`REquivIn.emb_rd`). With `NEquiv.rd_emb` these are the two formula round
  trips, on all formulas and over arbitrary contexts.
- *The target-directed elimination.* `TQPrf` is `RPrf` with another
  elimination of `Q`, the rule of
  [`target_closure`](Artifacts/target_closure/): from `Q_y B` and `B(δ_B(t))`
  infer `B(t)`, where `δ_B(t)` is `r` when `B` is a literal equation and `t`
  is literally `S r`, and `0` otherwise. One target term is supplied and no
  orbit term. `tqprf_iff_rprf : TQPrf Γ A ↔ RPrf Γ A` proves that the two
  calculi derive the same sequents on the same formulas, so
  `tqprf_emb_iff` gives the equivalence with the kernel. `TQPrf` is stable
  under renaming and not under substitution.
- *One introduction rule, stable under substitution.* The single
  introduction above tests the witness for being the literal `0`, and a
  substitution can turn a witness into `0`. If instead the fresh variable is
  used exactly when the matrix is literally of the diagonal shape
  `I(y, y; u.h) = I(y, y; v.k)`, the test looks at the matrix alone, and
  substitution for the free variables neither creates nor destroys the shape.
  That calculus, `GPrf`, has seven rules, is closed under substitution by a
  direct induction (`GPrf.subst`), and derives the same sequents
  (`gprf_iff_nprf`). Progress for an arbitrary equation `s(y) = t(y)` is
  recovered through its diagonal lift `I(y, y; u.s) = I(y, y; u.t)` and the
  unconditional equation `sel(y, s(0), I(y, y; u.s(y))) = s(y)`. This is the
  calculus of [`diagonal_guard`](Artifacts/diagonal_guard/).
- *No template.* Transport can be replaced by a rule that is given no
  template at all: from `s = t` and `u = v` infer `v = R(u)`, where `R`
  replaces every occurrence of `s` in `u` by `t`, root first and in one pass
  (`TPrf`, `tprf_iff_nprf`). The rule cannot choose which occurrences to
  replace; transport in a chosen template `h` is recovered with the marker
  `M = I(0, s; u.K)`, whose step term `K` is a numeral larger than `h`, so
  that `h(M)` contains `M` at the template positions and nowhere else. This
  is the rule of [`template_free`](Artifacts/template_free/).
- *Substitution for a parameter.* Transport can also be replaced by the rule
  Param of [`parameter_substitution`](Artifacts/parameter_substitution/): from
  `s = t` and `u = r` infer `r = ψ(s, t, u)`, where `ψ` is `u[t/s]` if `s` is
  a variable, `t` if `u` is `s`, and `u` otherwise. A proper subterm is
  replaced only when the source is a variable (`PPrf`, `pprf_iff_nprf`).
  Transport in a template `h` is recovered under a fresh alias `b = s`, where
  Param at the variable `b` turns `h(b) = h(b)` into `h(b) = h(s)` and into
  `h(b) = h(t)`; the alias is discharged through
  `D_{x,y} (sel(y, s, x) = s)`, proved by cases with the witness `s` and
  eliminated at `y = 1` (`PPrf.aliasE`). The proof of completeness uses the
  variable case and joining at the root only, never the reversal. A
  substitution can turn a variable source into a compound one, so `PPrf` is
  closed under injective renaming (`PPrf.ren`) and not under substitution by a
  direct induction.
- *Substitution at the discharge of a witness.* Transport and DE can be one
  rule: from `D_{x,y} B`, and from `s = t` and `F(s)` in the context opened at
  a fresh `b`, infer `F(t)`, provided it does not mention `b`. With it in
  place of both, the kernel has seven rules (`SDPrf`, `sdprf_iff_nprf`). The
  closed theorem `D_{x,y} (I(0, 0; u.u) = 0)` is proved by cases from a
  computation; a discharge of it that does not use its opened context is
  transport in an arbitrary formula (`SDPrf.tr`), reflexivity is the
  transport of `I(0, a; u.u) = a` along itself, and a constant template gives
  DE (`SDPrf.dE`). Every rule is stable under substitution. This is the
  discharge rule of
  [`substitutive_discharge`](Artifacts/substitutive_discharge/) on the raw
  kernel.
- *QE at a variable or at 1.* The term argument of QE can be restricted to a
  variable and to the numeral `1`: `VQPrf true` has the two rules `qEVar`
  and `qEOne` in place of QE, and derives the same sequents
  (`vqprf_iff_nprf`). An arbitrary target `t` is named by a fresh alias
  `b = t`, whose discharge uses QE at `1` once; QE is applied at the variable
  `b`, and `B(b)` is moved to `B(t)` by the Leibniz rule for `B`. The Leibniz
  rule for a compound formula needs QE at `S z` for its matrix, so the two are
  proved together by induction on the formula (`VQPrf.qELeib`,
  `VQPrf.leibniz`), the Leibniz rule being stated for derivability of the two
  instances over one context, so that no substitution into a derivation is
  used. This is the counterpart, for the kernel, of the clause use without a
  term argument of
  [`deterministic_specialization`](Artifacts/deterministic_specialization/).
  The numeral cannot be dropped: `VQPrf false`, with QE at variables only,
  does not derive `0 = 1` from `Q_y (sel(y, 0, 1) = 0)`, which the kernel
  derives (`vqprf_var_incomplete`). The countermodel reads every variable as
  `0` and every `Q` and `D` formula as true.
- *The shape of the witness of DI.* `DWPrf z v` is the kernel with the
  witness of DI restricted to the literal `0` (if `z`) and to variables (if
  `v`). Each shape alone is incomplete. With `0` alone the calculus is sound
  for the standard reading in which `D_{x,y} B` is read at `x = 0`, and does
  not derive `D_{x,y} (sel(y, 1, x) = 1)` (`dwprf_zero_incomplete`). With
  variables alone it derives no `D` formula at all in the empty context
  without free variables, by a syntactic invariant: there every derivable
  formula is an equation or a closure over an equation
  (`DWPrf.simple`, `dwprf_var_incomplete`). The introduction at a variable
  is enough once every term has a name. `DNPrf` is the kernel with DI at a
  variable only and the axiom scheme `D_{x,y} (sel(y, a, x) = a)` for every
  term `a`, and `dnprf_iff_nprf : DNPrf Γ A ↔ NPrf Γ A`
  (`NativeNamedWitness`). The scheme is the naming matrix of
  [`deterministic_introduction`](Artifacts/deterministic_introduction/):
  opened at a fresh `b` and used at `y = 1` it gives `b = a`, so DI at a term
  `t` is DI at a name of `t` followed by the Leibniz rule. That calculus is
  closed under renaming and not under substitution; its Leibniz rule is
  proved over one context, and a dummy witness in a scope without variables
  is a name of `0`. The two shapes together are enough without the scheme:
  `dwprf_iff_nprf : DWPrf true true Γ A ↔ NPrf Γ A` (`NativeWitnessComplete`).
  The names are derived. With `P` the predecessor term, the name of `P(y)`
  holds at `0` with the witness `0`, and at `S z` with the witness `z`, since
  `z = P(S z)`; so it holds for all `y` by cases with a dummy witness, in
  particular at `S a`, and opening that name gives a variable equal to
  `P(S a) = a`. The two equations of `P` come from a calculus with no
  witness at all, below.
- *The predecessor needs equations only.* `EqPrf` derives an equation from
  equations by five rules: hypothesis, the two computations, transport in one
  term template, and induction for a literal equation with parameters. It
  has no formula other than equations, no coverage `x = 0 ∨ ∃y x = S y`, no
  separation and no case rule. `EqPrf.pred_succ : EqPrf Γ (pred (S t)) t`,
  `EqPrf.pred_zero` and `EqPrf.succ_inj` (`EqKernel`, `EqArith`, `EqParity`,
  `EqCompare`, `EqPred`). The lemmas are those of the `T_eq` development on
  the quotient `EQ Γ` of terms by `EqPrf Γ`; its three Boolean case splits
  and two splits on a selector count become equation cases on a fresh
  variable, that is, the induction rule with an unused hypothesis
  (`EQ.zf_add_zf`, `EQ.mod3_step`, `EQ.sel_cyc_zf`, `EQ.sel_add`,
  `EQ.sel_self_zero`). `EqPrf` embeds in the kernel under any restriction of
  the witness (`EqPrf.toDW`): its induction is QI by progress followed by
  QE. This is the audit of the predecessor in
  [`uniform_raw`](Artifacts/uniform_raw/),
  [`newest_parameter`](Artifacts/newest_parameter/),
  [`parameter_witness`](Artifacts/parameter_witness/) and
  [`no_witness`](Artifacts/no_witness/).
- *A one-iterator selector.* The mode of the single introduction can be read
  off a smaller shape than the diagonal one: progress exactly when the matrix
  is literally `a(x, y) = I(y, a(x, y); u.h)`. That calculus is `MiPrf`
  (seven rules, `miprf_iff_nprf`), and with reflexivity and Eval it is the
  six-rule `M6Prf` (`m6prf_iff_nprf`) of
  [`mirror_core`](Artifacts/mirror_core/). The shape is preserved by
  substitution but can be created by it, so `MiPrf` is closed under injective
  renaming (`MiPrf.ren`), which suffices for weakening under a binder and for
  cut, and not under substitution by a direct induction.
- *Six rules.* Reflexivity and one rule Eval can replace both computation
  equations and transport. Eval infers `r = Φ(s, t, b)` from `s = t` and
  `b = r`, where `Φ` is `t` if `b` is `I(0, s; u.h)`, and `h[t/u]` if `b` is
  `I(S c, a; u.h)` and `s` is `I(c, a; u.h)`. A third case, `Φ = t` if `b` is
  `s`, is derivable from the first through the frame `I(0, s; u.u)`
  ([`equality_from_iteration`](Artifacts/equality_from_iteration/)). With QE, DE
  and the single introduction this is a calculus of six rules, `EPrf`, on the
  unchanged terms and formulas with ordinary substitution, and it derives the
  same sequents (`eprf_iff_nprf`). The computation equations are Eval on two
  reflexivities; transport in a template `h` is one iteration of `h`. This is
  the calculus of
  [`computational_equality`](Artifacts/computational_equality/).
- *Six rules on zero-normal terms.* With the zero computation in the syntax,
  one introduction suffices there too: it is progressive exactly when the
  normalized zero instance of the matrix is literally `r = r`. Hypothesis,
  successor computation, transport in one term, QE, DE and this introduction
  are six rules, `NRPrf` (`nrprf_iff_nprf`, `NRPrf.normal`). This is the
  calculus of [`reflexive_base`](Artifacts/reflexive_base/). Its completeness
  is by translation of the diagonal calculus, with the invariant that a
  literally reflexive hypothesis may be dropped.
- *One successor step.* On zero-normal terms the zero case of Eval is absorbed
  by the syntax, and reflexivity with the single rule Step, from
  `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer `r = h[t/u]`, replaces
  both successor computation and transport (`NSPrf`, `nsprf_iff_nprf`,
  `NSPrf.normal`). Equality comes from a pivot of two Steps through
  `I(S 0, x; v.v)`. This is the interface of
  [`uniform_step`](Artifacts/uniform_step/).
- *Seed evaluation.* On zero-normal terms the rule Step can in turn be replaced
  by SeedEval, from `a = b` and `I(S c, a; u.h) = r` infer
  `r = h[I(c, b; u.h)/u]`, whose equation premise is about the seed alone
  (`NVPrf`, `nvprf_iff_nprf`). At the counter `0` the two rules are the same
  inference, which is where the equality reasoning takes place. This is the
  rule of [`seed_evaluation`](Artifacts/seed_evaluation/).
- *One evaluation rule and one introduction on zero-normal terms.* The
  companion calculus of
  [`equality_from_iteration`](Artifacts/equality_from_iteration/) has six
  rules: hypothesis, reflexivity, QE, DE, the single introduction with the
  literal test, and UE, from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer
  `r = h[t/u]` (`ZEPrf`, `zeprf_iff_nprf`). The introduction by cases of an
  equation at the witness `0`, which the single introduction does not have,
  is derived with the zero-normal alias `I(S 0, 0; u.0)` of `0`, with no
  weakening and no cut.
- *A public language for two restrictions at once.* The calculus `PGPrf`
  has the root-determined introduction (progress at a literal equation, cases
  at a compound matrix, no test of the witness) and transport at iterator
  sources only. Every rule of it is a derived rule of the kernel, but a
  hypothesis `x = y` between variables is not a transport source and the
  introduction by cases of an equation is missing. The gated translation
  `pub` replaces every equation `s = t` by `Q_w (I(w, 0; u.s) = I(w, 0; u.t))`.
  Its image is public: every atomic matrix has the guarded shape
  `I(y, 0; u.h)` on both sides (`NFm.pub_guarded`). On it the two calculi
  agree: `pgprf_pub_iff : PGPrf (Γ.map pub) (pub A) ↔ NPrf Γ A`. A gate is
  opened at `S 0` to the wrapped equation `wr s = wr t`,
  `wr s = I(S 0, 0; u.s)`, whose two sides are admissible sources, and is
  closed again by progress. This is the common content of the public
  languages of [`guarded_core`](Artifacts/guarded_core/),
  [`guarded_source`](Artifacts/guarded_source/),
  [`guarded_orbit`](Artifacts/guarded_orbit/),
  [`deterministic_auxiliary`](Artifacts/deterministic_auxiliary/) and
  [`protected_core`](Artifacts/protected_core/). The theorem is proved for
  any gating of equations (`Gating`), and the one-sided guard
  `s = I(w, s; u.t)` of [`mirror_guard`](Artifacts/mirror_guard/) is a second
  instance (`Gating.mirror`, `NFm.pub_mirrored`). `Q` can be removed from
  the public language as well: `NFm.pubD` uses the paired binder with an
  unused witness for every closure, its image has no `Q` and only guarded
  atomic matrices (`NFm.pubD_noQ`, `NFm.pubD_guarded`), and
  `pgprf_pubD_iff : PGPrf (Γ.map pubD) (pubD A) ↔ NPrf Γ A`. That is the
  grammar of the packages: paired binders over guarded equations, with `Q`
  only in the contexts of derivations. The translation cannot be
  dropped: `PGPrf` does not derive `x = z` from `x = y` and `y = z` between
  variables (`pgprf_not_trans`), so on arbitrary sequents it is strictly
  weaker than the kernel (`pgprf_strictly_weaker`). The proof is a reading in
  which a value is a number with a colour, bound variables range over
  ordinary numbers, and an equation holds by number or by adjacent colours;
  every rule of `PGPrf` is sound for it and equality is not transitive.
  The root-determined introduction alone, with unrestricted transport
  (`RDPrf`), is complete on a public language too (`rdprf_pub_iff`) and is
  also strictly weaker on arbitrary formulas: it does not derive
  `D_{x,y} (y = 1)`, which the kernel derives by cases (`rdprf_not_cases`,
  `rdprf_strictly_weaker`). Here the sound reading is the progressive one:
  a closure over a literal equation is read as progressivity. The source
  restriction alone, with the two introductions of the kernel (`TIPrf`),
  contains `PGPrf` (`PGPrf.toTI`), is complete on both public languages
  (`tiprf_pub_iff`, `tiprf_pubD_iff`), and still does not derive
  transitivity between variables (`tiprf_not_trans`): the reading with
  colours is sound for the introduction by cases and for `Q` by progress as
  well. So each restriction is responsible for one loss by itself: iterator
  sources lose transitivity of raw equations, and the root-determined
  introduction loses the introduction by cases of raw equations.
- *Five rules on zero-normal terms, and four schemes.* The clause calculus
  can be put on zero-normal terms with the one successor step as its only
  computation: Refl, Eval, Use, Elim and Intro, each normalizing its
  conclusion, Intro reading its mode off the matrix and the witness (`ZCPrf`,
  `zcprf_iff_nprf`). This is the calculus `C5` of
  [`clausal_single_evaluation`](Artifacts/clausal_single_evaluation/). With
  uniform clauses and the fixed reflexivity clause it has the four schemes
  Use, Step, Open and Close of
  [`clause_contexts`](Artifacts/clause_contexts/) (`ZVPrf`, `zvprf_iff_zcprf`,
  `zvprf_iff_nprf`). Completeness normalizes a derivation of the raw clause
  calculus rule by rule. One case changes under normalization: an
  introduction by cases for an equation whose witness is not the literal `0`
  but has the normal form `0`, which on normal terms would select progress.
  It is made at the witness `w = I(S 0, 0; u.0)` instead, which is
  zero-normal, equal to `0` by one Eval, and not the literal `0`; the
  translation carries the invariant that an assumption `E(t)` of the source
  may be the assumption `E(w)` of the target (`Conv`), and converts at each
  use (`ZCPrf.convEq`). No cut and no renaming of `ZCPrf` derivations is
  needed.
- *Other forms of the source restriction.* For transport in an equation
  template with an uncrossed conclusion, the same restriction needs an
  equation induction and a singleton test, though no logical rule
  (`zprf_iff_nprf`; [`guarded_source`](Artifacts/guarded_source/); class
  `ZKernel`). If transport in arbitrary templates and QE both reverse the
  root equation of their conclusion, it again needs no induction
  (`rprf_iff_nprf`, the module proposed by
  [`reversal_core`](Artifacts/reversal_core/)).

**Which rules cannot be dropped.** Seven of the eight rules of the kernel are
independent of the others (`NativeModels`). A *reading* of the language over
the natural numbers fixes the value of the iterator and the meanings of an
equation, of `Q` and of `D`; one soundness theorem (`FPrf.sound`) asks of a
reading one condition for each rule in use, and each of the following readings
meets the conditions of the other rules and refutes a sequent that the kernel
derives:

| Rule dropped | Reading | Sequent lost |
| --- | --- | --- |
| `I(0, a; u.h) = a` | `I(c, a; u.h)` is `h` applied `c + 1` times to `a` | `I(0, 0; u.S u) = 0` |
| `I(S c, a; u.h) = h[I(c, a; u.h)/u]` | `I(c, a; u.h)` is `a` | `I(1, 0; u.S u) = S I(0, 0; u.S u)` |
| Tr | `s = t` means `s ≤ t` | `0 = 1 ⊢ 1 = 0` |
| QE | every `Q` and `D` formula is true | `Q_y (sel(y, 0, 1) = 0) ⊢ 0 = 1` |
| DE | every `D` formula is true | `D_{x,y} (sel(y, 0, 1) = 0) ⊢ 0 = 1` |
| DI | every `D` formula is false | `D_{x,y} (0 = 0)` |
| Hyp | none: without Hyp a derivation does not depend on its context | `0 = 1 ⊢ 0 = 1` |

The progress rule QI is the eighth. Its independence cannot be shown by a
reading of this kind: over the natural numbers the conditions for DI and DE
already imply the condition for QI, whatever an equation means
(`Sem.Sound.qIInd_of`). It needs a structure with nonstandard numbers in which
both computation equations hold at every count, and is left open here.

The standard reading meets every condition, so the kernel does not derive
`0 = 1` (`native_consistent`). Through the bi-interpretation this is the
consistency of `T_eq` and of iPRA (`teq_consistent`, `pra_consistent`), by a
proof that evaluates iterator terms only.

**Ordinary realization.** `T_eq` is intuitionistic first-order logic with
equality over the same terms, with the two computation equations, coverage
`∀x (x = 0 ∨ ∃y x = S y)`, separation `0 = S 0 → ⊥`, and induction for literal
equations with side assumptions. The reports derive a predecessor, reflection
of equality into a term, quantifier-free induction, pairing and a compiler for
all primitive recursive definitions, in that order, which gives the
bi-interpretation with iPRA.

The complete statement and the written proofs are in
[`Artifacts/certified_zero/reference/`](Artifacts/certified_zero/reference/)
(`inherited_choice_basis.tex`, `inherited_ordinary_bridge.tex`,
`scalar_predecessor.tex`, `equality_reflection.tex`,
`primitive_recursion.tex`).

## Packages

Sizes are tokens / AST nodes / normalized bytes of the selected complete
checker, as stated by each package; where a package reports separate programs
for separate coordinates, they are listed separately. Each package's own
`README` and `CLAIMS.json` are the authority for its claims and limits.

### On the native scalar core

| Package | Contribution beyond the inherited basis | Checker |
| --- | --- | --- |
| [`constructed_computation`](Artifacts/constructed_computation/) | Successor sources constructed from predecessors; a finite-range obstruction to restricting DI witnesses and QE targets at once | 279 / 314 / 682 |
| [`counter_congruence`](Artifacts/counter_congruence/) | A counter-congruence form of the calculus | 280 / 314 / 672 |
| [`uniform_predecessor`](Artifacts/uniform_predecessor/) | Uniform predecessor packets; single-body initializer fusion cannot define addition, selection or pairing | 269 / 307 / 629 |
| [`adaptive_seed`](Artifacts/adaptive_seed/) | An obstruction result only; no smaller checker | — |
| [`research`](Artifacts/research/) | A progressive binder `H_{x,y} B := ∃x ∀y (B(x,y) → B(x,S y))`; an eventually-constant obstruction | 276 / 305 / 749, and 652 bytes |
| [`local_scopes`](Artifacts/local_scopes/) | No finite-dimensional bi-interpretation of iPRA with the tied-seed `B` theory | 668 bytes |
| [`checker_and_barriers`](Artifacts/checker_and_barriers/) | Two further obstructions | 593 bytes |
| [`compact_kernel`](Artifacts/compact_kernel/) | Truth transfer in eventually constant powers for all `∧, ∃, ∀` formulas, hence a symmetry obstruction | 266 / 310 / 612 |
| [`certified_zero`](Artifacts/certified_zero/) | Certified zero sources; the reference statement of the inherited basis and bridge | 264 / 308 / 566; 558 bytes; joint 262 / 296 / 598 |
| [`uniform_zero`](Artifacts/uniform_zero/) | Uniform zero and constructed elimination majors; shorter certificates | 545 to 564 bytes over six profiles |
| [`uniform_premise`](Artifacts/uniform_premise/) | Every non-hypothesis instruction verifies a major premise against a retained neutral truth; a successful-trace invariant replaces the type guard | 262 / 303 / 548, and 537 bytes |
| [`witness_rule`](Artifacts/witness_rule/) | One introduction rule in place of the case/progress choice: progress exactly when the matrix is a literal equation and the witness is literally `0`, cases otherwise; the same sequents are derivable | 266 / 312 / 555 |
| [`neutral_scope`](Artifacts/neutral_scope/) | Composition of neutral premises with local scopes; no new mathematics | 266 / 310 / 529, and 290 AST nodes |
| [`prevalidated_elimination`](Artifacts/prevalidated_elimination/) | The elimination template and both instances are fixed before the major premise is proved; no new mathematics | 263 / 307 / 547; 539 bytes; 261 tokens |
| [`scope_and_coverage`](Artifacts/scope_and_coverage/) | Byte-profile checkers; for the self-seeded recursor without successor injectivity, `S^k(a) ≠ a` for each fixed `k ≥ 1` and a right predecessor with `n = 0 ∨ n = S(P n)` | 266 / 310 / 529, and 537 bytes |
| [`coverage_and_kernel`](Artifacts/coverage_and_kernel/) | For the self-seeded recursor without successor injectivity, whole-domain coverage from a protected orbit; one `D` over a literal equation represents exactly the prenex `∃∀` quantifier-free class | 531 and 539 bytes; 289 AST nodes |
| [`direct_closure`](Artifacts/direct_closure/), [`direct_closure_qprogress`](Artifacts/direct_closure_qprogress/) | Two independent write-ups of one change of primitive: equation induction introduces `Q_y E(y)` directly, from `E(z) ⊢ E(S z)`, and the witnessed `D` progress rule becomes derived; the first also carries a Lean migration sketch and a counter-vector experiment | no new minimum (552 and 568 bytes; 533 for the experiment) |
| [`source_dispatch`](Artifacts/source_dispatch/) | Transport may be restricted to sources that are not literally `0`, every omitted instance being derivable; the source then selects the elimination major (`Q_v F(v)` at `0`, `s = t` otherwise) | 259 tokens; 283 AST nodes; 526 bytes (three programs) |
| [`guarded_core`](Artifacts/guarded_core/) | Atomic matrices under `D` restricted to the guarded shape `I(y,0;u.h) = I(y,0;u.k)`, so one root-determined introduction rule suffices: progress at equations, cases at compound matrices | 260 tokens; 286 AST nodes; 527 bytes (three programs) |
| [`scope_and_closure`](Artifacts/scope_and_closure/) | Checker composition only for the core; a "mixed closure" variant with progressive `Q` at literal equations and a deterministic introduction; an obstruction to zero-start iterators | 264 / 288 / 608, and 528 bytes |
| [`reversal_core`](Artifacts/reversal_core/) | Transport and QE reverse the root equation of their conclusion, with transport sources other than the literal `0`; a constant template then gives unrestricted symmetry in one step, and the source restriction is removed with no induction, cases or successor computation. Ships a proposed Lean module | 525 bytes; 282 AST nodes (two programs); typed checker 1055 bytes against a 1365-byte control |
| [`guarded_source`](Artifacts/guarded_source/) | Source dispatch and the guarded core coexist: the recovery of zero-source transport needs equation induction only, its case splits being inductions that ignore the hypothesis | 258 tokens; 281 AST nodes; 525 bytes (as stated, different programs) |
| [`guarded_orbit`](Artifacts/guarded_orbit/) | In a strictly guarded proof language the two do not compose (`0 = t` does not yield `t = 0`); the administrative orbit `D_{r,y}(y = I(y,t;u.Su))` repairs it | 258 tokens; 281 AST nodes; 525 bytes (three programs) |
| [`deterministic_auxiliary`](Artifacts/deterministic_auxiliary/) | Source-selected elimination with root-determined introduction, keeping unrestricted atomic progress formulas as auxiliary intermediates; the guarded public consequences are unchanged | 525 and 522 bytes |
| [`mirror_guard`](Artifacts/mirror_guard/) | A one-sided guard: canonical atomic matrices `a(x,y) = I(y, a(x,y); u.h)`, with one root-determined introduction and no literal-zero transport source | modest, as stated |
| [`protected_core`](Artifacts/protected_core/) | Public equality `s = t` represented as `W(s) = W(t)`, `W(r) = I(0,r;u.0)`, so that every transport source is iterator-headed | modest, as stated |
| [`one_context`](Artifacts/one_context/) | Transport with one term template instead of two, crossed: from `s = t` and `h(s) = u` infer `u = h(t)`. Two steps recover the two-template rule; sources are unrestricted and the rule is stable under substitution. Ships proposed Lean modules. Independently, strict goal validation reuses the kernel's scope check | matched tagged checker 3382 to 3358 bytes, 1101 to 1089 tokens; strict Eq/D validator 824 to 803 bytes |
| [`kernel_refinement`](Artifacts/kernel_refinement/) | The guarded-source checkers with a loop over immutable tuple contexts and the scalar neutral premise. An auxiliary note replaces equational transport by replacement of one occurrence in the left side of an equation, `C[s] = r` to `C[t] = r` for a linear term context `C` | 256 tokens; 278 AST nodes; 521 bytes (three programs) |
| [`compact_update`](Artifacts/compact_update/) | The scalar neutral-resource encoding of `reversal_core` applied to the `guarded_source` checkers; stated to be an implementation-level composition. Also an exact criterion for when the conditional closure `E(0) → ∀y E(y)` and the progressive closure `∀y (E(y) → E(S y))` of an equation agree: exactly when `¬E(0)` implies progress | 257 tokens; 278 AST nodes; 521 bytes (different programs) |
| [`uniform_progress`](Artifacts/uniform_progress/) | A seven-rule calculus `R` on the unrestricted formula grammar with a changed reading: `Q_y E` of a literal equation means progress, `∀y (E(y) → E(S y))`, and of a compound matrix the conditional closure. One introduction rule chooses its mode from the root of the matrix alone, so it commutes with substitution; one elimination `Q_y B, B(η) ⊢ B(I(η, n; u. S u))` serves both readings. Translations to and from the native calculus with both round trips, as written proofs | matched typed checker 4553 bytes against 4692 for the eight-rule kernel and 4456 for the seven-rule witness kernel |
| [`one_sided_transport`](Artifacts/one_sided_transport/) | The seven-rule calculus with its transport replaced by the one-template crossed rule at sources other than the literal `0`: from `s = t` and `f(s) = r` infer `r = f(t)`. The zero computation and this rule alone recover all equality reasoning, with no induction and no logical rule. Ships a proposed Lean module | matched strict checker 3246 bytes against 3302, 1171 tokens against 1196 |
| [`validated_core`](Artifacts/validated_core/) | One recursive validator shared between raw-tree typing and the public grammar, for the unchanged rule basis | fully validated Eq/Q/D checker 897 bytes against a matched 1049; compact envelope 256 tokens, 278 AST nodes, 521 bytes (different programs) |
| [`validated_presentation`](Artifacts/validated_presentation/) | The whole certificate is typed by one test on its printed form, so the public syntax validator loses its separate raw-type pass; the proof kernel is unchanged | fully validated Eq/Q/D checker 870 bytes against 897, 383 tokens against 401 |
| [`checked_refinement`](Artifacts/checked_refinement/) | Three smaller implementations of the existing presentations; stated to contain no new axiom deletion | guarded public-goal checker 921 bytes against 1201; native Eq/D public checker 788 against 803; compact guarded 520 against 521 |
| [`equality_from_iteration`](Artifacts/equality_from_iteration/) | The rule Eval of `computational_equality` without its first case: equality composition `s = t, s = r ⊢ r = t` follows from the zero-iteration case through the frame `I(0, s; u.u)`. A companion calculus on zero-normal terms has reflexivity and one successor-evaluation schema | as stated |
| [`clause_guards`](Artifacts/clause_guards/) | The raw Eq/D clause calculus with the two-case Eval and the diagonal introduction: five rule families, with ordinary substitution preserving the whole proof tree | as stated |
| [`mirror_core`](Artifacts/mirror_core/) | Six rules on the raw language (Hyp, Refl, Eval, QE, DE and one introduction), the introduction being progressive exactly at a matrix of the literal shape `a(x,y) = I(y, a(x,y); u.h)`: one iterator in the selector where the diagonal guard has two | as stated |
| [`seed_evaluation`](Artifacts/seed_evaluation/) | On zero-normal terms, the rule `a = b, I(S c, a; u.h) = r ⊢ r = h[I(c, b; u.h)/u]` with reflexivity, equivalent to the rule Step without any logical rule or induction | as stated |
| [`clause_contexts`](Artifacts/clause_contexts/) | Four inference schemes (Use, Step, Open, Close) and the reflexivity axiom clause, on zero-normal terms | as stated |
| [`witness_discharge`](Artifacts/witness_discharge/) | Three inference families (Use, Intro, Name) and the reflexivity axiom clause; Name combines equality substitution with the discharge of an existential witness | as stated |
| [`inferred_witness`](Artifacts/inferred_witness/), [`deterministic_opening`](Artifacts/deterministic_opening/), [`first_instance`](Artifacts/first_instance/), [`clause_discharge`](Artifacts/clause_discharge/) | On full normal forms with clause contexts: the opening of `D_{x,y} B` at a fresh `b` reads its witness off the matrix. If `B(b, 0)` is literally `0 = 0` and `B(b, 1)` is literally `b = t`, the clause is opened at `t` (or `t` is substituted for `b` in the exported formula); otherwise at `b`. No replacement term and no equality proof are supplied. Three families (Use, Intro, Open) and the reflexivity clause | as stated; each reports a smaller matched complete checker and none claims a new minimum |
| [`substitutive_discharge`](Artifacts/substitutive_discharge/) | On the canonical recursor syntax, four families: one successor calculation, Use, Intro, and a discharge that opens `D` at a fresh `b`, proves `s = t` and `F(s)` there, and exports `F(t)`. Reflexivity is derived; no full normalization and no fixed clause | as stated |
| [`deterministic_introduction`](Artifacts/deterministic_introduction/) | In the raw guarded Eq/D calculus the introduction takes no witness: it selects `r` if the matrix is literally `C(y, 0, x) = C(y, 0, r)` with `C(y, a, b) = I(y, a; u.b)`, otherwise the newest numerical parameter, and `0` in an empty numerical scope. Proved equivalent to the unrestricted calculus on every open consequence; cut is proved before weakening | 1159 tokens; 1339 AST nodes; 3688 bytes, against 1078 / 1252 / 3442 for the matched control |
| [`newest_parameter`](Artifacts/newest_parameter/) | In the raw native calculus DI by cases takes no witness: always the newest numerical parameter, or `0` in an empty scope, with no naming-pattern exception; QI by progress is kept. Written proof of the same consequences as `NPrf` on all open sequents, with an audit that removes the Boolean and disjunctive case splits from the predecessor proof. Also for the strict guarded clause presentation | guarded: 1070 tokens; 1243 AST nodes; 3425 bytes, against 1078 / 1252 / 3442 for the unrestricted control |
| [`no_witness`](Artifacts/no_witness/) | The same restriction for the eight-rule native kernel and its seven-rule diagonal variant, on all native Eq/Q/D sequents | seven rules: 924; 1021; 2753, against 932 / 1029 / 2770. Eight rules: 971; 1078; 2817 |
| [`parameter_witness`](Artifacts/parameter_witness/) | A five-family raw clause calculus whose introduction carries one bit: `0` or the newest numerical parameter. The scalar predecessor is reorganized as a purely equational dependency, which removes the circularity of naming terms by a predecessor before logical completeness | as stated |
| [`uniform_raw`](Artifacts/uniform_raw/) | The raw guarded calculus of `deterministic_introduction` without its naming exception: introduction always at the newest parameter, or `0`. The predecessor is constructed from computation, equality and equation induction only (equational interpolation in place of Boolean case splits), and a coverage packet supplies the names | 1073 tokens; 1248 AST nodes; 3439 bytes, against 1159 / 1339 / 3688 for the naming-exception control |
| [`evaluation_discharge`](Artifacts/evaluation_discharge/) | On raw iterator terms with clause contexts, three families: Use, Intro, and a discharge that opens `D B` at a fresh `b`, proves `E` and `F` there, performs one deterministic evaluation (the two Eval patterns, or identity) and exports the result. A zero-normal companion with SeedEval | raw: 643 tokens; 695 AST nodes; 1892 bytes. Zero-normal: 633; 697; 1858 |
| [`one_body`](Artifacts/one_body/) | A context entry is one body `B(y)`, read as `B(0) → ∀y B(y)`, with no separate antecedent; an ordinary assumption is stored under an iterator gate. Atomic reflexivity, the two Eval cases, Use, Open and Intro | 3130 bytes, against 2999 for the matched control |
| [`progress_independence`](Artifacts/progress_independence/) | QI by progress is not admissible over the other seven rules of the kernel: a model of all finite iterator computations, coverage and separation, built as a staged tower of ultrapowers, in which `I(c, 0; u.u) = 1 ≠ 0` for some `c`; so `Q_y (I(y, 0; u.u) = 0)` fails while its base and step are derivable without progress. Also two smaller checkers of the existing presentation | 251 tokens; 283 AST nodes; 605 bytes, and 269; 301; 502 |
| [`orbit_closure`](Artifacts/orbit_closure/) | Orbit uniqueness: from `f(S z) = h(f(z))` infer `∀y (f(y) = I(y, f(0); u.h))`, with no target term, equivalent to pointwise uniqueness over arbitrary contexts; a narrower successor-only uniqueness; an audit of every Python source of the corpus | no size record, as stated |
| [`crossed_uniqueness`](Artifacts/crossed_uniqueness/) | On fully normalized terms, seeded crossed uniqueness derives equality transport and equation induction; a six-rule calculus. Separately a compact checker of the existing guarded calculus | reference checker 1909 tokens; 2087 AST nodes; 5618 bytes. Compact: 269; 301; 502 against 506 bytes |
| [`inferred_major`](Artifacts/inferred_major/), [`smaller_envelope`](Artifacts/smaller_envelope/) | The certificate no longer carries the major formula of an elimination: the checker reconstructs it from the target instance and still checks its proof. A mode selector `3 % len(a)` in place of the matrix-root test | compact envelope 253 tokens / 275 AST nodes / 503 bytes, by different programs; native public-goal checker 327; 375; 643 |
| [`checked_presentation`](Artifacts/checked_presentation/), [`context_phase`](Artifacts/context_phase/), [`frontier_review`](Artifacts/frontier_review/) | Smaller checkers of the existing calculi: a fully validated native Eq/D checker; an immutable-context checker in which the empty context marks the validation of the public goal, so that no phase flag is needed; a byte refinement of the guarded checker | 344 tokens; 393 AST nodes; 673 bytes against 370 / 426 / 849. 327; 375; 643 against 333 / 379 / 656. 513 bytes against 516 |
| [`prefix_clauses`](Artifacts/prefix_clauses/) | A `Q`-free formula is a chain of `D` binders ending in one equation, stored as `[k, s, t]` for `D^k (s = t)`; the four families of `uniform_clauses` on that representation. A separate theorem removes the antecedent field of a clause | as stated |
| [`variable_substitution`](Artifacts/variable_substitution/) | On zero-normal terms the equality rule substitutes for a variable only: from `x = t` and `u = v` infer `v = nf(u[t/x])`; the source can be restricted to the newest parameter | as stated |
| [`parameter_substitution`](Artifacts/parameter_substitution/) | On raw terms with clause contexts, replacement inside a term is restricted to free parameters; a nonvariable source is used only for joining at the root or reversing the minor equation, and a fresh alias recovers transport in a template. Five instruction families | as stated |
| [`deterministic_specialization`](Artifacts/deterministic_specialization/) | Clause use takes no term argument: the newest clause is specialized at `S 0`, every older one at the newest eigenparameter, and an arbitrary term is reached by naming it with a `D` formula and transporting | as stated |
| [`uniform_clauses`](Artifacts/uniform_clauses/), [`clausal_two_case`](Artifacts/clausal_two_case/), [`clausal_single_evaluation`](Artifacts/clausal_single_evaluation/) | Further forms of the clause calculus: reflexivity as one fixed axiom clause with four instruction families; the two-case Eval; zero-normal terms with a single evaluation scheme | as stated |
| [`uniform_step`](Artifacts/uniform_step/) | On zero-normal terms, reflexivity and one rule Step, from `I(c, a; u.h) = t` and `I(S c, a; u.h) = r` infer `r = h[t/u]`, give all computation and equality; at `c = 0` the first source is `a` by the syntax. With clause contexts: five schemes | as stated |
| [`rootfree_clausal`](Artifacts/rootfree_clausal/), [`reduced_clause_calculus`](Artifacts/reduced_clause_calculus/) | The clause calculus of `raw_clausal` with a two-case Eval, the equality-composition case being derived through a zero-iterator frame; `rootfree_clausal` adds a zero-normal variant whose introduction is progressive exactly when the instantiated zero base is literally `0 = 0` | as stated |
| [`computation_normal`](Artifacts/computation_normal/) | A six-rule calculus on fully normal terms, as in `full_normalization`, with the statement that it does not robustly reduce checker size; separately a validated checker of the unchanged calculus | 860 bytes against 870 |
| [`full_normalization`](Artifacts/full_normalization/) | Both iterator computations moved into the syntax: terms are in full normal form for `I(0, a; u.h) → a` and `I(S n, a; u.h) → h[I(n, a; u.h)/u]`, and there is no computation rule at all. Six patterns: Hyp, Refl, Tr, QE, DE and one witness-selected introduction, with a lemma that repairs case introduction when normalization turns a witness into the literal `0`. Written proofs of strong normalization, confluence and substitution coherence | selected checker 2529 bytes against 2532 for the zero-only control, with more tokens and AST nodes |
| [`reflexive_base`](Artifacts/reflexive_base/) | On zero-normal terms, the single introduction is progressive exactly when the normalized zero instance of the matrix is literally `r = r`. Six rules; a raw seven-rule variant with an asymmetric selector gate | matched strict checker 3084 bytes against 3095 |
| [`raw_clausal`](Artifacts/raw_clausal/) | Five rule patterns with ordinary substitution: reflexivity, Eval, use of a retained clause, paired elimination, witness-directed paired introduction; formulas `s = t` and `D` only, with clause contexts in place of `Q` | as stated |
| [`scalar_uniqueness`](Artifacts/scalar_uniqueness/) | Induction for literal equations replaced by uniqueness of iteration: from `f(S z) = h(f(z))` infer `f(t) = I(t, f(0); u.h(u))`, with no induction hypothesis in the premise. The report recovers predecessor, reflection of equality and equation induction from it, closing the gap left open in `scope_kernel` | matched raw checker grows from 3322 to 3393 bytes; validated checker of the existing calculus 866 against 870 |
| [`computational_equality`](Artifacts/computational_equality/) | Six rules on the unchanged language, with no normalization: Hyp, Refl, Eval, QE, DE, DI. Eval merges equality with one computation: from `s = t` and `b = r` infer `r = Φ(s, t, b)`, where `Φ` is `t` if `b` is `s` or `b` is `I(0, s; u.h)`, and `h[t/u]` if `b` is `I(S c, a; u.h)` and `s` is `I(c, a; u.h)`. Both computation equations and all congruence are derived | matched checker 3039 bytes against 3121, 959 tokens against 1008 |
| [`zero_normal`](Artifacts/zero_normal/) | Terms with no iterator whose counter is the literal `0`; substitution rebuilds terms with `I(0, a; u.h)` replaced by `a`, so the zero computation rule is deleted. With the single introduction and one-term transport: six rules. Ships a compiled Lean module for the normalization layer | matched strict tagged checkers, 8 and 7 rules: 3322 and 3272 bytes |
| [`diagonal_guard`](Artifacts/diagonal_guard/) | One introduction whose mode is chosen by a guard that substitution preserves and reflects: progress exactly when the matrix is literally `I(y, y; u.h) = I(y, y; v.k)`, cases otherwise. Seven rules on the full formula language with the original readings | matched typed checker 3244 bytes against 3382 for eight rules and 3205 for the witness rule |
| [`template_free`](Artifacts/template_free/) | Equality with no supplied template: from `s = t` and `u = v` infer `v = R(u)`, where `R` replaces every free occurrence of `s` in `u` by `t` in one pass. Seven rules; congruence in a chosen context is recovered through an oversized computation marker | strict tagged checker, as stated |
| [`target_closure`](Artifacts/target_closure/) | A seven-rule progressive calculus `T` whose closure elimination supplies one numerical target, equivalent to the calculus of `uniform_progress`; separately, exact certificate typing by a lexical gate for the existing calculus | `T` checker 4532 bytes against 4553; typed checker of the existing calculus 895 bytes against 1039 |
| [`scope_kernel`](Artifacts/scope_kernel/) | Reuse of the kernel's first scope traversal in the validated checker. Two research notes: a coordinatewise model on `N × N` that validates equation induction and refutes coverage, and an unfinished attempt to replace equation induction by uniqueness of iteration | fully validated Eq/Q/D checker 881 bytes against 897 |

### Other arithmetic bases

| Package | Arithmetic basis |
| --- | --- |
| [`scalar_successor`](Artifacts/scalar_successor/), [`transient_seed`](Artifacts/transient_seed/), [`successor_seed_completion`](Artifacts/successor_seed_completion/) | A successor-seeded recursor `R(0,a;u.h) = S(a)`, `R(S n,a;u.h) = h[R(n,a;u.h)/u]`, with `S(a) := R(0,a;u.0)`; three independent predecessor constructions |
| [`bounded_initializer`](Artifacts/bounded_initializer/) | A tied-seed recursor `B` with a Boolean equality test `ε` |
| [`monus_and_neutral_major`](Artifacts/monus_and_neutral_major/) | A tied-seed recursor with two truncated-subtraction equations, from which reflection of equality is derived; also a neutral-major certificate protocol for the native core |
| [`selfseed_scalar`](Artifacts/selfseed_scalar/) | A self-seeded recursor `F(0;v.h) = S(h(0))`, `F(S n;v.h) = h(F(n;v.h))` over ordinary logic with successor injectivity, `0 ≠ S 0`, a Boolean equality test and literal-equation induction; also checkers of 554 bytes and of 291 AST nodes for the native core |
| [`register_graph`](Artifacts/register_graph/) | Terms `x`, `0` and a counter-aware register iterator `J(n; i, r. body)` only, over ordinary logic: successor `S(a) = J(a; i, r. 0)` and the initializer are derived, and primitive recursion compiles without pairing; also a 288-node AST checker for the native core |
| [`canonical_recursors`](Artifacts/canonical_recursors/) | A successor-seeded recursor `R(n, a; u.h)` with successor defined as `R(0, a; u.0)`; the zero computation is built into a canonical term grammar with normalizing substitution, so successor computation is the only explicit computation rule. Six rules; written proofs of the equivalence with the raw calculus and of the bi-interpretation with iPRA. Normalization is part of the trusted specification. Matched strict checker 4611 bytes against 4923 for the scalar iterator with independent `S`; separately, the compact guarded codec at 516 bytes against 522 |
| [`initializer_equality`](Artifacts/initializer_equality/) | On zero-normal iterator terms, equality transport is replacement of an iterator's initializer; zero iteration is definitional, so this includes replacement at the root, and one iteration applies any term template. Six rules; the equality step takes two proofs and no template |
| [`clausal_canonical`](Artifacts/clausal_canonical/) | Five rules on the canonical recursor syntax, with an Eq/D public language and contexts of reusable clauses in place of `Q`. Matched checker 3305 bytes against 3820 for the six-rule control |
| [`counter_evaluation`](Artifacts/counter_evaluation/) | On the counter-aware successor-seeded recursor `R(n, a; i, u.h)`, reflexivity and one rule: from `s = t` and `R(S s, a; i,u.h) = r` infer `r = h(t, R(t, a; i,u.h))`. With clause contexts: five patterns |
| [`uniform_binding`](Artifacts/uniform_binding/) | The counter-aware clause calculus with one ternary recursor `R(n, a; i, u.h)`; `R` and `D` both bind exactly two variables in their last child, and one traversal handles validation, zero-body erasure and binder opening |
| [`parameter_intro`](Artifacts/parameter_intro/) | On the counter-aware successor-seeded recursor with full normalization and clause contexts, three families: Use, Introduction, and substitution with discharge. Introduction takes no witness: it uses the newest outer numerical parameter, or `0` at the closed root; arbitrary witnesses are recovered by naming through clause specialization. 630 tokens / 701 AST nodes / 1925 bytes |
| [`conditional_copy`](Artifacts/conditional_copy/) | Introduction at the newest parameter combined with a discharge that infers its replacement from two normalized rows; three families Use, Close and Export, and only Use supplies a term. The theorem that makes the combination possible is conditional copy, `D_{x,y} Sel(y, H(t), H(x))`, proved uniformly without equality transport |
| [`single_constructor`](Artifacts/single_constructor/) | Terms `x`, `0` and `R(n, a; i, u.h)` with the successor defined, a fixed reflexivity clause and three families Use, Introduce and Open with an inferred witness, on full canonical normal forms. 683 tokens / 764 AST nodes / 1965 bytes |
| [`constantfree`](Artifacts/constantfree/) | Terms `x` and `J(n; i,r.h)` only, with no numerical constant: `K(t) = J(t; i,r.i)`, `U(t) = J(t; i,r.K(r))`, `Z(t) = J(U(t); i,r.r)`, `S(t) = J(t; i,r.Z(r))`; zero is defined by `z = Z(z)`. Two `J` occurrences are necessary and sufficient for the constant one, three for zero. Also smaller compact checkers of the existing calculus | reference checker 3072 tokens; 3349 AST nodes; 13723 bytes against 2811 / 3054 / 12626. Compact: 250; 283; 603 and 264; 299; 498 |
| [`three_field`](Artifacts/three_field/) | Three-field certificates: the elimination major is inferred from the endpoint, the source field is reused as that major, and a cleared seed selects the major-checking branch | 249; 278; 607 and 255; 271; 606; four-field byte program 267; 299; 495; validated native checker 342; 391; 666 against 344 / 393 / 673 |
| [`guarded_register`](Artifacts/guarded_register/) | A guarded scalar register calculus with two unconditional computation axioms and no successor constructor, initializer field, Increment, Load or reflexivity rule; proved equivalent to the native core | strict checker 1041 tokens; 1181 AST nodes; 3467 bytes against 1045 / 1193 / 3566 |
| [`single_binder`](Artifacts/single_binder/) | A universal quantifier with one paired binder and one copy of the body, `D_{u,z} gate_z A(P(z))`, interderivable with the native universal; also a compact checker | 276; 308; 487 (since superseded by 272; 304; 479) |
| [`backward_replacement`](Artifacts/backward_replacement/) | Backward crossed replacement: from `s = t` and `Rep_t^s(u) = r` infer `r = u`, in place of transport; equivalent to the kernel, also without a literal-zero source | readable checker 1647; 1807; 7121 against 1581 / 1738 / 6971 |
| [`checker_refinement`](Artifacts/checker_refinement/), [`refinement`](Artifacts/refinement/), [`retained_premises`](Artifacts/retained_premises/), [`verified_refinements`](Artifacts/verified_refinements/), [`immediate_application`](Artifacts/immediate_application/), [`scope_and_frontier`](Artifacts/scope_and_frontier/), [`502_scope_audit`](Artifacts/502_scope_audit/) | Checker refinements of the existing calculi (retained majors, a two-field protocol, inverted entry test, immediate substitution, a context floor), with independent censuses, a counterexample to a cheaper scope shortcut, and an audit of packed sources | compact guarded envelope 249 / 271 / 479 by three programs; native 324; 374; 629; strict 334 / 387 / 637 |
| [`uniform_recursion`](Artifacts/uniform_recursion/) | Variables, `0` and the one recursor `R(n, a; i, u.h)`, with the successor defined as `R(0, a; i, u.0)`; a fixed reflexivity clause and three families Use, Close and Name. 662 tokens / 741 AST nodes / 1950 bytes |

## Intake record

Twenty-six archives `ipra_<name>_2026-11-10.zip` were delivered to
`docs/drafts/` on 2026-11-10, in three rounds of twenty, three and three, and
filed here on the same day.

- **Filed (22):** the packages listed above, each under its `<name>`.
- **Discarded (4):** `flat_computation`, `affine_arity`, `arity_calculus` and
  `affine_supply`. Each is a checker-size step on the native scalar core with
  no mathematics of its own, and each is superseded in its coordinates by
  `certified_zero` and its successors. The compact rule inventory of
  `affine_supply` is restated above.
- **Not filed from the kept packages:** the nested ZIP archives of earlier
  drafts carried by `constructed_computation`, `scalar_successor`,
  `successor_seed_completion` (nine each, under `sources/`) and
  `counter_congruence` (ten, under `reference/`); the LaTeX build logs; and
  two checksum ledgers. All of these, and the discarded archives, remain in
  the repository history under `docs/drafts/`.
- Two delivered CSV files with CRLF line endings are kept byte for byte by
  [`.gitattributes`](.gitattributes). File manifests inside the packages
  describe the delivered archives, so they also list the files not filed.
- The packages' Python scripts were not executed during the intake. The
  frozen comparison sources inside the packages are copies of checkers from
  earlier drafts of this same series, under the repository's MIT-0 licence.

A second delivery of six archives arrived in
[`docs/incoming/`](docs/incoming/) on 2026-11-10 and was filed on 2026-11-11:
`direct_closure` (two different packages under one archive name; the second
is filed as `direct_closure_qprogress`), `guarded_core`, `register_graph`,
`scope_and_closure` and `source_dispatch`. These respond to the Lean
formalization below. Not filed: their frozen copies of this repository's own
Lean sources (byte-identical to the pinned commits), three checksum ledgers
and one reproduction log. The archives remain in the repository history.
Their scripts were not executed.

A third delivery of six archives arrived in `docs/incoming/` on 2026-11-11
(commit `df07a9111c`) and was filed the same day: `deterministic_auxiliary`,
`guarded_orbit`, `guarded_source`, `mirror_guard`, `protected_core` and
`reversal_core`. They respond to the kernel with equational transport and
`zprf_iff_nprf`. Not filed, as before: fifty frozen copies of this
repository's Lean sources and three checksum ledgers. The proposed module
`Artifacts/reversal_core/formalization/Reversal.lean` is kept as delivered; its
compiled form is `Lean/ConciseIPRA/NativeReversal.lean`.

A fourth delivery of four archives arrived on 2026-11-11 (commits
`ed0d9a32d7`, `b1f7e85b3f` and `7669726207`) and was filed the same day:
`compact_update`, `one_context`, `kernel_refinement` and `uniform_progress`.
They respond to the third delivery and to `NativeReversal`. Not filed:
sixteen frozen copies of this repository's Lean sources and two checksum
ledgers. The proposed modules
`Artifacts/one_context/lean/*.lean` are kept as delivered.

A fifth delivery of two archives arrived on 2026-11-11 (commit `42a48d2f04`)
and was filed the same day: `one_sided_transport` and `validated_core`. Not
filed: thirty-nine frozen copies of this repository's Lean sources and one
checksum ledger. The proposed module
`Artifacts/one_sided_transport/formalization/NativeOneSided.lean` is kept as
delivered; `NativeOneContext` and `NativeMinimal` prove its theorems.

A sixth delivery of three archives arrived on 2026-11-11 and 2026-11-12 and
was filed on arrival: `canonical_recursors`, `checked_refinement` and
`validated_presentation`. Not filed: four frozen copies of this repository's
Lean sources and three checksum ledgers.

A seventh delivery of six archives arrived on 2026-11-11 (commit
`11be5aabc6`) and was filed the same day: `diagonal_guard`,
`initializer_equality`, `scope_kernel`, `target_closure`, `template_free` and
`zero_normal`. Not filed: fifty-five frozen copies of this repository's Lean
sources, three checksum ledgers and five build logs. The delivered module
`Artifacts/zero_normal/formal/ZeroNormalization.lean` compiled unchanged and
is `Lean/ConciseIPRA/ZeroNormalization.lean`.

Since 2026-11-12 an arrival is integrated directly into the article: its
mathematics into the chapter where it belongs, deduplicated, and its
executable part into `Artifacts/<package>/`; a checker that a smaller one
supersedes under the same input contract is deleted. The first such
delivery (commit `42fba2a76a`) was `constantfree` (chapter "Canonical and
counter-aware recursors"; compact checkers in "Certificates and checkers"),
`three_field` ("Certificates and checkers") and a second write-up of
`progress_independence` ("Obstructions", with its census under
`Artifacts/progress_independence/second_writeup/`). The next ten arrivals
(`502_scope_audit`, `backward_replacement`, `checker_refinement`,
`guarded_register`, `immediate_application`, `refinement`,
`retained_premises`, `scope_and_frontier`, `single_binder`,
`verified_refinements`) went the same way, into the chapters "The base
theories" (the one-binder universal), "Refinements of the eight rules"
(backward replacement), "Canonical and counter-aware recursors" (guarded
registers) and "Certificates and checkers" (the rest); 21 more checker files
they supersede were deleted. With it, 83 superseded
checker files were deleted from `Artifacts/` (the list is in the size
section of the chapter "Certificates and checkers").
On 2026-11-13 `conditional_image`, `coverage_constancy`, `coverage_obstruction`,
`homogeneous_discharge` and `validated_arity_refinement` went the same way, into the
chapters "Certificates and checkers" (the strict envelope is now 317/356/597;
`conditional_image` re-delivers two programs of `prefix_conditional`), "Discharge of a
witness and restricted equality rules" (coverage does not replace the comparison
equation; literal-zero transport with the equivalence rules stays incomplete) and
"Clause calculi" (the
three-rule homogeneous presentation); one checker they supersede and four re-delivered
copies of earlier superseded checkers were deleted.
Later that day `checked_reduction` and `validated_three_field` lowered the strict
envelope further, to 306/348/589 (and the compact node record to 255, chapter
"Certificates and checkers"); fifteen checker files they supersede, with their
byte-identical copies and three compressed copies, were deleted.
`checked_presentation`, `context_phase`, `crossed_uniqueness`,
`frontier_review`, `inferred_major`, `orbit_closure`, `progress_independence`
and `smaller_envelope` arrived on 2026-11-12 (commits `1c5ecfe518`,
`57aeafc84b`, `4326b27399`) and were filed on arrival. Not filed: six frozen
Lean copies, three logs, one checksum ledger, three build transcripts that
carry paths of the machine that produced them, twenty-one generated data
files larger than 300 kB (13.7 MB in all), and two censuses of this
corpus's own Python checkers (2,769 files under `audit/blobs` and
`reference/research_census`); all remain in the delivered archives in the
history of this repository.
`conditional_copy`, `newest_parameter`, `no_witness`, `parameter_witness`,
`single_constructor` and `uniform_raw` arrived earlier on 2026-11-12 (commit
`b16ed1b06e`) and were filed on arrival (eighteen frozen Lean copies and two
checksum ledgers not filed).
`deterministic_introduction`, `evaluation_discharge`, `one_body`,
`parameter_intro` and `uniform_recursion` arrived earlier on 2026-11-12 (commit
`9f9545f5ff`) and were filed on arrival (twenty-two frozen Lean copies and two
checksum ledgers not filed).
`clause_discharge`, `deterministic_opening`, `first_instance`,
`inferred_witness`, `prefix_clauses` and `substitutive_discharge` arrived
before them and were filed on arrival (sixteen frozen Lean copies, three logs and two
checksum ledgers not filed).
`clause_contexts`, `clause_guards`, `mirror_core`, `seed_evaluation`,
`uniform_binding` and `witness_discharge` arrived before them and were filed on
arrival (nine frozen Lean copies, three logs and two checksum ledgers not
filed). `clausal_single_evaluation`, `clausal_two_case`,
`deterministic_specialization`, `parameter_substitution`, `uniform_clauses`
and `variable_substitution` arrived after those below and were filed on
arrival. Not filed: sixteen frozen Lean copies, four logs, one checksum ledger,
and eighteen generated proof certificates of `clausal_single_evaluation`
larger than 300 kB each (13 MB in all; they remain in the delivered archive in
the history of this repository).
`computation_normal`, `counter_evaluation`, `reduced_clause_calculus`,
`rootfree_clausal` and `uniform_step` arrived last and were filed on arrival
(three frozen Lean copies, four logs and checksum ledgers not filed).
`full_normalization` arrived before them and was filed on arrival.
`equality_from_iteration`, `raw_clausal` and `reflexive_base` arrived before it
and were filed on arrival (seventy-nine frozen Lean copies and two logs not
filed). `clausal_canonical` and `scalar_uniqueness` arrived after these and were
filed on arrival (two frozen Lean copies and one checksum ledger not filed).
`computational_equality` arrived later the same day and was filed on arrival;
four frozen copies of this repository's Lean sources and one build log are
not filed.

## Lean formalization

The Lake library `ConciseIPRA` (root workspace; sources under
[`Lean/ConciseIPRA/`](Lean/ConciseIPRA/), namespace `LeanProofs.ConciseIPRA`)
formalizes three systems and proves them mutually bi-interpretable:

1. **The native scalar core** (`Native`): the calculus of
   [The native scalar core](#the-native-scalar-core), deeply embedded.
   Formulas are `s = t`, `Q_y B` and `D_{x,y} B` only. Derivability
   `NPrf Γ A` has eight rules: Hyp, the two computation equations,
   Tr in one term, QE, DE, DI by cases and QI by progress. There are no
   connectives and no structural rules. The calculus exactly as the reports
   state it, with Tr in arbitrary templates and the witnessed DI by progress,
   is `IPrf` (`NativeInherited`); the two derive the same sequents.
2. **`T_eq`** (`Scalar`): intuitionistic natural deduction with equality
   over the iterator terms, with the axioms listed under *Ordinary
   realization*.
3. **iPRA in the usual way** (`PR`): one function symbol for every primitive
   recursive definition (zero, successor, projections, composition,
   primitive recursion) with its defining equations, `S x = 0 → ⊥`,
   injectivity of successor, and induction for quantifier-free formulas,
   over the same intuitionistic natural deduction.

### Results

| Statement | Lean | Content |
| --- | --- | --- |
| `T_eq` ≡ iPRA | `biInterp : BiInterp TeqAx PRAAx` | term translations in both directions whose composites are provably the identity: a synonymy |
| | `teq_iff_pra`, `pra_iff_teq` | each theory proves a sequent iff the other proves its translation |
| | `teq_roundTrip`, `pra_roundTrip` | every formula is provably equivalent to its round trip |
| | `teq_consistent_iff` | equiconsistency |
| consistency | `native_consistent`, `teq_consistent`, `pra_consistent` | none of the three systems derives `0 = 1`: the kernel is sound for the standard reading over the natural numbers (`NPrf.sound_std`), and the bi-interpretation carries this to `T_eq` and iPRA |
| independence of the rules | `indep_hyp`, `indep_iterZero`, `indep_iterSucc`, `indep_trOne`, `indep_qE`, `indep_dE`, `indep_dICase` | for each of seven rules, a sequent that the kernel derives and the kernel without that rule (`FPrf`) does not; six by a reading over the natural numbers (`FPrf.sound`, `Sem.Sound`), Hyp by `FPrf.ctx` |
| | `Sem.Sound.qIInd_of` | over the natural numbers the conditions for DI and DE imply the condition for QI by progress, so its independence is not reachable by such a reading |
| kernel = reports' calculus | `iprf_iff_nprf : IPrf Γ A ↔ NPrf Γ A` | Tr in one term and QI by progress derive the same sequents as Tr in arbitrary templates and witnessed DI by progress |
| | `NPrf.trEq`, `NPrf.tr`, `NPrf.dIProg` | transport in an equation template (two steps) and the two inherited rules, as derived rules of the kernel |
| no literal-zero source | `oprf_iff_nprf : OPrf Γ A ↔ NPrf Γ A` | the kernel's transport restricted to sources other than the literal `0` derives the same sequents, with no induction |
| | `zprf_iff_nprf : ZPrf Γ A ↔ NPrf Γ A` | the same for uncrossed transport in an equation template, by an equation induction and a singleton test |
| no template | `tprf_iff_nprf : TPrf Γ A ↔ NPrf Γ A`, `Tm.rep_marker`, `NPrf.repEq` | transport replaced by replacement of all occurrences of the source; a chosen template is recovered with an oversized marker |
| substitution for a parameter | `pprf_iff_nprf : PPrf Γ A ↔ NPrf Γ A`, `PPrf.aliasE`, `PPrf.trOne`, `Tm.psi_rn` | transport replaced by Param: a proper subterm is replaced only when the source is a variable; a template is recovered under a fresh alias, discharged through a `D` formula |
| substitutive discharge | `sdprf_iff_nprf : SDPrf Γ A ↔ NPrf Γ A`, `SDPrf.tr`, `SDPrf.dE`, `SDPrf.subst` | one rule in place of transport and DE; seven rules, each stable under substitution |
| QE at a variable or at `1` | `vqprf_iff_nprf : VQPrf true Γ A ↔ NPrf Γ A`, `VQPrf.qE`, `VQPrf.leibniz`, `VQPrf.aliasE` | the term argument of QE restricted to a variable or the numeral `1`; an arbitrary target is named by a fresh alias and reached by the Leibniz rule |
| the witness of DI needs both shapes | `DWPrf`, `Tm.IsWit`, `DWPrf.sound`, `dwprf_zero_incomplete`, `NFm.Simple`, `DWPrf.simple`, `dwprf_var_incomplete` | DI at the literal `0` alone does not derive `D_{x,y} (sel(y, 1, x) = 1)`, by the reading of `D` at `x = 0`; DI at variables alone derives no `D` formula in the empty context without free variables |
| the literal `0` and variables suffice as witnesses of DI | `dwprf_iff_nprf : DWPrf true true Γ A ↔ NPrf Γ A`, `DWPrf.names`, `DWPrf.namePQ`, `DWPrf.nameOf`, `DWPrf.qI`, `DWPrf.ofEq`, `EqPrf.toDW`, `NFm.nameP` | DI by cases at `0` or at a variable, and at no other term, derives what the kernel derives; every term has a name there, through the predecessor |
| the predecessor in the equational calculus | `EqPrf`, `EqPrf.pred_succ : EqPrf Γ (Tm.pred (succ t)) t`, `EqPrf.pred_zero`, `EqPrf.succ_inj`, `EqPrf.substW`, `EQ`, `EQ.eqInd`, `EQ.pred_succ`, `EQ.zf_add_zf`, `EQ.mod3_step`, `EQ.sel_cyc_zf`, `EQ.sel_add` | five rules on equations only (hypothesis, two computations, one-template transport, equation induction) derive `P(0) = 0` and `P(S t) = t`; no coverage, separation or case rule; no `Classical.choice` |
| DI at a variable, with a name for every term | `DNPrf`, `dnprf_iff_nprf : DNPrf Γ A ↔ NPrf Γ A`, `dwprf_complete_iff_names`, `DNPrf.toDW`, `DNPrf.name`, `DNPrf.dIVar`, `DNPrf.aliasE`, `DNPrf.qI`, `DNPrf.leibniz`, `DNPrf.dIEq`, `DNPrf.dICase`, `DNPrf.ren`, `NFm.aliasM_subst` | the introduction takes no term: its witness is a variable, and the axiom scheme `D_{x,y} (sel(y, a, x) = a)` names every term; equivalent to the kernel on all sequents |
| QE at variables only is weaker | `vqprf_var_incomplete`, `VQPrf.zsound`, `NFm.zt` | `Q_y (sel(y, 0, 1) = 0) ⊢ 0 = 1` is derivable in the kernel and not with QE at variables only; the countermodel reads variables as `0` and `Q`, `D` formulas as true |
| uncrossed one-term transport | `uprf_iff_nprf : UPrf Γ A ↔ NPrf Γ A` | from `s = t` and `h(s) = r` infer `h(t) = r`: the crossing is not essential when sources are unrestricted |
| one introduction rule | `wprf_iff_nprf : WPrf Γ A ↔ NPrf Γ A` | the seven-rule calculus with the single, syntax-directed introduction derives the same sequents |
| seven rules | `mprf_iff_nprf`, `mprf_iff_iprf : MPrf Γ A ↔ IPrf Γ A` | one-term transport at sources other than the literal `0` and the single introduction together derive the sequents of the reports' calculus |
| substitution-stable introduction | `gprf_iff_nprf : GPrf Γ A ↔ NPrf Γ A`, `GPrf.subst` | one introduction whose mode is read off the diagonal shape of the matrix; closed under substitution by direct induction |
| one-iterator selector | `miprf_iff_nprf : MiPrf Γ A ↔ NPrf Γ A`, `m6prf_iff_nprf : M6Prf Γ A ↔ NPrf Γ A`, `MiPrf.ren` | the single introduction with the mirror test `a = I(y, a; u.h)`; seven rules, and six with reflexivity and Eval; closed under injective renaming |
| six rules, substitution-stable | `sprf_iff_nprf : SPrf Γ A ↔ NPrf Γ A`, `SPrf.subst` | Hyp, Refl, Eval, QE, DE and the diagonal DI: closed under substitution by direct induction; the equivalence uses `propext` and `Quot.sound` only |
| three families, evaluation at the discharge | `e3prf_iff_vprf : E3Prf Γ A ↔ VPrf Γ A`, `e3prf_iff_nprf_of_qfree`, `E3Prf.toVPrf`, `VPrf.toE3`, `E3Prf.theta`, `Rho`, `Rho.functional`, `Rho.total`, `UCl.rn` | Use, Intro and one rule that opens `D B`, evaluates one step `ρ_E(F)` and discharges the witness, in place of Eval and Elim; equivalent to uniform clause use on every clause context, without `Classical.choice` |
| one-body contexts | `obprf_iff_nprf : OBPrf (Γ.map NFm.gb) A ↔ NPrf Γ A` for `Q`-free `Γ`, `A`; `obprf_unQ_iff_nprf`, `obprf_iff_cprf`, `OBPrf.toNPrf`, `CPrf.toOB`, `OBPrf.conv`, `OBPrf.access`, `OBPrf.gtZero`, `LEq`, `Org`, `NFm.gt`, `NFm.gb` | Refl, Eval, Use, Open and Intro with a context of single bodies `B(y)` read as `B(0) → ∀y B(y)`; an assumption is a gate body; no antecedent field and no hypothesis rule |
| five rules, clauses | `cprf_iff_nprf : CPrf (asm ∘ unQ) Γ (unQ A) ↔ NPrf Γ A`, `cprf_iff_nprf_of_qfree`, `CPrf.qfree` | Refl, Eval, Use, Elim and Intro on Eq/D formulas with clause contexts; no `Q`, no computation axiom, no transport rule |
| five rules, clauses, substitution-stable | `kprf_iff_nprf_of_qfree`, `kprf_iff_nprf`, `KPrf.subst`, `KPrf.qfree` | the clause calculus with the diagonal introduction; closed under substitution by direct induction |
| four families, one axiom clause | `vprf_iff_cprf`, `vprf_iff_nprf_of_qfree` | Use, Eval, Elim, Intro with clauses of at most one antecedent and the fixed clause `[; y. y = y]`; no reflexivity rule |
| six rules | `eprf_iff_nprf : EPrf Γ A ↔ NPrf Γ A`, `eprf_iff_iprf` | Hyp, Refl, Eval, QE, DE and the single DI: one rule for equality and computation, no computation axiom and no template |
| one computation rule | `nzprf_iff_nprf : NZPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `nzprf_iff_pra` | the kernel without the zero computation rule, on zero-normal terms with normalizing substitution, derives the normal form of every kernel sequent and nothing else |
| six rules, zero-normal | `nrprf_iff_nprf : NRPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `NRPrf.normal` | no zero computation rule and one introduction, progressive exactly at a literally reflexive normalized base |
| full normal forms | `Tm.full`, `Tm.nbe`, `Tm.nbe_sub`, `Tm.nbe_nbe`, `Tm.full_subst_congr`, `NPrf.eqFull`, `equivFull` | the normalizer for both computations, by evaluation; its coherence with substitution and renaming; correctness in the kernel |
| no computation rule | `fnprf_iff_nprf : FNPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A`, `fnprf_iff_nprf_of_normal`, `fnprf_iff_pra` | Hyp, Refl, Tr, QE, DE, DI by cases and QI by progress on full normal forms; both computation equations hold by syntax |
| opening with an inferred witness | `foprf_iff_nprf : FOPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A`, `NFm.owit`, `NPrf.owitQ`, `NPrf.toFO` | DE replaced by the opening at the witness read off two rows of the normalized matrix |
| substitution for a variable only | `vsprf_iff_nprf : VSPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A`, `VSPrf.packet`, `NPrf.toVS` | on full normal forms, `x = t`, `u = v` ⊢ `v = u[t/x]` is the only equality rule; transport by a naming packet |
| equality at the discharge of a witness | `nmprf_iff_nprf : NMPrf (Γ.map NFm.full) A.full ↔ NPrf Γ A`, `NMPrf.packet`, `NMPrf.dE` | six rules on full normal forms: Name in place of transport and DE |
| six rules on full normal forms | `f6prf_iff_nprf : F6Prf (Γ.map NFm.full) A.full ↔ NPrf Γ A`, `F6Prf.dIZero`, `FNPrf.toF6` | Hyp, Refl, Tr, QE, DE and one introduction selected by the matrix and the witness; no computation rule |
| five rules on full normal forms | `n5prf_iff_nprf : N5Prf (Γ.map NFm.full) A.full ↔ NPrf Γ A`, `n5prf_iff_pra`, `NMPrf.toN5` | Hyp, Refl, Name, QE and one introduction; formula contexts |
| three rule families on full normal forms | `wdprf_iff_nprf : WDPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A`, `wdprf_iff_nprf_of_qfree`, `wdprf_iff_pra`, `WDPrf.qfree`, `N5Prf.toWD` | Use, Intro and Name with clause contexts and the reflexivity clause; no `Q` |
| three rule families with an inferred witness | `ocprf_iff_nprf : OCPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A`, `ocprf_iff_nprf_of_qfree`, `ocprf_iff_pra`, `OCPrf.qfree`, `OCPrf.packet`, `NFm.owit_rn`, `NFm.not_otest_tz`, `NPrf.toOC` | Use, Intro and Open at the witness read off two rows; no transport, no supplied term, no `Q` |
| three rule families with a deterministic discharge | `xcprf_iff_nprf : XCPrf (UCl.refl :: Γ.map fun X => UCl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A`, `xcprf_iff_nprf_of_qfree`, `xcprf_iff_pra`, `XCPrf.qfree`, `XCPrf.dE`, `XCPrf.packet`, `XCPrf.toWD`, `F6Prf.toXC` | Use, Intro and Discharge: the clause is opened at the fresh variable and the selected witness is substituted in the exported formula |
| substitution for the newest variable | `v0prf_iff_nprf : V0Prf (Γ.map NFm.full) A.full ↔ NPrf Γ A` | the rule of `VSPrf` restricted to the variable of index `0` |
| seven uniform rules, `Q` at an equation read as progressivity | `rprf_emb_iff : RPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A`, `rprf_iff_rd : RPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd`, `REquivIn.emb_rd`, `rprf_iff_pra`, `rprf_emb_iff_pra`, `RPrf.toNPrf`, `rprf_consistent`, `NPrf.toR`, `NEquiv.rd_emb`, `RPrf.eqInd`, `RPrf.leibniz`, `RPrf.subst` | QE, DE and DI read their mode off the matrix root; equivalence with the kernel through the padding translation |
| no odd cycle of the successor without progress | `NoInd.no_odd_cycle : K Γ (S^(2i+1) c = c) → K Γ (0 = 1)`, `NoInd.no_succ_fixed`, `NoInd.succ_ne_self`, `NoInd.zf3`, `Rules.noInd`, `NoInd.cases` | the kernel without `Q` by progress refutes `S c = c` and every successor cycle of odd length; a constraint on any countermodel for the independence of that rule |
| the seed cannot be fixed to zero | `ZTm.mono`, `ZTm.no_zero_test`, `Tm.val_zf` | zero-seeded recursor terms denote monotone functions; the kernel's terms define the zero test |
| replacement of one occurrence | `lprf_iff_nprf : LPrf Γ A ↔ NPrf Γ A`, `lprf_iff_uprf`, `Reach.subst`, `LPrf.ofReach`, `Tm.Hole`, `Tm.Free` | transport replaced by replacement at one hole of a term context, below binders as well |
| the reflexive-base introduction on raw terms | `rrprf_iff_nprf : RRPrf Γ A ↔ NPrf Γ A`, `rrprf_iff_pra`, `NFm.isRefl_rn`, `RRPrf.ren`, `RRPrf.decS`, `RRPrf.decT`, `RRPrf.qInd` | seven rules without normalization; progress exactly when `B(t, 0)` is literally `r = r` |
| the public language is necessary | `pgprf_not_trans`, `pgprf_strictly_weaker : ∃ Γ A, NPrf Γ A ∧ ¬ PGPrf Γ A`, `PGPrf.sound`, `Colour.T_recolor`, `Colour.T_Q_eq`, `Colour.tr_sound` | transitivity between variables is not derivable with the root-determined introduction and transport at iterator sources; a sound reading with a non-transitive equality |
| transport at iterator sources alone | `TIPrf`, `PGPrf.toTI`, `TIPrf.ofDIEta`, `tiprf_pub_iff (g : Gating) : TIPrf (Γ.map (NFm.pub g)) (A.pub g) ↔ NPrf Γ A`, `tiprf_pubD_iff`, `TIPrf.sound`, `tiprf_not_trans`, `tiprf_strictly_weaker : ∃ Γ A, NPrf Γ A ∧ ¬ TIPrf Γ A` | the kernel with its two introductions and transport at iterator sources only: complete on a public language, and transitivity between variables is not derivable, so the source restriction alone causes that loss |
| the root-determined introduction alone | `rdprf_pub_iff (g : Gating) : RDPrf (Γ.map (NFm.pub g)) (A.pub g) ↔ NPrf Γ A`, `rdprf_not_cases`, `rdprf_strictly_weaker : ∃ A, NPrf [] A ∧ ¬ RDPrf [] A`, `RDPrf.sound`, `Prog.T`, `nprf_cases_example`, `pgprf_not_cases` | complete on a public language with unrestricted transport; on arbitrary formulas the introduction by cases of an equation is not derivable, by the progressive reading over the natural numbers |
| a public language without `Q` | `pgprf_pubD_iff : PGPrf (Γ.map NFm.pubD) A.pubD ↔ NPrf Γ A`, `pgprf_pubD_iff_pra`, `NFm.pubD_noQ`, `NFm.pubD_guarded`, `NEquiv.pubD`, `PGPrf.atomE`, `PGPrf.atomI`, `PGPrf.dumE`, `PGPrf.dumI` | formulas built from the paired binder and guarded equations only; no `Classical.choice` |
| the guarded public languages | `pgprf_pub_iff (g : Gating) : PGPrf (Γ.map (NFm.pub g)) (A.pub g) ↔ NPrf Γ A`, `pgprf_pub_iff_pra`, `Gating.gate`, `Gating.mirror`, `NFm.pub_guarded`, `NFm.pub_mirrored`, `NEquiv.pub`, `PGPrf.trW`, `PGPrf.subst` | the root-determined introduction and transport at iterator sources only, on formulas whose atomic matrices are guarded (two-sided, or the one-sided mirror guard); no `Classical.choice` |
| the mixed closure | `mcprf_iff_rprf : MCPrf Γ A ↔ RPrf Γ A`, `mcprf_iff_rd`, `mcprf_emb_iff`, `mcprf_consistent` | the uniform rules with transport in formula templates as primitive |
| the target-directed elimination of `Q` | `tqprf_iff_rprf : TQPrf Γ A ↔ RPrf Γ A`, `tqprf_iff_rd : TQPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd`, `tqprf_emb_iff : TQPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A`, `tqprf_consistent`, `TQPrf.eqInd`, `TQPrf.orbit`, `TQPrf.ren` | QE with one target: a successor target asks for the predecessor instance, any other target for the instance at zero |
| five rules with clauses and substitution for the newest variable | `vcprf_iff_nprf : VCPrf (Γ.map fun X => Cl.asm (NFm.unQ X).full) (NFm.unQ A).full ↔ NPrf Γ A`, `vcprf_iff_nprf_of_qfree`, `vcprf_iff_pra`, `VCPrf.qfree`, `VCPrf.packet`, `Cl.rep`, `Cl.Inv`, `F6Prf.toVC` | Refl, Sub, Use, Elim and Intro with clause contexts; no `Q`, no transport in a template |
| five rules on zero-normal terms | `zcprf_iff_nprf : ZCPrf (Γ.map fun X => Cl.asm (fnf (unQ X))) (fnf (unQ A)) ↔ NPrf Γ A`, `zcprf_iff_nprf_of_qfree`, `CPrf.toZC`, `Conv` | Refl, one Eval scheme, Use, Elim and Intro on zero-normal terms with clause contexts |
| four schemes on zero-normal terms | `zvprf_iff_zcprf`, `zvprf_iff_nprf` | Use, Step, Open, Close with uniform clauses and the fixed reflexivity clause |
| seed evaluation | `nvprf_iff_nprf : NVPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `NVPrf.normal` | on zero-normal terms, reflexivity and SeedEval in place of successor computation and transport |
| one evaluation rule, six rules | `zeprf_iff_nprf : ZEPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `zeprf_iff_pra`, `ZEPrf.normal`, `ZN.dICase`, `ZN.qInd` | on zero-normal terms, reflexivity, the rule UE and the single introduction with the literal test |
| equality in the initializer | `niprf_iff_nprf : NIPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `niprf_iff_pra`, `NIPrf.normal`, `NIPrf.root`, `NIPrf.trOneNf` | on zero-normal terms, replacement of an iterator's initializer as the only equality rule; no reflexivity rule and no template |
| one successor step | `nsprf_iff_nprf : NSPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `NSPrf.normal` | on zero-normal terms, reflexivity and Step in place of successor computation and transport |
| | `NZPrf.normal`, `nzprf_iff_nprf_of_normal` | it derives only zero-normal formulas from zero-normal hypotheses, and on those sequents it agrees with the kernel |
| crossed transport | `rprf_iff_nprf : RPrf Γ A ↔ NPrf Γ A`, `reversal_iff_pra` | root-reversing transport and QE with nonzero sources; equality recovered without induction |
| closure criterion | `Teq.closure_iff_progress` | for quantifier-free `φ`, with `B = φ(0)`, `C = B → ∀y φ(y)` and `P = ∀y (φ(y) → φ(S y))`: `T_eq ⊢ (C ↔ P) ↔ (¬B → P)`; and `P → C` always |
| | `Teq.ex_closure_iff_progress` | after binding a parameter `x` existentially, as in the reading of `D`: `T_eq ⊢ (∃x C ↔ ∃x P) ↔ ((∃x ¬B) → ∃x P)` |
| uniqueness of iteration | `NPrf.uniq` | from `f(S z) = h(f(z))` with `z` fresh, `f(t) = I(t, f(0); u.h)`: a derived rule of the kernel, by one equation induction |
| native → `T_eq` | `NPrf.sound` | `NPrf Γ A → Γ.map toFm ⊢[TeqAx] A.toFm` for the ordinary readings of `Q` and `D` |
| `T_eq` → native | `NPrf.ofPrf` | `Γ ⊢[TeqAx] φ → NPrf (Γ.map ofFm) (ofFm φ)`, where `ofFm` replaces each connective by its native macro |
| native = `T_eq` | `NPrf.iff_teq`, `Teq.iff_native` | faithfulness of both readings |
| | `NEquiv.ofFm_toFm`, `Teq.iff_toFm_ofFm` | both round trips are the identity up to interderivability / provable equivalence |
| native ≡ iPRA | `native_iff_pra`, `pra_iff_native` | the native calculus proves a sequent iff iPRA proves its reading, and conversely |
| | `native_roundTrip`, `pra_native_roundTrip` | both composites through iPRA are the identity up to equivalence |
| | `native_inconsistent_iff` | `NPrf [] (0 = 1)` iff iPRA proves `⊥` |

The main chain (every module except the twenty kernel comparisons,
`ZeroNormalization`, `NativeZeroNormal`, `NativeZeroStep`, `NativeZeroSeed`, `NativeZeroEval`, `NativeInitializer`,
`NativeZeroReflexive`, `NativeZeroClausal`, `FullNormalization`, `NativeFullNormal`,
`NativeInferredWitness`, `NativeVariableSubstitution`, `NativeNewestVariable`, `NativeWitnessDischarge`, `NativeFullSix`,
`NativeFullFive`, `NativeNameClauses`, `NativeOpenClauses`, `NativeExportClauses`,
`NativeVariableClauses`, `NativeProgressive`, `NativeProgressiveRules`,
`NativeProgressiveLeibniz`, `NativeProgressiveEmbedding`, `NativeTargetClosure`,
`NativeProgressiveRoundTrip`, `NativeMixedClosure`, `NativePublic`, `NativePublicD`, `NativePublicNecessary`, `NativeRootDetermined`, `NativeIteratorSource`,
`NativeRawReflexive`, `NativeOneOccurrence`, `NativeNoFixedPoint`,
`ZeroSeedObstruction`,
`NativePrefix`, `NativeUniqueness`, `NativeModels`, `NativeWitnessShape`,
`NativeWitnessComplete`, `EqKernel`, `EqArith`, `EqParity`, `EqCompare`, `EqPred` and
`TeqClosure`) is 4,872
lines; it was 5,984 before the shortening passes. The larger cuts: cut for
natural deduction is a six-line induction on the context, by implication
introduction and elimination, instead of an induction over the seventeen
rules; weakening and substitution share one induction; simultaneous
congruence uses one extra variable; the equality bootstrap of the native
calculus is four single rule applications; reflection of quantifier-free
formulas is proved as an equivalence of Lean propositions,
`mk Γ (chi φ) = 0 ↔ Γ ⊢ φ`, from which the formula of `T_eq` follows. A dependency-closure scan of the
end results, computed inside Lean from the proof terms, finds no further
unused theorem apart from `rfl` lemmas that `simp` uses silently and the
derived rule `NPrf.eqInd`, which only the comparison modules use; a duplicate
of `NFm.map_shift_subst_repl` was removed. In the arithmetic of `T_eq`,
`Q.eqInd` finds its base and its step by `simp` when they are not given, the
computation lemmas of the iterator-defined operations are single terms where
the instance of the computation equation is the statement up to unfolding, and
a quotient induction with one closing step is one line. In the round trip
through iPRA, a recursion which ignores its counter is the iterator of any
provably equal body (`Q.prc_itG`), by one equation induction; that the
iterator respects its body is two instances of it, so no separate uniqueness
or body-congruence induction remains. In the native calculus, ex falso is one
transport of the selector `sel(v, 0 = 0, A)` along `0 = 1` (`NPrf.botE`),
in place of an induction on the formula, and the two collapses of a
trivially guarded `Q` (`NEquiv.qSel`, `NEquiv.qGate`) are instances of one
lemma (`NEquiv.qTriv`). The round trip `T_eq → iPRA → T_eq` of a term is
the soundness of the back translation applied to the evaluation equation of
its code (`RoundTrip.sigma_tau`), not a fourth induction on terms; the
native universal quantifier `all X = X(0) ∧ Q X` is read through the
conjunction lemma and one propositional step; and case distinctions use
`Teq.casesOn` in place of coverage followed by an explicit existential
elimination and weakening. On the iPRA side, uniqueness of primitive
recursion at a parameter substitution (`ToPRA.prec_uniq`, one
quantifier-free induction) gives both the extensionality of the simulated
iterator and the round trip of a recursion symbol, and the successor
equation of that round trip is the translated axiom `FromPRA.ax_precSucc`
rather than a second proof of the same recursion equation. The equality test
of `T_eq` is the symmetric `sel(a ∸ b, b ∸ a, 1)`, whose reflection follows
from the additive witness of the order in four lines, and nine composition
lemmas of native substitution are instances of `NFm.subst_comp`. The
predecessor follows the diagonal lemma of `orbit_equality`: `Q.pred_succ` is
one equation induction on `pred (S x) = x` from the conjugacy of the
saturating counters and `bump 1 0 = 0`, so the comparator diagonal
`cmp (S x) x = 0` and the invariant `sat x (S x) = x` below the cap, each an
induction of its own, are gone (likewise in `EqPred`). The order is
obtained from the maximum identity `x + (y ∸ x) = y + (x ∸ y)` (one equation
induction) in place of a selector-guarded witness invariant, and the
logarithm counter of the pairing from the one-parameter invariant
"`2 ^ i ≤ k` implies `lgc i k = i`", so the monotonicity of `2 ^ x` and
transitivity of the order are not needed. In the native round trip, a
disjunction is read back by closure by cases on a formula (`Teq.caseAll`)
instead of coverage, existential elimination and transport of the selector;
`Q` introduction factors through `D` introduction at the witness `0` and the
dummy-witness elimination `NPrf.dDummyE`, as the article states it; the
forward half of the composite reading of `Q` is derived unshifted and then
shifted; and the elimination of a universal statement at its own variable is
one instance of `NPrf.allShiftE`. The translation into iPRA compiles iPRA
terms rather than iterator terms (`ToPRA.pcode`: projections and
compositions), so the evaluation of a code is a two-case fact about iPRA,
`FromPRA.code (pcode p)` is `sigma p` syntactically, and
`RoundTrip.sigma_tau` is one direct induction; the recursion equations of the
code of `prec f g` are proved once (`FromPRA.code_prec_zero/succ`) and the
translated defining axioms follow from them. In the foundations,
composition of renamings is a corollary of the substitution laws
(`Tm.ren_ren` via `ren_eq_sub`), the congruence and one-variable Leibniz
rules hand `Fin.cases` straight to the Leibniz rule of the calculus,
weakening and the extension maps of `Lindenbaum` are single instances of
`substWeaken`, and the quantifier congruences of `Interpretation` weaken by
`wk` without subset lemmas. In the
round trip through `T_eq`, the steps of each chain of equations are composed
directly instead of being stated twice, and the step shared by three of the
chains is one lemma (`RoundTrip.tau_subst_code`).

All modules build without `sorry` or warnings. The final theorems depend
only on Lean's `propext`, `Classical.choice` and `Quot.sound` (the `T_eq` ≡
iPRA part on `propext` and `Quot.sound` alone); there are no added axioms and
no `native_decide`.

### Modules

| Layer | Modules | Content |
| --- | --- | --- |
| syntax and logic | `Syntax`, `Term`, `Deduction`, `Interpretation` | de Bruijn substitution, iterator terms, natural deduction, term interpretations and `BiInterp` |
| theories | `Scalar`, `PR`, `Native` | `T_eq`, iPRA, the native calculus and its soundness |
| `T_eq` arithmetic | `Lindenbaum`, `TeqArith`, `TeqParity`, `TeqCompare`, `TeqPred`, `TeqEq`, `TeqReflect`, `TeqOrder`, `TeqPair`, `TeqRec` | predecessor, reflection of equality into a term, quantifier-free induction, pairing, compilation of primitive recursion |
| `T_eq` ≡ iPRA | `ScalarToPRA`, `PRAToScalar`, `RoundTripScalar`, `RoundTripPRA`, `BiInterpretation` | the two interpretations and their composites |
| zero-normal syntax | `ZeroNormalization`, `NativeZeroNormal`, `NativeZeroStep`, `NativeZeroSeed`, `NativeZeroEval`, `NativeInitializer`, `NativeZeroReflexive`, `NativeZeroClausal` | contraction of iterators with a literal-zero counter, hereditary substitution, and the equivalence of a formula with its normal form (delivered); the kernel without the zero computation rule, `NZPrf`; reflexivity and one successor step, `NSPrf`; reflexivity and seed evaluation, `NVPrf`; six rules with one evaluation rule and the literal test, `ZEPrf`; six rules with the reflexive-base introduction, `NRPrf`; five rules with clauses, `ZCPrf`, and four schemes with uniform clauses, `ZVPrf` |
| closures in `T_eq` | `TeqClosure` | decidability of quantifier-free formulas; the criterion for agreement of the conditional and the progressive closure |
| full normal forms | `FullNormalization`, `NativeFullNormal`, `NativeInferredWitness`, `NativeVariableSubstitution`, `NativeNewestVariable`, `NativeWitnessDischarge`, `NativeFullSix`, `NativeFullFive`, `NativeNameClauses`, `NativeOpenClauses`, `NativeExportClauses`, `NativeVariableClauses` | the normalizer for both computations, defined by evaluation, with its laws and its correctness; the kernel without computation rules, `FNPrf`; the same with the opening at an inferred witness, `FOPrf`; the same with substitution for a variable as its only equality rule, `VSPrf`; six rules with Name, `NMPrf`; six rules with one introduction, `F6Prf`; five rules, `N5Prf`; three rule families with clauses, `WDPrf`; the same with the opening at an inferred witness in place of Name, `OCPrf`; the same with a deterministic discharge, `XCPrf`; five rules with clauses and substitution for the newest variable, `VCPrf` |
| derived rule | `NativeUniqueness` | uniqueness of iteration |
| uniqueness in place of induction | `UrQuotient`, `UrArith`, `UrRetract`, `UrPred`, `UrMonus`, `UrReflect` | `T_UR` (`TurAx`: `T_eq` with induction replaced by uniqueness of iteration) and its terms modulo provable equality `U Γ`; common update, addition, the right inverse, rigidity and induction for zero equations; the clocks, the modified ramp, the comparator and the predecessor; truncated subtraction, diagonal descent, the Boolean identities, the accumulator, commutativity of the maximum and reflection of equality; `Tur.eqInd` and `tur_iff_teq : (Γ ⊢[TurAx] φ) ↔ (Γ ⊢[TeqAx] φ)` |
| one occurrence | `NativeOneOccurrence` | contexts with exactly one hole (`Tm.Hole`), chains of single replacements (`Reach`), and the calculus `LPrf` of `kernel_refinement` |
| raw reflexive base | `NativeRawReflexive` | the calculus `RRPrf` of `reflexive_base` on raw terms, its structural rules by injective renaming, and the equivalence with the kernel |
| public language | `NativePublic`, `NativePublicD`, `NativePublicNecessary`, `NativeRootDetermined`, `NativeIteratorSource` | the calculus `PGPrf` with the root-determined introduction and transport at iterator sources; gatings of equations (`Gating`), the translation `pub`, the predicate `PublicBy`, and the equivalence with the kernel on translated sequents; the coloured reading and the strictness of `PGPrf` on arbitrary sequents; the calculus `RDPrf` with unrestricted transport, the progressive reading, and its strictness; the calculus `TIPrf` with the introductions of the kernel and restricted transport, and its strictness; the `Q`-free translation `pubD` |
| prefix form | `NativePrefix` | a `Q`-free formula is `k` binders `D` and one equation |
| an obstruction | `ZeroSeedObstruction` | terms with a zero-seeded recursor denote monotone functions, so the seed of the iterator cannot simply be deleted |
| progressive reading | `NativeProgressive`, `NativeProgressiveRules`, `NativeProgressiveLeibniz`, `NativeProgressiveEmbedding`, `NativeTargetClosure`, `NativeProgressiveRoundTrip`, `NativeMixedClosure` | the seven uniform rules of `uniform_progress`, `RPrf`; the reading `NFm.rd` of `Q` at a literal equation as progressivity; soundness in the kernel and in iPRA, and consistency; inside `RPrf`: substitution, weakening and cut, the equality rules, equation induction, and the Leibniz rule for all formulas; the padding translation `NFm.emb` and the equivalence `rprf_emb_iff : RPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A`; the calculus `TQPrf` with the target-directed elimination, equivalent to `RPrf` on the same formulas; the second formula round trip and the faithfulness of the progressive reading |
| without progress | `NativeNoFixedPoint` | the seven rules other than `Q` by progress derive `0 = 1` from `S c = c`, and from every successor cycle of odd length |
| the equational calculus | `EqKernel`, `EqArith`, `EqParity`, `EqCompare`, `EqPred`, `NativeWitnessComplete` | `EqPrf` and the quotient `EQ Γ` with the interface of `Lindenbaum`; selector, addition, parity, three-cycle, ramp, factor map, comparator, saturating counter and predecessor, with equation cases in place of case splits; the embedding in `DWPrf` and the completeness of `0` and variables as witnesses |
| readings over the natural numbers | `NativeModels`, `NativeWitnessShape` | evaluation of terms and formulas for a reading `Sem`; the kernel with rules switched by flags, `FPrf`, and its soundness; consistency of the three systems; independence of seven rules; the kernel with the witness of DI restricted by shape, `DWPrf`, and the incompleteness of each shape alone |
| native admissible rules | `NativeStruct`, `NativeEq`, `NativeGate` | weakening, substitution, cut, `Q`-introduction, numerical cases; equality, interderivability over a context, Leibniz and transport in every template, equation induction; selector and gate formulas |
| kernel comparison | `NativeInherited`, `NativeOneContext`, `NativeOneIntro`, `NativeDiagonal`, `NativeMirror`, `NativeSix`, `NativeMinimal`, `NativeEval`, `NativeTemplateFree`, `NativeParameter`, `NativeVariableQE`, `NativeSubstitutiveDischarge`, `NativeClausal`, `NativeClausalDiagonal`, `NativeUniformClauses`, `NativeZeroSource`, `NativeReversal`, `NativeNamedWitness`, `NativeOneBody`, `NativeEvalDischarge`, `NativeAbstraction`, `NativePartialDischarge`, `NativeNewestUse`, `NativeReplacementCalculi`, `NativeNonzeroSources` | the calculus of the reports, `IPrf`, and `iprf_iff_nprf`; no literal-zero transport sources, `OPrf`, generic over the class `OKernel`, and the uncrossed rule, `UPrf`; six rules with Eval, `EPrf`; replacement without a template, `TPrf`; substitution for a parameter, `PPrf`, with injective renaming, cut and the fresh alias; QE at a variable or at `1`, `VQPrf`, with its own Leibniz rule and the countermodel for variables alone; substitutive discharge, `SDPrf`; the diagonal introduction, `GPrf`, with its own structural rules; the mirror introduction, `MiPrf` and `M6Prf`; Eval with the diagonal introduction, `SPrf`; the five-rule clause calculus, `CPrf`, with weakening, renaming and cut of assumptions; the clause calculus with the diagonal introduction, `KPrf`; uniform clause use, `VPrf`; one introduction rule, `WPrf`, generic over the class `WKernel`; both together, `MPrf`; the source restriction for uncrossed transport in an equation template, `ZPrf`, generic over the class `ZKernel`; root-reversing transport and QE, `RPrf`; DI at a variable with a name for every term, `DNPrf`, with renaming, cut and its own Leibniz rule; one-body contexts, `OBPrf`, with conversion and access by induction on the number of binders; evaluation at the discharge, `E3Prf`; backward replacement and elimination by abstraction, `APrf`, generic over the class `AKernel` (`aprf_iff_nprf`); partial evaluation at the discharge, `PDPrf`, and uniform clauses with the diagonal introduction, `KUPrf` (`pdprf_iff_kuprf`, `kuprf_iff_kprf`); Use at the newest parameter, `XNPrf` (`xnprf_iff_xcprf`); backward replacement in the kernel and with the single introduction, `BPrf` and `B7Prf`, and template-free replacement with the single introduction, `G7Prf` (`bprf_iff_nprf`, `b7prf_iff_nprf`, `g7prf_iff_nprf`); backward replacement at sources other than the literal `0` in the kernel, with the single introduction and with elimination by abstraction, `BmPrf`, `Bm7Prf` and `AmPrf`, generic over the class `BMKernel` (`bmprf_iff_nprf`, `bm7prf_iff_nprf`, `amprf_iff_nprf`; the last settles `kern:q:aqeminus`) |
| native logic | `NativeLogic` | `⊥`, `→`, `∧`, `∨`, `∃`, `∀` as native macros with all their natural deduction rules |
| native ≡ `T_eq` ≡ iPRA | `NativeTranslate`, `NativeComposite`, `NativeRoundTrip`, `NativeBiInterpretation` | translation of derivations, both round trips, the composite with `biInterp` |

The connectives are native macros. With `sel(v, A, B)` the selector formula
(`A` at `v = 0`, `B` at a successor) and `gate(v, A)` the formula trivial at
`0` and equivalent to `A` at a successor:

    ⊥        :=  0 = S 0
    A → B    :=  Q_y sel(y, A, B)
    A ∧ B    :=  Q_y gate(y, sel(par y, A, B))      par = parity iterator
    ∃x A     :=  D_{x,y} gate(y, A(x))
    A ∨ B    :=  ∃v sel(v, A, B)
    ∀x A     :=  A(0) ∧ Q_y A(y)

### Proposals and their status in Lean

| Package | Status in Lean |
| --- | --- |
| `one_context` | Adopted: its rule is the kernel's transport rule `NPrf.trOne`. The equality bootstrap became four single applications of it, and the two-template rule is the derived `NPrf.trEq`. Its seven-constructor variant is `WPrf`. The delivered modules are superseded by the kernel change. |
| `one_sided_transport` | Proved: its calculus is `MPrf` (`mprf_iff_nprf`, `mprf_iff_iprf`), and its strengthening, that the first computation equation and the restricted rule recover all equality reasoning, is the class `OKernel` (`OKernel.trOneF`, `oprf_iff_nprf`). Written here against the new kernel before the package was read; the delivered module follows the same steps. |
| `export_specialization` | Proved, for its newest-parameter calculus `𝒳_ν` (`NativeNewestUse`): `XNPrf` is `XCPrf` with Use at `Tm.newest` (the variable `0`, or `0` in an empty scope) and reflexivity at every term; `xnprf_iff_xcprf` with the reflexivity clause, and `xnprf_iff_nprf_of_qfree`. A Use at `t` is a discharge of the name formula of the normal form of `t` around a Use at the fresh variable (`XCPrf.toXN`, with a renaming and a context extension). The node count `n + 3u` is not formalized; its checker results concern Python programs. |
| `476_byte_presentation` | Proved, for the three-family calculus `PD` (`NativePartialDischarge`): `RhoPlus` is the partial evaluation step `ρ⁺` (the zero and successor rows of `ρ` and the identity only at an auxiliary formula with root `D`; `RhoPlus.toRho`); `PDPrf` has Use, the diagonal Intro of `KPrf` and the discharge through `ρ⁺`; `KUPrf` is `K^u`, the uniform clause calculus with the diagonal introduction. `pdprf_iff_kuprf` on every clause context, `kuprf_iff_kprf` with the reflexivity clause, hence `pdprf_iff_nprf_of_qfree`. The tree-preserving substitution theorem of the package is not needed for these proofs and is not formalized. Its checker results concern Python programs. |
| `abstraction_and_refinements` | Proved, for the calculus `A₇` (`NativeAbstraction`): `APrf` has hypothesis, the two computations, backward replacement `bRep` (from `s = t` and `Rep_t^s(u) = r` infer `r = u`), elimination by abstraction `aqE` (from `Q_y Rep_t^y(A)` and `Rep_t^0(A)` infer `A`), `dE` and the single introduction of `WPrf`, and `aprf_iff_nprf : APrf Γ A ↔ NPrf Γ A`. Replacement and abstraction are one operation, `Tm.rpl t v σ`, whose tests look only at the source term, so it commutes with substitution (`Tm.rpl_comp`) and with injective renaming of the source (`Tm.rpl_ren`); `APrf` is closed under weakening and injective renaming (`APrf.ren`). Equality, congruence and transport in a term template come from the first computation and `bRep` with the marker; closure by cases from the introduction at the witness `I(0, 0; u.0)`; transport in formula templates and `QE` together by induction on the number of binders (`APrf.trEl`), `QE` being `aqE` at the marker of the matrix (`NFm.abs_mark`, `NFm.rep_mark`) followed by transport along `marker = t`. Its checker results concern Python programs. |
| `kernel_refinement` | Its checker results concern Python programs. Its note on replacement in the left side of an equation is proved with a term template in place of a context with exactly one hole: `uprf_iff_nprf`. The rule of the note itself, with a context that has exactly one hole, is proved as well (`NativeOneOccurrence`): `LPrf` has LOR, from `s = t` and `C[s] = r` infer `C[t] = r` with `Tm.Hole 0 C`, and `lprf_iff_nprf : LPrf Γ A ↔ NPrf Γ A`. The reduction of a template to single occurrences is `Reach.subst`: the instances `h(s)` and `h(t)` are connected by single replacements, by induction on `h`; below a binder the hole and the bound variable are exchanged (`Reach.iterH`). |
| `compact_update` | Its checker results concern Python programs. Its closure criterion is proved in `T_eq` for every quantifier-free formula: `Teq.closure_iff_progress`, with `Teq.closure_of_progress` and the decidability lemma `Teq.qfDec` (`TeqClosure`). The variant after existential binding is `Teq.ex_closure_iff_progress`. |
| `uniform_progress` | One direction is proved (`NativeProgressive`). `RPrf` is its seven-rule calculus (Hyp, the two computations, transport in an equation template, and QE, DE, DI with the mode read off the root of the matrix). `NFm.rd` reads `Q_y E` at a literal equation as `∀y (E(y) → E(S y))`, and `D_{x,y} E` as `∃x ∀y (E(x,y) → E(x,S y))`, in the kernel's language. `RPrf.toNPrf : RPrf Γ A → NPrf (Γ.map NFm.rd) A.rd`, hence `rprf_sound_pra` and `rprf_consistent`. The only rule that needs an argument is QE at an equation (`NPrf.progE`, an equation induction). Inside `RPrf`, substitution in derivations is a direct induction (`RPrf.subst`; no rule looks at a witness), the equality rules and the kernel's transport are derived, and equation induction is recovered (`RPrf.eqInd`): the introduction at an equation with an unused witness coordinate, its elimination, and QE with the source `0`, whose conclusion `E(I(0, u; v.S v))` is `E(u)` by the first computation equation (`NativeProgressiveRules`). Transport in an arbitrary formula, which is not primitive in `RPrf`, is derived by induction on the formula (`RPrf.leibniz`, `RPrf.tr`, `NativeProgressiveLeibniz`): at a compound matrix the redex `I(0, c; v.S v)` left by QE is removed by the induction hypothesis, and at a literal equation one progress step is QE with the initializer `1` and `I(z, 1; v.S v) = S z`. The converse is proved for the translation of the package (`NativeProgressiveEmbedding`): `NFm.emb` pads every equation below a binder to the compound formula `D_{r,v} (sel(v,0,s) = sel(v,0,t))`; an equation and its padding are interderivable in `RPrf` (`RPrf.padI`, `RPrf.padE`); every kernel derivation translates (`NPrf.toR`); in the kernel the progressive reading of the translation of a formula is equivalent to the formula (`NEquiv.rd_emb`). Hence `rprf_emb_iff : RPrf (Γ.map NFm.emb) A.emb ↔ NPrf Γ A` and `rprf_emb_iff_pra`. The other formula round trip is proved too (`NativeProgressiveRoundTrip`): in `RPrf`, over every context, a formula `B` is interderivable with `emb (rd B)` (`REquivIn.emb_rd`), hence `rprf_iff_rd : RPrf Γ A ↔ NPrf (Γ.map NFm.rd) A.rd` and `rprf_iff_pra`. No rule for the connectives of `NativeLogic` is re-proved inside `RPrf`: at a literal equation, one direction is the translation of a short kernel derivation (`RPrf.progBack`); for the other, one step of progress at a term is itself a closure over an equation (`NFm.stepM`), `RPrf` derives the translation of that closure (`RPrf.stepQ`), and the kernel derives progressivity from it (`RPrf.progForth`). So the two calculi are bi-interpretable, with both round trips, on all formulas. |
| `validated_core`, `validated_presentation`, `checked_refinement` | Their results concern Python programs; the rule basis is unchanged. |
| `scalar_uniqueness` | Proved for the ordinary theory: `tur_iff_teq` (`UrQuotient` … `UrReflect`) says that `T_UR`, `T_eq` with induction for literal equations replaced by uniqueness of iteration, derives the same sequents as `T_eq`; the converse direction follows the report: the predecessor from the modified ramp, truncated subtraction, the accumulator, commutativity of the maximum and the reflection `Δ`, then zero induction on `Δ(s(n), t(n))`. The rule is also a derived rule of the kernel (`NPrf.uniq`). The native form, `U` with `UR` in place of `QI` (`kern:thm:urnative`), is not formalized. |
| `clausal_canonical` | Not formalized: it is stated on the canonical recursor syntax with clause contexts. |
| `computational_equality`, `equality_from_iteration` | Proved: the six-rule calculus is `EPrf`, with `eprf_iff_nprf` and `eprf_iff_iprf` (`NativeEval`). Eval has the two cases of `equality_from_iteration` as constructors; the third case of `computational_equality` is the derived rule `EPrf.evalId`. The zero-normal companion of `equality_from_iteration` is proved as well (`NativeZeroEval`): `ZEPrf` has its six rules, with the single rule UE for arithmetic and equality and the single introduction with the literal test at canonical witnesses, and `zeprf_iff_nprf : ZEPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`. The missing introduction by cases of an equation at the witness `0` is derived as in `NativeOneIntro`, with the zero-normal term `I(S 0, 0; u.0)` as the alias of `0`. |
| `clause_guards` | Proved: its calculus is `KPrf` (`kprf_iff_nprf_of_qfree`, `kprf_iff_nprf`, `KPrf.subst`; `NativeClausalDiagonal`), which was written here before the package arrived. |
| `mirror_core` | Proved: its six-rule calculus is `M6Prf` (`m6prf_iff_nprf`), over the seven-rule `MiPrf` (`miprf_iff_nprf`; `NativeMirror`). Because the mirror shape can be created by a substitution, the structural rules are weakening, injective renaming and cut; progress for an arbitrary equation uses the lift `s = sel(y, s, t)`. |
| `seed_evaluation` | Proved, for its arithmetic and equality interface: `NVPrf`, with `nvprf_iff_nprf`, `NVPrf.normal` and `nvprf_iff_pra` (`NativeZeroSeed`), with the kernel's two introductions and `Q` in place of clause contexts. |
| `clause_contexts` | Proved: its four schemes with the reflexivity clause are `ZVPrf`, with `zvprf_iff_zcprf` and `zvprf_iff_nprf` (`NativeZeroClausal`). |
| `witness_discharge` | Proved, for the kernel: `NMPrf` is the kernel on full normal forms with Name in place of transport and DE (six rules), and `nmprf_iff_nprf` (`NativeWitnessDischarge`). The package's own form is proved as well: `WDPrf` has clause contexts, the fixed reflexivity clause and the three families Use, Intro and Name, and `wdprf_iff_nprf` proves it equivalent to the kernel on `Q`-free forms in full normal form (`NativeNameClauses`). The proof translates the five-rule calculus `N5Prf`; weakening and renaming of `WDPrf` are direct inductions. |
| `inferred_witness`, `deterministic_opening`, `first_instance`, `clause_discharge` | Proved, for the kernel: the opening at the witness read off the rows `B(b, 0)` and `B(b, 1)` of the normalized matrix, in place of DE, is `FOPrf`, with `foprf_iff_nprf` (`NativeInferredWitness`). The form with clause contexts, the three families Use, Intro and Open and the reflexivity clause is proved as well: `OCPrf` and `ocprf_iff_nprf` (`NativeOpenClauses`). It has no transport rule; transport comes from a packet on which Open selects the target, and the kernel's DE is translated under the substitution of the selected witness. That is the rule of `inferred_witness` and `deterministic_opening` (the clause is opened at the selected witness and the goal is unchanged). `first_instance` and `clause_discharge` instead open at the fresh variable and substitute the selected witness in the exported formula; that is `XCPrf`, with `xcprf_iff_nprf` (`NativeExportClauses`). There the ordinary elimination of `D` is a derived rule, and the proof is a rule-by-rule translation of `F6Prf`. |
| `substitutive_discharge` | Proved, for the kernel: its discharge rule in place of transport and DE is `SDPrf`, with `sdprf_iff_nprf` (`NativeSubstitutiveDischarge`). The package's four families are stated on the canonical recursor syntax with clause contexts, which is not formalized. |
| `prefix_clauses` | Its representation is proved: `NFm.Pre k A` says that `A` is `k` binders `D` followed by one equation; a formula has that form exactly when it is `Q`-free (`NFm.qfree_iff_pre`), `k` is unique (`NFm.Pre.unique`) and unchanged by substitution (`NFm.Pre.subst`), and from `Q`-free assumptions `VPrf` derives only such formulas (`VPrf.pre`, `NativePrefix`). The calculus of the package is `VPrf` on that representation. Its second theorem, on clauses without an antecedent field, is not formalized. |
| `uniform_binding` | Not formalized: the counter-aware recursor syntax. |
| `parameter_substitution` | Proved, for the equality rule: `PPrf` is the kernel with transport replaced by Param, and `pprf_iff_nprf` (`NativeParameter`). The package's five instruction families combine it with clause contexts and the witness-tested single introduction, which are not formalized together with it. |
| `variable_substitution` | Proved, for the kernel: `VSPrf` is the kernel on full normal forms with the rule `x = t`, `u = v` ⊢ `v = u[t/x]` in place of transport, and `vsprf_iff_nprf` (`NativeVariableSubstitution`). Transport is recovered by the two-row naming packet (`VSPrf.packet`). The restriction of the source to the newest variable is `V0Prf`, with `v0prf_iff_nprf` (`NativeNewestVariable`): the same proof applies, because the packet substitutes only for the witness it has just opened and no derivation is renamed. The clausal five-rule form is `VCPrf`, with `vcprf_iff_nprf` (`NativeVariableClauses`): the six-rule calculus `F6Prf` is translated under an arbitrary renaming, a hypothesis being represented by its assumption clause or, for `Q_y B`, by the closure clause; premises needed under further variables come from the induction hypothesis at a shifted renaming, which is the package's protected translation. |
| `uniform_step` | Proved: its arithmetic and equality interface on zero-normal terms is `NSPrf` (`nsprf_iff_nprf`, `NSPrf.normal`, `nsprf_iff_pra`; `NativeZeroStep`), with the kernel's two introductions and `Q` in place of clause contexts. On the unnormalized syntax the rule Step is the constructor `evalSucc` of `EPrf` and `SPrf`. |
| `uniform_clauses` | Proved: its calculus is `VPrf`, with `vprf_iff_cprf` and `vprf_iff_nprf_of_qfree` (`NativeUniformClauses`). |
| `deterministic_specialization` | Proved, for the kernel: QE at a variable or at the numeral `1` derives the same sequents (`vqprf_iff_nprf`, `NativeVariableQE`), and QE at variables alone does not (`vqprf_var_incomplete`). The package's own form, on zero-normal terms with clause contexts and the positional choice of the target (the newest clause at `1`, an older one at the newest eigenparameter), is not formalized; that choice is not stable under renaming, and the package handles it by regenerating premise proofs. |
| `clausal_single_evaluation` | Proved: its calculus `C5` is `ZCPrf`, with `zcprf_iff_nprf` and `zcprf_iff_nprf_of_qfree` (`NativeZeroClausal`). Completeness is by normalizing derivations of `CPrf`. |
| `full_normalization`, `computation_normal` | Proved: the normalizer of both computations is `Tm.full` (`FullNormalization`), defined by evaluation, so that totality and uniqueness of normal forms need no proof and the coherence with substitution is `Tm.full_subst_congr`; the kernel without computation rules is `FNPrf` (`fnprf_iff_nprf`, `NativeFullNormal`), and the packages' six-rule calculus with the single witness-selected introduction is `F6Prf` (`f6prf_iff_nprf`, `NativeFullSix`). The repair of case introduction at a witness that normalizes to `0` is `F6Prf.dIZero`; it differs from the packages' compound envelope. |
| `counter_evaluation` | Not formalized: the counter-aware recursor syntax. |
| `raw_clausal`, `reduced_clause_calculus`, `clausal_two_case`, `rootfree_clausal` | Proved, for the raw calculus with the two-case Eval: `CPrf`, with `cprf_iff_nprf`, `cprf_iff_nprf_of_qfree` and `CPrf.qfree` (`NativeClausal`). Completeness is by translating the six-rule calculus `EPrf` rule by rule. The zero-normal clause calculus is `ZCPrf` (`NativeZeroClausal`). |
| `reflexive_base` | Proved: its six-rule calculus on zero-normal terms is `NRPrf`, with `nrprf_iff_nprf`, `NRPrf.normal` and `nrprf_iff_pra` (`NativeZeroReflexive`). Its raw seven-rule variant is proved as well (`NativeRawReflexive`): `RRPrf` has ordinary substitution and one introduction whose mode is progress exactly when the zero instance `B(t, 0)` of the matrix is literally `r = r`; `rrprf_iff_nprf : RRPrf Γ A ↔ NPrf Γ A`. The test is not stable under substitution, so the structural rules are weakening, injective renaming and cut, as for `mirror_core`; progress for an arbitrary equation uses the package's asymmetric lift `sel(y, t, s) = sel(0, t, s)` and its two decoder equations. |
| `zero_normal` | Its normalization layer is adopted as `ZeroNormalization`: the delivered module compiled unchanged. On top of it `NativeZeroNormal` proves the deletion of the zero computation rule for the kernel (`nzprf_iff_nprf`, `NZPrf.normal`, `nzprf_iff_pra`), with the kernel's two introductions and unrestricted sources. A six-rule form on zero-normal terms with a single introduction is proved as `NRPrf`, with the mode test of `reflexive_base` in place of the test on the witness. |
| `diagonal_guard` | Proved: its calculus is `GPrf`, with `gprf_iff_nprf`, `gprf_iff_iprf` and substitution by direct induction (`NativeDiagonal`). Progress for an arbitrary equation is recovered by a shorter argument than the report's: no implication between equations and no substitution into the step premise. The equivalence uses neither `Classical.choice` nor the bi-interpretation. |
| `template_free` | Proved, for the equality rule: `TPrf` is the kernel with transport replaced by the replacement rule, and `tprf_iff_nprf` (`NativeTemplateFree`). The package's seven-rule form combines it with the witness-tested single introduction, which is not combined here. |
| `target_closure` | Its calculus and its comparison theorem are proved (`NativeTargetClosure`). `TQPrf` has the rules of `RPrf` with the elimination `Q_y B`, `B(δ_B(t))` ⊢ `B(t)`. `tqprf_iff_rprf : TQPrf Γ A ↔ RPrf Γ A`: a step of `TQPrf` is the orbit elimination with the initializer `1`; a target that is not a successor is the orbit elimination from `0`, with the redex removed by the Leibniz rule; conversely the orbit elimination at an equation is an equation induction inside `TQPrf` (`TQPrf.orbit`), whose own induction uses the target `I(0, t; u.0)`. Hence `tqprf_emb_iff`, `tqprf_iff_rd` and `tqprf_consistent`. The package's second part, a smaller checker for an existing theory, is not a statement about a calculus. |
| `initializer_equality` | Proved, for its equality rule (`NativeInitializer`). The package is stated on zero-normal iterator terms, not on another term syntax. `NIPrf` has, in place of transport, the rule Seed: from `s = t` and `C(c, s, h) = r` infer `C(c, t, h) = r`, where `C(0, a, h)` is `a`. `niprf_iff_nprf : NIPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`. At the counter `0` the rule replaces at the root, which gives reflexivity from one successor computation, symmetry and transitivity; at the counter `1` it applies any template. The package's sixth-rule count uses the single introduction; `NIPrf` keeps the kernel's two introductions (seven rules). |
| `scope_kernel` | Not formalized: it concerns Python programs, and its research notes are a model and an unfinished argument. |
| `canonical_recursors` | Not formalized. It is a different term language (a recursor whose seed is a successor, with a canonical grammar and normalizing substitution), so it would need its own syntax, its equivalence with the raw calculus and a bi-interpretation with iPRA. |
| `witness_rule` (first delivery) | Proved: `wprf_iff_nprf`. The kernel keeps two introductions, because the single rule is not stable under substitution by a direct induction (a substitution can turn a witness into the literal `0`). |
| `direct_closure`, `direct_closure_qprogress` | Adopted: `qIInd` is the kernel's progress rule. The delivered migration patch compiled as written. |
| `source_dispatch` | Proved twice: `zprf_iff_nprf` for its own uncrossed rule, and `oprf_iff_nprf` for the kernel's rule, where it needs no induction. The kernel keeps unrestricted sources, because substitution into derivations (`NPrf.subst`) is not admissible in the restricted calculus. |
| `reversal_core` | Adopted as `NativeReversal`: the delivered module compiled after four typed-target fixes (`rprf_iff_nprf`, `reversal_iff_pra`, `pra_iff_reversal`). |
| `guarded_source` | Its key lemma is proved: the class `ZKernel` has no logical rule, only equation induction, and `ZKernel.trF` recovers unrestricted transport from it. Its guarded public language is formalized in the common form of `NativePublic` (see `protected_core` below). |
| `deterministic_auxiliary`, `guarded_orbit` | Their aim, source selection together with a root-determined introduction, is proved on the full native language as `mprf_iff_nprf`. The guarded public language is proved in a common form (`NativePublic`, `pgprf_pub_iff`); their auxiliary formulas are not formalized. |
| `protected_core` | Proved, in the native language (`NativePublic`). `PGPrf` is the kernel with the root-determined introduction and with transport at iterator sources only; `NFm.pub .gate` puts every equation under the closure of its gate, so that every atomic matrix is guarded and the two sides of an opened gate are iterators; `NFm.pub_guarded`, `NEquiv.pub`, and `pgprf_pub_iff .gate : PGPrf (Γ.map pub) (pub A) ↔ NPrf Γ A`. The proof uses neither `Classical.choice` nor the bi-interpretation. The package's grammar, the paired binder over guarded equations with `Q` only in contexts, is reached by `NFm.pubD` (`NativePublicD`, `pgprf_pubD_iff`, `NFm.pubD_noQ`). Remaining differences from the package: equations at the root are gated, not wrapped as `W(s) = W(t)`; the certificate format is not modelled. |
| `mirror_guard` | Proved, in the native language (`NativePublic`): the one-sided guard `s = I(w, s; u.t)` is the gating `Gating.mirror`, every atomic matrix of a translated formula is mirrored (`NFm.pub_mirrored`), and `pgprf_pub_iff .mirror : PGPrf (Γ.map pub) (pub A) ↔ NPrf Γ A`, with the root-determined introduction and with transport at iterator sources only, which is stronger than the package's exclusion of the literal `0`. An opened mirror gate `s = J`, `J = I(S 0, s; u.t)`, gives `J = s` and `J = t`, hence the wrapped equation. The same differences from the package as for `protected_core` apply. |
| `guarded_core` | Its aim, one root-determined introduction, is reached without changing the formula language by `wprf_iff_nprf`. Its own route through guarded atomic matrices is proved in the common form of `NativePublic` (`pgprf_pub_iff`), with `Q` kept as a formula; clause contexts in place of `Q` are not formalized. |
| `scope_and_closure` | Its checker results concern Python programs. Its mixed closure is proved (`NativeMixedClosure`): `MCPrf` is the uniform calculus with transport in an arbitrary formula template as its primitive equality rule, and `mcprf_iff_rprf : MCPrf Γ A ↔ RPrf Γ A`, since that transport is a derived rule of `RPrf`. Hence `mcprf_iff_rd`, `mcprf_emb_iff` and `mcprf_consistent`. Its obstruction note is proved too (`ZeroSeedObstruction`): in a term language whose recursor has its seed fixed to zero, even with an update that sees the counter, every term denotes a function that is nondecreasing in each variable (`ZTm.mono`), so no term is the zero test (`ZTm.no_zero_test`), while `sel(x, 1, 0)` of the kernel's language is (`Tm.val_zf`). The statement is about denotations in the natural numbers only. |
| `deterministic_introduction` | Proved, for the kernel, in the form with a free choice of the variable: `DNPrf` has DI at a variable and the naming scheme `D_{x,y} (sel(y, a, x) = a)` as an axiom, and `dnprf_iff_nprf : DNPrf Γ A ↔ NPrf Γ A` (`NativeNamedWitness`). The package's naming matrix `C(y, 0, x) = C(y, 0, r)` is replaced by the alias matrix `sel(y, a, x) = a` of `NativeParameter`, which needs one successor computation in place of reflexivity. The steps are the package's: name, open, introduce at the name, transport. Not formalized: the deterministic selection (the newest parameter, `0` in an empty scope, priority for a literal naming matrix) and the structural theorem it needs, weakening by renaming an old selection anew; clause contexts and the guarded public language; the checker measurements. Without the scheme each shape of witness alone is incomplete (`dwprf_zero_incomplete`, `dwprf_var_incomplete`). |
| `one_body` | Proved: its calculus is `OBPrf`, with `obprf_iff_nprf`, `obprf_unQ_iff_nprf` and `obprf_iff_cprf` (`NativeOneBody`). The rules are the package's: atomic reflexivity, the two cases of Eval, Use, Open and Intro with the witness-selected mode, on contexts of single bodies. Soundness reads a body `B` as `Q B`. Completeness is the package's translation of `CPrf` by the origin of each clause occurrence (`Org`, `CPrf.toOB`), with conversion and access proved in the order `L_0, H_0, L_1, H_1, …` as one induction on the number of binders (`OBPrf.conv`, `OBPrf.acc`). One difference: the gate at `0` is derived directly (`OBPrf.gtZero`), not by conversion from deep reflexivity. The checker measurements are not reproduced. |
| `evaluation_discharge` | Proved, for the raw calculus: its three families are `E3Prf`, with `e3prf_iff_vprf` on every clause context and `e3prf_iff_nprf_of_qfree` (`NativeEvalDischarge`). The evaluation step is the relation `Rho`, the graph of the package's `ρ`, proved functional and total. Both translations are the package's; the one from `VPrf` carries a renaming and a context extension through the induction, where the package first proves weakening and injective renaming. Not formalized: the zero-normal companion with SeedEval, and the checker measurements. |
| `parameter_intro` | Not formalized: it is stated on the counter-aware recursor with full normalization. Its introduction without a witness is the subject of `NativeNamedWitness` and `NativeWitnessShape`. Its naming theorem proves `D_{x,u} (C(u, 0, x) = C(u, 0, t))` with variables as the only witnesses, by cases on `y` in a formula that mentions a predecessor `P(y)`: in the successor case the witness is the case variable `z`, and `z = P(S z)` holds by normalization. On iterator terms no term has `P(S z) = z` by computation, so the argument does not transfer as it stands. What does transfer is proved: for the kernel with variables (and `0`) as the only witnesses, completeness is equivalent to the derivability of those names (`dwprf_complete_iff_names`). |
| `uniform_recursion` | Not formalized: its terms are variables, `0` and the counter-aware recursor `R(n, a; i, u.h)`, with the successor defined as `R(0, a; i, u.0)`. It needs its own syntax with a normalizer and a bi-interpretation with the iterator terms, like `uniform_binding` and `counter_evaluation`. Its three families Use, Close and Name are, by its own account, those of the control it is measured against (`inferred_witness`) on that syntax. |
| `newest_parameter`, `no_witness`, `parameter_witness`, `uniform_raw` | Their common theorem is proved for the kernel, with a free choice among `0` and the variables: `dwprf_iff_nprf : DWPrf true true Γ A ↔ NPrf Γ A` (`NativeWitnessComplete`). Their audit of the predecessor is proved as stated: `EqPrf.pred_succ` and `EqPrf.pred_zero` in a calculus of equations with hypothesis, the two computations, one-template transport and equation induction only (`EqPred`), each Boolean split replaced by an equation case. The names follow the coverage packet of the packages: the name of `P(y)` by cases, used at `S t`. Not formalized: the deterministic selection (always the newest parameter, `0` in an empty scope) with its regeneration of proofs under scope extensions; the seven-rule diagonal variant, the one-bit clause calculus and the guarded calculus with that selection; the checker measurements. |
| `conditional_copy`, `single_constructor` | Not formalized: both are stated on the counter-aware recursor on normal forms, a term syntax that is not formalized here. |
| `orbit_closure` | Its rule Orbit, in native form, is a derived rule of the kernel: `NPrf.orbit` concludes the closure `Q_y (f(y) = I(y, f(0); u.h))` from `f(S z) = h(f(z))`, with no target term, and `NPrf.uniq` is now `NPrf.orbit` followed by `QE` (`NativeUniqueness`). Not formalized: the converse (Orbit recovers equation induction), successor-only uniqueness, the translator and the audit. |
| `progress_independence`, `orbit_closure`, `crossed_uniqueness`, `inferred_major`, `smaller_envelope`, `checked_presentation`, `context_phase`, `frontier_review` | Filed on 2026-11-12; the comparison with the Lean development is in progress. `progress_independence` answers further question 1 in writing (QI by progress is independent, by a tower of ultrapowers); it is not formalized. |
| `register_graph` | Not formalized. It is a different term language (`J` with two bound variables) over ordinary logic, so it would need a second bi-interpretation with iPRA from scratch. |

### Further questions

Questions that this work raised and did not settle. None of the statements
marked as conjectures is proved here.

1. **Is the progress rule independent?** Seven of the eight rules of the
   kernel are independent (`NativeModels`). For QI by progress the method of
   readings over the natural numbers cannot work: `Sem.Sound.qIInd_of` proves
   that the conditions for DI and DE already imply the condition for QI there.
   A countermodel must have nonstandard numbers. It can have no cycle of the
   successor: from `S c = c` the kernel without QI derives `0 = 1`, by the
   iterator of `u ↦ sel(u, 1, 0)` at the count `c` and three equations proved
   by cases (`NoInd.no_succ_fixed`, `NativeNoFixedPoint`). Since
   `zf (zf (zf y)) = zf y`, the same derivation excludes every cycle of odd
   length (`NoInd.no_odd_cycle`). Cycles of even length need a counter of
   another period, whose behaviour would itself have to be established
   without induction; that is not formalized. So, granting that, its
   nonstandard part consists of
   chains infinite in both directions, and every step term definable with
   parameters needs an orbit infinite in both directions along each chain. An
   ultrapower with the internal iterator has such orbits and satisfies
   induction; the open point is a structure that has the orbits and refutes an
   instance of progress, for example `Q_y (I(y, 0; u.u) = 0)`. The term model
   of full normal forms in one variable refutes that instance and satisfies
   both computation equations, but it has elements that are neither `0` nor a
   successor, so DI by cases is not sound in it.
2. **How far can the witness of DI be restricted?** Settled for the shape
   of the witness: the literal `0` and variables are enough
   (`dwprf_iff_nprf`, `NativeWitnessComplete`), and neither alone is
   (`dwprf_zero_incomplete`, `dwprf_var_incomplete`). The predecessor that
   the argument needs is derived in a calculus of equations only
   (`EqPrf.pred_succ`). Still open in Lean: the deterministic choice of the
   packages, the newest variable or `0` in an empty scope, which is not
   stable under weakening. The rest of this item is the analysis that
   preceded the proof. QE needs only a variable
   or the numeral `1` as its target (`vqprf_iff_nprf`), and a variable alone is
   not enough (`vqprf_var_incomplete`). For DI each of the two shapes alone
   is not enough (`dwprf_zero_incomplete`, `dwprf_var_incomplete`,
   `NativeWitnessShape`). With the axiom scheme that every term has a name,
   DI at a variable is enough (`dnprf_iff_nprf`, `NativeNamedWitness`); the
   question is whether that scheme is derivable, and it is exactly that:
   with variables (and `0`) as the only witnesses, the calculus is complete
   if and only if it derives `D_{x,y} (sel(y, a, x) = a)` for every term `a`
   (`dwprf_complete_iff_names`). `parameter_intro` derives the names on the
   counter-aware recursor, where a predecessor computes. The analogous positive
   statement for DI is a
   conjecture: DI by cases at the literal `0` or at a variable is enough. A
   route: prove `Q_y D_{x,y'} (sel(y, 0, S x) = y)` by cases with the
   witnesses `0` and the fresh variable, instantiate at `y = S t`, and use the
   injectivity of the successor to name `t` by a variable. It needs the
   predecessor equation `pred (S z) = z` inside the restricted calculus.
   The restricted calculus is closed under renaming but not under
   substitution, so universal generalization is not available in it as it is
   in the kernel: a derivation of `F(w)` that introduces at the variable `w`
   gives no derivation of `F(S z)`. In particular the shorter argument
   "under `w = t` introduce at `w`, then close over `w` and instantiate at
   `t`" fails: the closure over `w` would have to be proved by cases, and at
   `w = S z` no admissible witness is equal to `t`. Whether the restricted
   calculus derives, say, `∃x (x = S 0)` in the empty context is the test
   case; the route above derives it only through the predecessor.
   Three observations, none of them formalized. (a) In the main chain the
   derived rules of the kernel use DI at `0` or at a variable everywhere
   except in `NPrf.exI` (and so in `orI₂`, which is `exI` at `1`) and in
   `NPrf.dI`; but they instantiate derivations by substitution throughout.
   (b) The restricted calculus has implication, cases on a compound formula
   (DI at the dummy witness `0`, then DE and QE) and so a hypothetical split
   of a term into `0` and a successor, without disjunction; the predecessor
   of `T_eq` uses coverage only through such splits. So the conjecture
   reduces to redoing that arithmetic inside the restricted calculus. (c) In
   a reading in which variables range over a subset `U` of the values of
   terms, the soundness of DI and of QI needs every value to be `0` or the
   successor of an element of `U`. With an injective successor that omits
   `0` this forces `U` to be everything, so a reading of that kind that
   refutes the conjecture must give up one of the two.
3. **Substitution for a variable on raw terms.** On full normal forms,
   substitution for a variable is the only equality rule needed
   (`vsprf_iff_nprf`). On raw terms the rows of the naming packet are not
   literal, and Param, which also joins two equations at the root, is proved
   sufficient (`pprf_iff_nprf`). Settled for open sequents in the article
   (chapter "Computation, equality and normal forms", from
   [`head_conversion`](Artifacts/head_conversion/)): on raw terms substitution
   for a variable alone, without joining, is strictly weaker; a reading in
   which values carry a colour separates `I(0,x;u.u) = y ⊢ x = y`. Open: the
   reading validates every theorem in the empty context, so whether those
   calculi derive all theorems of the kernel is not settled. Not in Lean.
4. **The newest variable.** Settled: `variable_substitution` restricts the
   source of its rule to the newest variable, and `v0prf_iff_nprf` proves that
   restriction sufficient on full normal forms. The rule is not stable under
   renaming, but the proof never renames a derivation.
5. **The progressive reading of `Q`.** In `uniform_progress`, and by its
   description in `target_closure`, `Q_y E` for a literal equation `E` means
   `∀y (E(y) → E(S y))`. Soundness of the seven uniform rules for that reading
   is proved (`RPrf.toNPrf`, `rprf_sound_pra`, `rprf_consistent`), and so is
   the recovery of equation induction inside the calculus (`RPrf.eqInd`). Settled:
   the kernel embeds faithfully (`rprf_emb_iff`), the reading is faithful
   (`rprf_iff_rd`), and both formula round trips are proved
   (`NEquiv.rd_emb`, `REquivIn.emb_rd`). The calculus of `target_closure` is
   proved equivalent to `RPrf` on the same formulas (`tqprf_iff_rprf`), so
   the same results hold for it.
6. **Other term syntaxes.** `canonical_recursors`, `clausal_canonical`,
   `counter_evaluation`, `uniform_binding`, `substitutive_discharge` in its
   own form, and `register_graph` are stated on recursors with a counter or
   with a successor seed. Each needs its own syntax and a bi-interpretation
   with the iterator terms. (`initializer_equality` was listed here by
   mistake: it is on zero-normal iterator terms, and its rule is proved,
   `niprf_iff_nprf`.) The rule of `counter_evaluation` puts the equation in
   the counter and needs a body that sees the counter, so it has no analogue
   on iterator terms.
7. **The clausal presentations.** Settled: on full normal forms the clausal
   forms of `witness_discharge` (`WDPrf`), of `inferred_witness` and
   `deterministic_opening` (`OCPrf`), of `first_instance` and
   `clause_discharge` (`XCPrf`), and of `variable_substitution` (`VCPrf`)
   are proved equivalent to the kernel.
8. **A shorter proof of the equivalence.** The main chain is 4,872 lines. A
   dependency-closure computation shows that it contains nothing that the end
   results do not use. Three designs fix most of its size, and no shorter
   replacement for any of them is known: the predecessor of `T_eq` from
   iteration alone (parity, a ramp with residues modulo three, a factor map, a
   comparator, a saturating counter); the conjunction of two formulas through
   a parity; and the selector between two formulas by a double recursion on
   their binders. On the iPRA side the extensionality of the simulated
   iterator (`ToPRA.iterSym_ext`) and the round trip of primitive recursion
   are both instances of the uniqueness of primitive recursion
   (`ToPRA.prec_uniq`), as their `T_eq` counterparts are instances of
   `Q.prc_itG`.
9. **Is the public language necessary?** Settled: yes. `PGPrf` is equivalent
   to the kernel on translated sequents (`pgprf_pub_iff`) and strictly weaker
   on arbitrary ones: `x = y, y = z ⊢ x = z` between variables is not
   derivable in it (`pgprf_not_trans`, `pgprf_strictly_weaker`). The
   invariant that covers `QE`, `DE` and the introduction is semantic. A value
   is a number with a colour; a variable may hold any value, every other term
   has an ordinary number as its value, bound variables range over ordinary
   numbers, and an equation holds by number or by adjacent colours. A matrix
   that holds by colours does not depend on its bound variables, so closures
   over it hold trivially (`Colour.T_Q_eq`) and compound formulas do not see
   colours (`Colour.T_recolor`). For the weaker source restriction of the
   packages (no literal `0`), and for no restriction of the sources at all,
   transitivity is derivable but the answer is the same for a different
   reason: the root-determined introduction does not give the introduction
   by cases of a raw equation (`rdprf_not_cases`, by the progressive reading
   over the natural numbers). In the other direction, restoring both
   introductions of the kernel does not restore transitivity
   (`tiprf_not_trans`, `NativeIteratorSource`).

Build with one module per invocation, for example

    $env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
    lake build +ConciseIPRA.NativeBiInterpretation
