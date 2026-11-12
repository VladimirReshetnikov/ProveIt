# Concise presentations of intuitionistic primitive recursive arithmetic

This project collects the research packages that look for a very small
complete presentation of a theory bi-interpretable with full first-order
intuitionistic primitive recursive arithmetic (iPRA), and the Lean
formalization of the most concise of them.

- [`Research/`](Research/) holds fifty-six delivered packages, one directory
  each. They are written mathematics with executable Python proof checkers;
  none of them claims a proof-assistant verification.
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
  [`one_context`](Research/one_context/).
- *Direct closure.* Progress introduces the closure `Q_y E(y)` itself, with
  no existential witness and one bound variable fewer; the witnessed rule
  follows by QE and DI by cases. This is the proposal of
  [`direct_closure`](Research/direct_closure/) and
  [`direct_closure_qprogress`](Research/direct_closure_qprogress/).

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
  [`one_sided_transport`](Research/one_sided_transport/), and it lets the
  source of an elimination select its major premise
  ([`source_dispatch`](Research/source_dispatch/)).

- *One introduction rule.* The two introductions can be replaced by one,

      DI:  Γ, B(t, η) ⊢ B(t, S z)  with z fresh   ⟹   Γ ⊢ D_{x,y} B

  where `η` is `z` if `B` is a literal equation and `t` is the literal `0`,
  and `0` otherwise. That calculus has seven rules and derives the same
  sequents (`wprf_iff_nprf`). This is the idea of
  [`witness_rule`](Research/witness_rule/); the case it removes, an equation
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
  [`zero_normal`](Research/zero_normal/); the normalization is part of the
  specification of the calculus.
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
  calculus of [`diagonal_guard`](Research/diagonal_guard/).
- *Six rules.* Reflexivity and one rule Eval can replace both computation
  equations and transport. Eval infers `r = Φ(s, t, b)` from `s = t` and
  `b = r`, where `Φ` is `t` if `b` is `I(0, s; u.h)`, and `h[t/u]` if `b` is
  `I(S c, a; u.h)` and `s` is `I(c, a; u.h)`. A third case, `Φ = t` if `b` is
  `s`, is derivable from the first through the frame `I(0, s; u.u)`
  ([`equality_from_iteration`](Research/equality_from_iteration/)). With QE, DE
  and the single introduction this is a calculus of six rules, `EPrf`, on the
  unchanged terms and formulas with ordinary substitution, and it derives the
  same sequents (`eprf_iff_nprf`). The computation equations are Eval on two
  reflexivities; transport in a template `h` is one iteration of `h`. This is
  the calculus of
  [`computational_equality`](Research/computational_equality/).
- *Other forms of the source restriction.* For transport in an equation
  template with an uncrossed conclusion, the same restriction needs an
  equation induction and a singleton test, though no logical rule
  (`zprf_iff_nprf`; [`guarded_source`](Research/guarded_source/); class
  `ZKernel`). If transport in arbitrary templates and QE both reverse the
  root equation of their conclusion, it again needs no induction
  (`rprf_iff_nprf`, the module proposed by
  [`reversal_core`](Research/reversal_core/)).

**Ordinary realization.** `T_eq` is intuitionistic first-order logic with
equality over the same terms, with the two computation equations, coverage
`∀x (x = 0 ∨ ∃y x = S y)`, separation `0 = S 0 → ⊥`, and induction for literal
equations with side assumptions. The reports derive a predecessor, reflection
of equality into a term, quantifier-free induction, pairing and a compiler for
all primitive recursive definitions, in that order, which gives the
bi-interpretation with iPRA.

The complete statement and the written proofs are in
[`Research/certified_zero/reference/`](Research/certified_zero/reference/)
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
| [`constructed_computation`](Research/constructed_computation/) | Successor sources constructed from predecessors; a finite-range obstruction to restricting DI witnesses and QE targets at once | 279 / 314 / 682 |
| [`counter_congruence`](Research/counter_congruence/) | A counter-congruence form of the calculus | 280 / 314 / 672 |
| [`uniform_predecessor`](Research/uniform_predecessor/) | Uniform predecessor packets; single-body initializer fusion cannot define addition, selection or pairing | 269 / 307 / 629 |
| [`adaptive_seed`](Research/adaptive_seed/) | An obstruction result only; no smaller checker | — |
| [`research`](Research/research/) | A progressive binder `H_{x,y} B := ∃x ∀y (B(x,y) → B(x,S y))`; an eventually-constant obstruction | 276 / 305 / 749, and 652 bytes |
| [`local_scopes`](Research/local_scopes/) | No finite-dimensional bi-interpretation of iPRA with the tied-seed `B` theory | 668 bytes |
| [`checker_and_barriers`](Research/checker_and_barriers/) | Two further obstructions | 593 bytes |
| [`compact_kernel`](Research/compact_kernel/) | Truth transfer in eventually constant powers for all `∧, ∃, ∀` formulas, hence a symmetry obstruction | 266 / 310 / 612 |
| [`certified_zero`](Research/certified_zero/) | Certified zero sources; the reference statement of the inherited basis and bridge | 264 / 308 / 566; 558 bytes; joint 262 / 296 / 598 |
| [`uniform_zero`](Research/uniform_zero/) | Uniform zero and constructed elimination majors; shorter certificates | 545 to 564 bytes over six profiles |
| [`uniform_premise`](Research/uniform_premise/) | Every non-hypothesis instruction verifies a major premise against a retained neutral truth; a successful-trace invariant replaces the type guard | 262 / 303 / 548, and 537 bytes |
| [`witness_rule`](Research/witness_rule/) | One introduction rule in place of the case/progress choice: progress exactly when the matrix is a literal equation and the witness is literally `0`, cases otherwise; the same sequents are derivable | 266 / 312 / 555 |
| [`neutral_scope`](Research/neutral_scope/) | Composition of neutral premises with local scopes; no new mathematics | 266 / 310 / 529, and 290 AST nodes |
| [`prevalidated_elimination`](Research/prevalidated_elimination/) | The elimination template and both instances are fixed before the major premise is proved; no new mathematics | 263 / 307 / 547; 539 bytes; 261 tokens |
| [`scope_and_coverage`](Research/scope_and_coverage/) | Byte-profile checkers; for the self-seeded recursor without successor injectivity, `S^k(a) ≠ a` for each fixed `k ≥ 1` and a right predecessor with `n = 0 ∨ n = S(P n)` | 266 / 310 / 529, and 537 bytes |
| [`coverage_and_kernel`](Research/coverage_and_kernel/) | For the self-seeded recursor without successor injectivity, whole-domain coverage from a protected orbit; one `D` over a literal equation represents exactly the prenex `∃∀` quantifier-free class | 531 and 539 bytes; 289 AST nodes |
| [`direct_closure`](Research/direct_closure/), [`direct_closure_qprogress`](Research/direct_closure_qprogress/) | Two independent write-ups of one change of primitive: equation induction introduces `Q_y E(y)` directly, from `E(z) ⊢ E(S z)`, and the witnessed `D` progress rule becomes derived; the first also carries a Lean migration sketch and a counter-vector experiment | no new minimum (552 and 568 bytes; 533 for the experiment) |
| [`source_dispatch`](Research/source_dispatch/) | Transport may be restricted to sources that are not literally `0`, every omitted instance being derivable; the source then selects the elimination major (`Q_v F(v)` at `0`, `s = t` otherwise) | 259 tokens; 283 AST nodes; 526 bytes (three programs) |
| [`guarded_core`](Research/guarded_core/) | Atomic matrices under `D` restricted to the guarded shape `I(y,0;u.h) = I(y,0;u.k)`, so one root-determined introduction rule suffices: progress at equations, cases at compound matrices | 260 tokens; 286 AST nodes; 527 bytes (three programs) |
| [`scope_and_closure`](Research/scope_and_closure/) | Checker composition only for the core; a "mixed closure" variant with progressive `Q` at literal equations and a deterministic introduction; an obstruction to zero-start iterators | 264 / 288 / 608, and 528 bytes |
| [`reversal_core`](Research/reversal_core/) | Transport and QE reverse the root equation of their conclusion, with transport sources other than the literal `0`; a constant template then gives unrestricted symmetry in one step, and the source restriction is removed with no induction, cases or successor computation. Ships a proposed Lean module | 525 bytes; 282 AST nodes (two programs); typed checker 1055 bytes against a 1365-byte control |
| [`guarded_source`](Research/guarded_source/) | Source dispatch and the guarded core coexist: the recovery of zero-source transport needs equation induction only, its case splits being inductions that ignore the hypothesis | 258 tokens; 281 AST nodes; 525 bytes (as stated, different programs) |
| [`guarded_orbit`](Research/guarded_orbit/) | In a strictly guarded proof language the two do not compose (`0 = t` does not yield `t = 0`); the administrative orbit `D_{r,y}(y = I(y,t;u.Su))` repairs it | 258 tokens; 281 AST nodes; 525 bytes (three programs) |
| [`deterministic_auxiliary`](Research/deterministic_auxiliary/) | Source-selected elimination with root-determined introduction, keeping unrestricted atomic progress formulas as auxiliary intermediates; the guarded public consequences are unchanged | 525 and 522 bytes |
| [`mirror_guard`](Research/mirror_guard/) | A one-sided guard: canonical atomic matrices `a(x,y) = I(y, a(x,y); u.h)`, with one root-determined introduction and no literal-zero transport source | modest, as stated |
| [`protected_core`](Research/protected_core/) | Public equality `s = t` represented as `W(s) = W(t)`, `W(r) = I(0,r;u.0)`, so that every transport source is iterator-headed | modest, as stated |
| [`one_context`](Research/one_context/) | Transport with one term template instead of two, crossed: from `s = t` and `h(s) = u` infer `u = h(t)`. Two steps recover the two-template rule; sources are unrestricted and the rule is stable under substitution. Ships proposed Lean modules. Independently, strict goal validation reuses the kernel's scope check | matched tagged checker 3382 to 3358 bytes, 1101 to 1089 tokens; strict Eq/D validator 824 to 803 bytes |
| [`kernel_refinement`](Research/kernel_refinement/) | The guarded-source checkers with a loop over immutable tuple contexts and the scalar neutral premise. An auxiliary note replaces equational transport by replacement of one occurrence in the left side of an equation, `C[s] = r` to `C[t] = r` for a linear term context `C` | 256 tokens; 278 AST nodes; 521 bytes (three programs) |
| [`compact_update`](Research/compact_update/) | The scalar neutral-resource encoding of `reversal_core` applied to the `guarded_source` checkers; stated to be an implementation-level composition. Also an exact criterion for when the conditional closure `E(0) → ∀y E(y)` and the progressive closure `∀y (E(y) → E(S y))` of an equation agree: exactly when `¬E(0)` implies progress | 257 tokens; 278 AST nodes; 521 bytes (different programs) |
| [`uniform_progress`](Research/uniform_progress/) | A seven-rule calculus `R` on the unrestricted formula grammar with a changed reading: `Q_y E` of a literal equation means progress, `∀y (E(y) → E(S y))`, and of a compound matrix the conditional closure. One introduction rule chooses its mode from the root of the matrix alone, so it commutes with substitution; one elimination `Q_y B, B(η) ⊢ B(I(η, n; u. S u))` serves both readings. Translations to and from the native calculus with both round trips, as written proofs | matched typed checker 4553 bytes against 4692 for the eight-rule kernel and 4456 for the seven-rule witness kernel |
| [`one_sided_transport`](Research/one_sided_transport/) | The seven-rule calculus with its transport replaced by the one-template crossed rule at sources other than the literal `0`: from `s = t` and `f(s) = r` infer `r = f(t)`. The zero computation and this rule alone recover all equality reasoning, with no induction and no logical rule. Ships a proposed Lean module | matched strict checker 3246 bytes against 3302, 1171 tokens against 1196 |
| [`validated_core`](Research/validated_core/) | One recursive validator shared between raw-tree typing and the public grammar, for the unchanged rule basis | fully validated Eq/Q/D checker 897 bytes against a matched 1049; compact envelope 256 tokens, 278 AST nodes, 521 bytes (different programs) |
| [`validated_presentation`](Research/validated_presentation/) | The whole certificate is typed by one test on its printed form, so the public syntax validator loses its separate raw-type pass; the proof kernel is unchanged | fully validated Eq/Q/D checker 870 bytes against 897, 383 tokens against 401 |
| [`checked_refinement`](Research/checked_refinement/) | Three smaller implementations of the existing presentations; stated to contain no new axiom deletion | guarded public-goal checker 921 bytes against 1201; native Eq/D public checker 788 against 803; compact guarded 520 against 521 |
| [`equality_from_iteration`](Research/equality_from_iteration/) | The rule Eval of `computational_equality` without its first case: equality composition `s = t, s = r ⊢ r = t` follows from the zero-iteration case through the frame `I(0, s; u.u)`. A companion calculus on zero-normal terms has reflexivity and one successor-evaluation schema | as stated |
| [`full_normalization`](Research/full_normalization/) | Both iterator computations moved into the syntax: terms are in full normal form for `I(0, a; u.h) → a` and `I(S n, a; u.h) → h[I(n, a; u.h)/u]`, and there is no computation rule at all. Six patterns: Hyp, Refl, Tr, QE, DE and one witness-selected introduction, with a lemma that repairs case introduction when normalization turns a witness into the literal `0`. Written proofs of strong normalization, confluence and substitution coherence | selected checker 2529 bytes against 2532 for the zero-only control, with more tokens and AST nodes |
| [`reflexive_base`](Research/reflexive_base/) | On zero-normal terms, the single introduction is progressive exactly when the normalized zero instance of the matrix is literally `r = r`. Six rules; a raw seven-rule variant with an asymmetric selector gate | matched strict checker 3084 bytes against 3095 |
| [`raw_clausal`](Research/raw_clausal/) | Five rule patterns with ordinary substitution: reflexivity, Eval, use of a retained clause, paired elimination, witness-directed paired introduction; formulas `s = t` and `D` only, with clause contexts in place of `Q` | as stated |
| [`scalar_uniqueness`](Research/scalar_uniqueness/) | Induction for literal equations replaced by uniqueness of iteration: from `f(S z) = h(f(z))` infer `f(t) = I(t, f(0); u.h(u))`, with no induction hypothesis in the premise. The report recovers predecessor, reflection of equality and equation induction from it, closing the gap left open in `scope_kernel` | matched raw checker grows from 3322 to 3393 bytes; validated checker of the existing calculus 866 against 870 |
| [`computational_equality`](Research/computational_equality/) | Six rules on the unchanged language, with no normalization: Hyp, Refl, Eval, QE, DE, DI. Eval merges equality with one computation: from `s = t` and `b = r` infer `r = Φ(s, t, b)`, where `Φ` is `t` if `b` is `s` or `b` is `I(0, s; u.h)`, and `h[t/u]` if `b` is `I(S c, a; u.h)` and `s` is `I(c, a; u.h)`. Both computation equations and all congruence are derived | matched checker 3039 bytes against 3121, 959 tokens against 1008 |
| [`zero_normal`](Research/zero_normal/) | Terms with no iterator whose counter is the literal `0`; substitution rebuilds terms with `I(0, a; u.h)` replaced by `a`, so the zero computation rule is deleted. With the single introduction and one-term transport: six rules. Ships a compiled Lean module for the normalization layer | matched strict tagged checkers, 8 and 7 rules: 3322 and 3272 bytes |
| [`diagonal_guard`](Research/diagonal_guard/) | One introduction whose mode is chosen by a guard that substitution preserves and reflects: progress exactly when the matrix is literally `I(y, y; u.h) = I(y, y; v.k)`, cases otherwise. Seven rules on the full formula language with the original readings | matched typed checker 3244 bytes against 3382 for eight rules and 3205 for the witness rule |
| [`template_free`](Research/template_free/) | Equality with no supplied template: from `s = t` and `u = v` infer `v = R(u)`, where `R` replaces every free occurrence of `s` in `u` by `t` in one pass. Seven rules; congruence in a chosen context is recovered through an oversized computation marker | strict tagged checker, as stated |
| [`target_closure`](Research/target_closure/) | A seven-rule progressive calculus `T` whose closure elimination supplies one numerical target, equivalent to the calculus of `uniform_progress`; separately, exact certificate typing by a lexical gate for the existing calculus | `T` checker 4532 bytes against 4553; typed checker of the existing calculus 895 bytes against 1039 |
| [`scope_kernel`](Research/scope_kernel/) | Reuse of the kernel's first scope traversal in the validated checker. Two research notes: a coordinatewise model on `N × N` that validates equation induction and refutes coverage, and an unfinished attempt to replace equation induction by uniqueness of iteration | fully validated Eq/Q/D checker 881 bytes against 897 |

### Other arithmetic bases

| Package | Arithmetic basis |
| --- | --- |
| [`scalar_successor`](Research/scalar_successor/), [`transient_seed`](Research/transient_seed/), [`successor_seed_completion`](Research/successor_seed_completion/) | A successor-seeded recursor `R(0,a;u.h) = S(a)`, `R(S n,a;u.h) = h[R(n,a;u.h)/u]`, with `S(a) := R(0,a;u.0)`; three independent predecessor constructions |
| [`bounded_initializer`](Research/bounded_initializer/) | A tied-seed recursor `B` with a Boolean equality test `ε` |
| [`monus_and_neutral_major`](Research/monus_and_neutral_major/) | A tied-seed recursor with two truncated-subtraction equations, from which reflection of equality is derived; also a neutral-major certificate protocol for the native core |
| [`selfseed_scalar`](Research/selfseed_scalar/) | A self-seeded recursor `F(0;v.h) = S(h(0))`, `F(S n;v.h) = h(F(n;v.h))` over ordinary logic with successor injectivity, `0 ≠ S 0`, a Boolean equality test and literal-equation induction; also checkers of 554 bytes and of 291 AST nodes for the native core |
| [`register_graph`](Research/register_graph/) | Terms `x`, `0` and a counter-aware register iterator `J(n; i, r. body)` only, over ordinary logic: successor `S(a) = J(a; i, r. 0)` and the initializer are derived, and primitive recursion compiles without pairing; also a 288-node AST checker for the native core |
| [`canonical_recursors`](Research/canonical_recursors/) | A successor-seeded recursor `R(n, a; u.h)` with successor defined as `R(0, a; u.0)`; the zero computation is built into a canonical term grammar with normalizing substitution, so successor computation is the only explicit computation rule. Six rules; written proofs of the equivalence with the raw calculus and of the bi-interpretation with iPRA. Normalization is part of the trusted specification. Matched strict checker 4611 bytes against 4923 for the scalar iterator with independent `S`; separately, the compact guarded codec at 516 bytes against 522 |
| [`initializer_equality`](Research/initializer_equality/) | On the canonical recursor syntax, equality transport is replacement of an iterator's initializer; zero iteration is definitional, so this includes replacement at the root, and one iteration applies any term template. Six rules; the equality step takes two proofs and no template |
| [`clausal_canonical`](Research/clausal_canonical/) | Five rules on the canonical recursor syntax, with an Eq/D public language and contexts of reusable clauses in place of `Q`. Matched checker 3305 bytes against 3820 for the six-rule control |

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
`Research/reversal_core/formalization/Reversal.lean` is kept as delivered; its
compiled form is `Lean/ConciseIPRA/NativeReversal.lean`.

A fourth delivery of four archives arrived on 2026-11-11 (commits
`ed0d9a32d7`, `b1f7e85b3f` and `7669726207`) and was filed the same day:
`compact_update`, `one_context`, `kernel_refinement` and `uniform_progress`.
They respond to the third delivery and to `NativeReversal`. Not filed:
sixteen frozen copies of this repository's Lean sources and two checksum
ledgers. The proposed modules
`Research/one_context/lean/*.lean` are kept as delivered.

A fifth delivery of two archives arrived on 2026-11-11 (commit `42a48d2f04`)
and was filed the same day: `one_sided_transport` and `validated_core`. Not
filed: thirty-nine frozen copies of this repository's Lean sources and one
checksum ledger. The proposed module
`Research/one_sided_transport/formalization/NativeOneSided.lean` is kept as
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
`Research/zero_normal/formal/ZeroNormalization.lean` compiled unchanged and
is `Lean/ConciseIPRA/ZeroNormalization.lean`.

`full_normalization` arrived after all of these and was filed on arrival.
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
| kernel = reports' calculus | `iprf_iff_nprf : IPrf Γ A ↔ NPrf Γ A` | Tr in one term and QI by progress derive the same sequents as Tr in arbitrary templates and witnessed DI by progress |
| | `NPrf.trEq`, `NPrf.tr`, `NPrf.dIProg` | transport in an equation template (two steps) and the two inherited rules, as derived rules of the kernel |
| no literal-zero source | `oprf_iff_nprf : OPrf Γ A ↔ NPrf Γ A` | the kernel's transport restricted to sources other than the literal `0` derives the same sequents, with no induction |
| | `zprf_iff_nprf : ZPrf Γ A ↔ NPrf Γ A` | the same for uncrossed transport in an equation template, by an equation induction and a singleton test |
| uncrossed one-term transport | `uprf_iff_nprf : UPrf Γ A ↔ NPrf Γ A` | from `s = t` and `h(s) = r` infer `h(t) = r`: the crossing is not essential when sources are unrestricted |
| one introduction rule | `wprf_iff_nprf : WPrf Γ A ↔ NPrf Γ A` | the seven-rule calculus with the single, syntax-directed introduction derives the same sequents |
| seven rules | `mprf_iff_nprf`, `mprf_iff_iprf : MPrf Γ A ↔ IPrf Γ A` | one-term transport at sources other than the literal `0` and the single introduction together derive the sequents of the reports' calculus |
| substitution-stable introduction | `gprf_iff_nprf : GPrf Γ A ↔ NPrf Γ A`, `GPrf.subst` | one introduction whose mode is read off the diagonal shape of the matrix; closed under substitution by direct induction |
| six rules, substitution-stable | `sprf_iff_nprf : SPrf Γ A ↔ NPrf Γ A`, `SPrf.subst` | Hyp, Refl, Eval, QE, DE and the diagonal DI: closed under substitution by direct induction; the equivalence uses `propext` and `Quot.sound` only |
| six rules | `eprf_iff_nprf : EPrf Γ A ↔ NPrf Γ A`, `eprf_iff_iprf` | Hyp, Refl, Eval, QE, DE and the single DI: one rule for equality and computation, no computation axiom and no template |
| one computation rule | `nzprf_iff_nprf : NZPrf (Γ.map fnf) (fnf A) ↔ NPrf Γ A`, `nzprf_iff_pra` | the kernel without the zero computation rule, on zero-normal terms with normalizing substitution, derives the normal form of every kernel sequent and nothing else |
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

The main chain (every module except the nine kernel comparisons,
`ZeroNormalization`, `NativeZeroNormal`, `NativeUniqueness` and `TeqClosure`) is 5,630
lines; it was 5,984 before the shortening passes. The larger cuts: cut for
natural deduction is a six-line induction on the context, by implication
introduction and elimination, instead of an induction over the seventeen
rules; weakening and substitution share one induction; simultaneous
congruence uses one extra variable; the equality bootstrap of the native
calculus is four single rule applications; reflection of quantifier-free
formulas is proved as an equivalence of Lean propositions,
`mk Γ (chi φ) = 0 ↔ Γ ⊢ φ`, from which the formula of `T_eq` follows. A dependency-closure scan of the
end results, computed inside Lean from the proof terms, finds no further
unused theorem apart from `rfl` lemmas that `simp` uses silently.

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
| zero-normal syntax | `ZeroNormalization`, `NativeZeroNormal` | contraction of iterators with a literal-zero counter, hereditary substitution, and the equivalence of a formula with its normal form (delivered); the kernel without the zero computation rule, `NZPrf` |
| closures in `T_eq` | `TeqClosure` | decidability of quantifier-free formulas; the criterion for agreement of the conditional and the progressive closure |
| derived rule | `NativeUniqueness` | uniqueness of iteration |
| native admissible rules | `NativeStruct`, `NativeEq`, `NativeGate` | weakening, substitution, cut, `Q`-introduction, numerical cases; equality, interderivability over a context, Leibniz and transport in every template, equation induction; selector and gate formulas |
| kernel comparison | `NativeInherited`, `NativeOneContext`, `NativeOneIntro`, `NativeDiagonal`, `NativeSix`, `NativeMinimal`, `NativeEval`, `NativeZeroSource`, `NativeReversal` | the calculus of the reports, `IPrf`, and `iprf_iff_nprf`; no literal-zero transport sources, `OPrf`, generic over the class `OKernel`, and the uncrossed rule, `UPrf`; six rules with Eval, `EPrf`; the diagonal introduction, `GPrf`, with its own structural rules; Eval with the diagonal introduction, `SPrf`; one introduction rule, `WPrf`, generic over the class `WKernel`; both together, `MPrf`; the source restriction for uncrossed transport in an equation template, `ZPrf`, generic over the class `ZKernel`; root-reversing transport and QE, `RPrf` |
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
| `kernel_refinement` | Its checker results concern Python programs. Its note on replacement in the left side of an equation is proved with a term template in place of a context with exactly one hole: `uprf_iff_nprf`. The reduction of a template to successive single occurrences is not formalized. |
| `compact_update` | Its checker results concern Python programs. Its closure criterion is proved in `T_eq` for every quantifier-free formula: `Teq.closure_iff_progress`, with `Teq.closure_of_progress` and the decidability lemma `Teq.qfDec` (`TeqClosure`). The variant after existential binding is `Teq.ex_closure_iff_progress`. |
| `uniform_progress` | Not formalized. Its calculus changes the reading of `Q` at literal equations, so it needs its own soundness proof, its own structural rules and both formula translations with their round trips. |
| `validated_core`, `validated_presentation`, `checked_refinement` | Their results concern Python programs; the rule basis is unchanged. |
| `scalar_uniqueness` | Half proved: the uniqueness rule is a derived rule of the kernel (`NPrf.uniq`). The converse, that it recovers equation induction when induction is not a rule, needs the report's own predecessor and reflection of equality and is not formalized. |
| `clausal_canonical` | Not formalized: it is stated on the canonical recursor syntax with clause contexts. |
| `computational_equality`, `equality_from_iteration` | Proved: the six-rule calculus is `EPrf`, with `eprf_iff_nprf` and `eprf_iff_iprf` (`NativeEval`). Eval has the two cases of `equality_from_iteration` as constructors; the third case of `computational_equality` is the derived rule `EPrf.evalId`. The zero-normal companion of `equality_from_iteration` is not formalized. |
| `full_normalization` | Not formalized. It needs the normalization of both computations with its termination and confluence, where `ZeroNormalization` treats the zero computation only. |
| `reflexive_base`, `raw_clausal` | Not formalized: a further mode test for the single introduction on zero-normal terms; a clause calculus without `Q`. |
| `zero_normal` | Its normalization layer is adopted as `ZeroNormalization`: the delivered module compiled unchanged. On top of it `NativeZeroNormal` proves the deletion of the zero computation rule for the kernel (`nzprf_iff_nprf`, `NZPrf.normal`, `nzprf_iff_pra`), with the kernel's two introductions and unrestricted sources. The six-rule form with the single introduction is not formalized. |
| `diagonal_guard` | Proved: its calculus is `GPrf`, with `gprf_iff_nprf`, `gprf_iff_iprf` and substitution by direct induction (`NativeDiagonal`). Progress for an arbitrary equation is recovered by a shorter argument than the report's: no implication between equations and no substitution into the step premise. The equivalence uses neither `Classical.choice` nor the bi-interpretation. |
| `template_free`, `target_closure` | Not formalized. Each is a further calculus on the native formula language: replacement of all occurrences in place of a template; a progressive closure with a target. |
| `initializer_equality`, `scope_kernel` | Not formalized: the first is stated on the canonical recursor syntax; the second concerns Python programs, and its research notes are a model and an unfinished argument. |
| `canonical_recursors` | Not formalized. It is a different term language (a recursor whose seed is a successor, with a canonical grammar and normalizing substitution), so it would need its own syntax, its equivalence with the raw calculus and a bi-interpretation with iPRA. |
| `witness_rule` (first delivery) | Proved: `wprf_iff_nprf`. The kernel keeps two introductions, because the single rule is not stable under substitution by a direct induction (a substitution can turn a witness into the literal `0`). |
| `direct_closure`, `direct_closure_qprogress` | Adopted: `qIInd` is the kernel's progress rule. The delivered migration patch compiled as written. |
| `source_dispatch` | Proved twice: `zprf_iff_nprf` for its own uncrossed rule, and `oprf_iff_nprf` for the kernel's rule, where it needs no induction. The kernel keeps unrestricted sources, because substitution into derivations (`NPrf.subst`) is not admissible in the restricted calculus. |
| `reversal_core` | Adopted as `NativeReversal`: the delivered module compiled after four typed-target fixes (`rprf_iff_nprf`, `reversal_iff_pra`, `pra_iff_reversal`). |
| `guarded_source` | Its key lemma is proved: the class `ZKernel` has no logical rule, only equation induction, and `ZKernel.trF` recovers unrestricted transport from it. Its guarded public language is not formalized. |
| `deterministic_auxiliary`, `guarded_orbit` | Their aim, source selection together with a root-determined introduction, is proved on the full native language as `mprf_iff_nprf`. Their guarded public languages with auxiliary formulas are not formalized. |
| `mirror_guard`, `protected_core` | Not formalized: each is a further restriction of the public formula language (a one-sided guard; equations wrapped as `W(s) = W(t)`), which needs its own embedding and both translations. |
| `guarded_core` | Its aim, one root-determined introduction, is reached without changing the formula language by `wprf_iff_nprf`. Its own route (guarded atomic matrices, clause contexts in place of `Q`) is not formalized: it needs a second embedding and both translations. |
| `scope_and_closure` | Its checker results concern Python programs. Its mixed closure also aims at a deterministic introduction, by giving `Q` a progressive reading at literal equations and adding arithmetic to QE; not formalized, for the same reason. |
| `register_graph` | Not formalized. It is a different term language (`J` with two bound variables) over ordinary logic, so it would need a second bi-interpretation with iPRA from scratch. |

Build with one module per invocation, for example

    $env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
    lake build +ConciseIPRA.NativeBiInterpretation
