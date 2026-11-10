# Concise presentations of intuitionistic primitive recursive arithmetic

This project collects the research packages that look for a very small
complete presentation of a theory bi-interpretable with full first-order
intuitionistic primitive recursive arithmetic (iPRA), and the Lean
formalization of the most concise of them.

- [`Research/`](Research/) holds sixteen delivered packages, one directory
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

### Other arithmetic bases

| Package | Arithmetic basis |
| --- | --- |
| [`scalar_successor`](Research/scalar_successor/), [`transient_seed`](Research/transient_seed/), [`successor_seed_completion`](Research/successor_seed_completion/) | A successor-seeded recursor `R(0,a;u.h) = S(a)`, `R(S n,a;u.h) = h[R(n,a;u.h)/u]`, with `S(a) := R(0,a;u.0)`; three independent predecessor constructions |
| [`bounded_initializer`](Research/bounded_initializer/) | A tied-seed recursor `B` with a Boolean equality test `ε` |
| [`monus_and_neutral_major`](Research/monus_and_neutral_major/) | A tied-seed recursor with two truncated-subtraction equations, from which reflection of equality is derived; also a neutral-major certificate protocol for the native core |
| [`selfseed_scalar`](Research/selfseed_scalar/) | A self-seeded recursor `F(0;v.h) = S(h(0))`, `F(S n;v.h) = h(F(n;v.h))` over ordinary logic with successor injectivity, `0 ≠ S 0`, a Boolean equality test and literal-equation induction; also checkers of 554 bytes and of 291 AST nodes for the native core |

## Intake record

Twenty archives `ipra_<name>_2026-11-10.zip` were delivered to `docs/drafts/`
on 2026-11-10 and filed here on the same day.

- **Filed (16):** the packages listed above, each under its `<name>`.
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

## Lean formalization

In progress. The target is the native scalar core above as a deeply embedded
calculus, the ordinary theory `T_eq`, and their bi-interpretation with iPRA.
