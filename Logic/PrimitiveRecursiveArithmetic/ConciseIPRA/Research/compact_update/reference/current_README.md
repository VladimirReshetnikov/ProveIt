# Concise presentations of intuitionistic primitive recursive arithmetic

This project collects the research packages that look for a very small
complete presentation of a theory bi-interpretable with full first-order
intuitionistic primitive recursive arithmetic (iPRA), and the Lean
formalization of the most concise of them.

- [`Research/`](Research/) holds twenty-eight delivered packages, one directory
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
| Tr, equational | `Γ ⊢ s = t`, `Γ ⊢ a(s) = b(s)` | `Γ ⊢ a(t) = b(t)` |
| QI, progress | `Γ, E(z) ⊢ E(S z)` with `z` fresh, `E` a literal equation | `Γ ⊢ Q_y E(y)` |

- *Equational transport.* Transport never has to look inside a `Q` or a `D`:
  for a compound template it follows by induction on the template from QE,
  DE, DI by cases and symmetry. Equality reasoning in the kernel is purely
  equational.
- *Direct closure.* Progress introduces the closure `Q_y E(y)` itself, with
  no existential witness and one bound variable fewer; the witnessed rule
  follows by QE and DI by cases. This is the proposal of
  [`direct_closure`](Research/direct_closure/) and
  [`direct_closure_qprogress`](Research/direct_closure_qprogress/).

- *No literal-zero source.* Transport may further be restricted to equations
  `s = t` whose source `s` is not the literal term `0`; the omitted instances
  are derivable (`zprf_iff_nprf`). This is the theorem of
  [`source_dispatch`](Research/source_dispatch/), which lets the source of an
  elimination select its major premise.

- *One introduction rule.* The two introductions can be replaced by one,

      DI:  Γ, B(t, η) ⊢ B(t, S z)  with z fresh   ⟹   Γ ⊢ D_{x,y} B

  where `η` is `z` if `B` is a literal equation and `t` is the literal `0`,
  and `0` otherwise. That calculus has seven rules and derives the same
  sequents (`wprf_iff_nprf`). This is the idea of
  [`witness_rule`](Research/witness_rule/); the case it removes, an equation
  by cases at the witness `0`, is recovered at the witness `I(0, 0; u. 0)`.

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

### Other arithmetic bases

| Package | Arithmetic basis |
| --- | --- |
| [`scalar_successor`](Research/scalar_successor/), [`transient_seed`](Research/transient_seed/), [`successor_seed_completion`](Research/successor_seed_completion/) | A successor-seeded recursor `R(0,a;u.h) = S(a)`, `R(S n,a;u.h) = h[R(n,a;u.h)/u]`, with `S(a) := R(0,a;u.0)`; three independent predecessor constructions |
| [`bounded_initializer`](Research/bounded_initializer/) | A tied-seed recursor `B` with a Boolean equality test `ε` |
| [`monus_and_neutral_major`](Research/monus_and_neutral_major/) | A tied-seed recursor with two truncated-subtraction equations, from which reflection of equality is derived; also a neutral-major certificate protocol for the native core |
| [`selfseed_scalar`](Research/selfseed_scalar/) | A self-seeded recursor `F(0;v.h) = S(h(0))`, `F(S n;v.h) = h(F(n;v.h))` over ordinary logic with successor injectivity, `0 ≠ S 0`, a Boolean equality test and literal-equation induction; also checkers of 554 bytes and of 291 AST nodes for the native core |
| [`register_graph`](Research/register_graph/) | Terms `x`, `0` and a counter-aware register iterator `J(n; i, r. body)` only, over ordinary logic: successor `S(a) = J(a; i, r. 0)` and the initializer are derived, and primitive recursion compiles without pairing; also a 288-node AST checker for the native core |

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

## Lean formalization

The Lake library `ConciseIPRA` (root workspace; sources under
[`Lean/ConciseIPRA/`](Lean/ConciseIPRA/), namespace `LeanProofs.ConciseIPRA`)
formalizes three systems and proves them mutually bi-interpretable:

1. **The native scalar core** (`Native`): the calculus of
   [The native scalar core](#the-native-scalar-core), deeply embedded.
   Formulas are `s = t`, `Q_y B` and `D_{x,y} B` only. Derivability
   `NPrf Γ A` has eight rules: Hyp, the two computation equations,
   equational Tr, QE, DE, DI by cases and QI by progress. There are no
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
| kernel = reports' calculus | `iprf_iff_nprf : IPrf Γ A ↔ NPrf Γ A` | equational Tr and QI by progress derive the same sequents as Tr in arbitrary templates and witnessed DI by progress |
| | `NPrf.tr`, `NPrf.dIProg` | the two inherited rules as derived rules of the kernel |
| no literal-zero source | `zprf_iff_nprf : ZPrf Γ A ↔ NPrf Γ A` | transport restricted to sources other than the literal `0` derives the same sequents |
| one introduction rule | `wprf_iff_nprf : WPrf Γ A ↔ NPrf Γ A` | the seven-rule calculus with the single, syntax-directed introduction derives the same sequents |
| native → `T_eq` | `NPrf.sound` | `NPrf Γ A → Γ.map toFm ⊢[TeqAx] A.toFm` for the ordinary readings of `Q` and `D` |
| `T_eq` → native | `NPrf.ofPrf` | `Γ ⊢[TeqAx] φ → NPrf (Γ.map ofFm) (ofFm φ)`, where `ofFm` replaces each connective by its native macro |
| native = `T_eq` | `NPrf.iff_teq`, `Teq.iff_native` | faithfulness of both readings |
| | `NEquiv.ofFm_toFm`, `Teq.iff_toFm_ofFm` | both round trips are the identity up to interderivability / provable equivalence |
| native ≡ iPRA | `native_iff_pra`, `pra_iff_native` | the native calculus proves a sequent iff iPRA proves its reading, and conversely |
| | `native_roundTrip`, `pra_native_roundTrip` | both composites through iPRA are the identity up to equivalence |
| | `native_inconsistent_iff` | `NPrf [] (0 = 1)` iff iPRA proves `⊥` |

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
| native admissible rules | `NativeStruct`, `NativeEq`, `NativeGate` | weakening, substitution, cut, `Q`-introduction, numerical cases; equality, interderivability over a context, Leibniz and transport in every template, equation induction; selector and gate formulas |
| kernel comparison | `NativeInherited`, `NativeZeroSource`, `NativeOneIntro` | the calculus of the reports, `IPrf`, and `iprf_iff_nprf`; the calculus without literal-zero transport sources, `ZPrf`, and `zprf_iff_nprf`; the calculus with one introduction rule, `WPrf`, and `wprf_iff_nprf` |
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
| `witness_rule` (first delivery) | Proved: `wprf_iff_nprf`, for the kernel with equational transport. The kernel keeps two introductions, because the single rule is not stable under substitution by a direct induction (a substitution can turn a witness into the literal `0`). |
| `direct_closure`, `direct_closure_qprogress` | Adopted: `qIInd` is the kernel's progress rule. The delivered migration patch compiled as written. |
| `source_dispatch` | Proved: `zprf_iff_nprf`. The kernel keeps unrestricted sources, because substitution into derivations (`NPrf.subst`) is not admissible in the restricted calculus. |
| `guarded_core` | Its aim, one root-determined introduction, is reached without changing the formula language by `wprf_iff_nprf`. Its own route (guarded atomic matrices, clause contexts in place of `Q`) is not formalized: it needs a second embedding and both translations. |
| `scope_and_closure` | Its checker results concern Python programs. Its mixed closure also aims at a deterministic introduction, by giving `Q` a progressive reading at literal equations and adding arithmetic to QE; not formalized, for the same reason. |
| `register_graph` | Not formalized. It is a different term language (`J` with two bound variables) over ordinary logic, so it would need a second bi-interpretation with iPRA from scratch. |

Build with one module per invocation, for example

    $env:LAKE_JOBS = '1'; $env:LEAN_NUM_THREADS = '0'
    lake build +ConciseIPRA.NativeBiInterpretation

