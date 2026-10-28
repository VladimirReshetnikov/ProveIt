# Actual C222 source-negation compatibility: read-only plan

This is the proposed second source-interpretation leaf. No new Lean source,
compiler invocation, dependency build, or theorem acceptance is represented
by this note. The intended new files are `ValidatorSourceNegation222.lean`
and `ValidatorSourceNegation222Checks.lean` under
`Logic/Interpretability/ZFCinPA/Lean/ZFCinPA`.

## Exact target and import boundary

Import only `ZFCinPA.ValidatorFormulaEncoder222`. Its transitive actual C222
propositional and relational core already supplies every logical resource
needed here. The pending `ValidatorProofContext222` leaf is not needed; its
private finite-proof helpers need not become public. Neither `R2Neg` nor
`R2Ctx`, nor either old CProv254 theory module, will be imported.

Use the following public predicate and endpoint, with unambiguous names for
the two distinct notions of negation:

```lean
-- Throughout: V is an ORingStructure and models IΣ1.
def CodeIff (a b : V) : Prop :=
  ValidatorProvability222.CProv (wim a b) ∧
  ValidatorProvability222.CProv (wim b a)

abbrev codeNeg (a : V) : V := wim a 1
def NegEq (F B s p : V) : Prop :=
  CodeIff
    (ValidatorFormulaEncoder222.encode F B s (Bootstrapping.neg ℒₛₑₜ p))
    (codeNeg (ValidatorFormulaEncoder222.encode F B s p))

theorem encode_neg [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
    {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    NegEq F B s p
```

Both directions are actual C222 provability statements. Small projection
theorems may expose each implication and an actual pair of history witnesses
by unfolding `CProv`. The only object-level side condition is typed source
syntax. In particular, `F`, `B`, and `s` are arbitrary internal values:
there is no `len B = n`, freshness, injectivity, distinct-label, StreamFree,
vacant-variable or standardness premise. Fallback term labels and coincident
labels are covered by the actual total encoder.

The IΣ1 assumption supports the accepted definitions. As in the accepted
current alpha/vacuity packets, the theorem explicitly adds IΣ2 for the
uniform Π₂ induction; this is not a claim that IΣ1 proves the full result.

## Finite actual-code proof helpers

At IΣ1, use only `ValidatorProvability222.cProv_classical` and the accepted
`ValidatorRelationalCore222` theorems `compose`, `contrapose_of`,
`double_neg_intro`, `double_neg_elim`, and `all_mono`. Small local fixed
`Kalmar.Der` certificates provide implication congruence. Proposed helpers:

```lean
codeIff_refl (a : V) : CodeIff a a
codeIff_trans (h₁ : CodeIff a b) (h₂ : CodeIff b c) : CodeIff a c
codeIff_imp (ha : CodeIff a a') (hb : CodeIff b b') :
  CodeIff (wim a b) (wim a' b')
codeIff_neg (h : CodeIff a b) : CodeIff (codeNeg a) (codeNeg b)
codeIff_all (i : V) (h : CodeIff a b) : CodeIff (wal i a) (wal i b)
codeIff_doubleNeg (a : V) : CodeIff a (codeNeg (codeNeg a))
codeIff_neg_swap (h : CodeIff a (codeNeg b)) : CodeIff (codeNeg a) b
```

`codeIff_imp` uses the reverse antecedent implication and forward consequent
implication in its first direction, and conversely in its second. The helper
proofs do not assume semantic truth or equivalence of arbitrary formulas.
They produce checker witnesses through the actual classical C222 rule
closures. A copied generic GG algorithm or a finite semantic oracle is not
needed.

The conjunction case can be shortened relative to the old guide: from
`a ↔ ¬p` and `b ↔ ¬q`, implication congruence gives
`(¬a → b) ↔ (p → ¬q)`, then double-negation equivalence supplies the required
`(¬a → b) ↔ ¬¬(p → ¬q)`. For source disjunction, congruence first gives
`(a → ¬b) ↔ (¬p → q)`, then contraposition gives their negations. This avoids
the old four-variable tautology expansions while preserving the exact target.

## Actual source induction and eight cases

The source is the represented internal set-language syntax, not Lean's
external inductive formulas. `Foundation...Formula.Basic` supplies the exact
eight-way `IsSemiformula.case_iff`; the two quantifier body types have bound
arity `n+1`. `Foundation...Formula.Functions` defines the represented NNF
negation with eight recursion clauses and proves `neg_rel`, `neg_nrel`,
`neg_verum`, `neg_falsum`, `neg_and`, `neg_or`, `neg_all`, and `neg_ex`.

The induction motive is exactly:

```lean
fun p => ∀ n F B s : V,
  IsSemiformula ℒₛₑₜ n p → NegEq F B s p
```

`CProv` is genuinely Σ₁ by its fixed history graph; the accepted hierarchy
`strict_mono` lemma embeds it in Π₂. The actual total encoder and source
negation have Δ₁ graphs, and `IsSemiformula` is Δ₁. Register these precise
level-two instances and prove the displayed motive Π₂ by four universal
closures and the typed antecedent. Then use
`InductionOnHierarchy.order_induction_sigma 𝚷 2`. The strict subcode bounds
are the existing constructor bounds. No ordinary Lean induction over a
standard-length syntax tree substitutes for this internal induction.

| Actual source constructor | Exact remaining code argument |
|---|---|
| relation | `encode_nrel` is literally the negation of the same `atom`; reflexivity works for membership and Eind equality alike |
| negated relation | the same atom compared with its double negation |
| truth | codes `1` and `wim 0 1`; ex falso forward, actual `cProv_truth` supplies the converse deduction |
| falsity | codes `0` and `wim 1 1`; both are actual theorems, then K gives the two implications |
| conjunction | the finite congruence/double-negation argument above |
| disjunction | implication congruence followed by negation congruence |
| universal | invoke IH at `(n+1,F,s∷B,s+2)`, negate/swap the body equivalence, lift through the same `wal s`, then negate |
| existential | invoke that same shifted-state IH, lift through `wal s`, then add double negation on the right |

The quantifier proof compares the same literal binder on both sides. It
therefore uses neither alpha-renaming nor a vacuity rule. The source equality
case is syntactic atom/negated-atom compatibility; it does not identify Eind
with primitive `weq` or interpret the source equality axioms.

## Focused checks and limits

Expected main size is approximately 220–280 lines and checks 55–75 lines.
Checks should cover both projected implications, actual history witnesses,
membership and equality atoms with colliding/fallback labels, source truth
and false, double source negation, and an alternating nested `∀/∃` example
with the literal `s∷B`, `s+2` updates. Retain a malformed-source control:
source code zero is not a typed formula, even though its total encoder returns
zero. Do not extend the theorem to malformed inputs by erasing `hp`.

This is a source syntax/logical compatibility theorem in arbitrary IΣ2
models. It does not establish the ten source derivation cases, any source
set axiom image, a tagged seed interpretation, closed ZF-to-C222 provability,
or the final HA equivalence. Classical C222 object logic is legitimate here;
it is not an added excluded-middle constructor in the separate HA calculus.

## Cache plan

The exact minimal closure is the already authenticated encoder-only closure
from `reviews/validator-proof-context222-cache.json`, SHA256
`1291c1b923dd64dcebcb323cec22cde4d5afb437d830f9b315ee2792c15b4dd4`:
152 reused current-source modules, 117 Foundation, 503 artifacts, **40** explicit
external boundaries including Init and Aesop. The frozen Context inventory
had 39 because its parser omitted `public meta import Aesop` from
`Foundation.FirstOrder.Basic.AesopInit`; root caught this in independent
preflight before its compiler invocation. This plan corrects only that
header metadata and adds the actual Aesop primary boundary, pinned by the
accepted Enum proof-word inventory. The frozen Context files are unchanged.
It contains Formula.Basic/Functions,
Arithmetic.Schemata, Arithmetic.Basic.Hierarchy and Kalmar already. No new
Foundation dependency or compiler work is required by the plan. The selected
encoder and three syntax prerequisite objects remain the independently
accepted root-fresh objects, not the pending context object.

The accompanying JSON rehashes every current source, object, companion,
external boundary and relevant guide/primary source, and pins the existing
compiler/toolchain/manifest. It creates no overlay and executes no Lean.
If approved, author only the two new leaves with private regular outputs,
Lean4.32 `-M6000 -j1 -DElab.async=false`, the 512 MiB reserve guard and full
pre/post authentication. All attempts must be preserved.
