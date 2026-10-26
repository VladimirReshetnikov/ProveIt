# Arithmetic adapter between Foundation GG and conventional HA

Read-only audit by `/root/circuit_reduction`, 26 October 2026. No Lean module
was compiled or changed for this audit. The frozen GG, HA, equation, and LV
packets remain unchanged. This document proposes interfaces; signatures marked
**proposed** are not existing theorems.

## Conclusion and smallest useful next packet

Reuse Foundation's existing GG recursion. The smallest useful new bridge is
a **syntax translation and intuitionistic proof-tree map from Foundation's
ordered arithmetic language into the already checked PAHF-language HA**.
Interpret `1` as `S 0` and `<` as `exists z, x + S z = y`. Preserve primitive
implication, quantifiers, and equality. The logical proof map does not require
any arithmetic axioms. A subsequent finite arithmetic library must prove the
translations of the actual PeanoMinus axioms and arbitrary induction in HA.

This separates three different obligations that cannot be identified by a
notation change:

1. actual intuitionistic derivations across the two syntax/binder conventions;
2. HA proofs of the translated Foundation PA axioms, including induction;
3. an HA proof that the particular translated conclusion is the intended
   arithmetic no-zero/no-refutation sentence.

Defining a new Foundation theory whose axioms are exactly `PA.ToTheoryᵢ` does
not discharge(2). A standard-model or classical all-model argument does not
construct the required intuitionistic derivations either.

## Sources actually inspected

Foundation sources are in
`/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation`,
checkout `32e1a0956a8622fad067328ca1959729a7634428`. The active project lists
the Foundation library at `lakefile.toml:192`; its compatible59-module GG
cache was previously authenticated for the frozen adapter. This audit reused
no compiled objects and makes no new closure or import-compatibility claim.

I read the complete relevant constructors and definitions, not the entire
66,936-line PASyntax development: PAHF syntax/renaming/substitution at
`PASyntax.lean:100–139,447–464`, closures at556–560, induction substitutions
at8041 and8154, and all six axioms/induction/closed axiom predicates at
8216–8323. The Foundation arithmetic axiom/schema definitions, all Hilbert
constructors, theory proof representation, GG module, equality definitions,
and binder rewrites were read directly. The portions of PeanoMinus following
the axioms are model-semantic algebra, not HA proof trees.

Scoped searches over `Logic/Interpretability/PAHF/Lean`,
`Logic/FoundationPort/Coq/FirstOrder`, and the current HA modules found no
PAHF-to-Foundation arithmetic syntax/proof adapter. In particular a literal
cross-namespace search for PAHF/`SetTheory.PA` with Foundation/`LO` in the
repository's Lean/Coq logic sources found none. This is a scoped search, not a
claim about all external developments. The Coq arithmetic port retains the
same separate syntax and its PeanoMinus core explicitly packages semantic
laws; its existing GG proof is useful prior art, not an HA arithmetic adapter.

## Exact existing interfaces

* `Foundation/Syntax/Predicate/Language.lean:94`: `Language.ORing.Func` has
  `zero,one : Func 0` and `add,mul : Func 2`; `Rel` has `eq,lt : Rel 2`.
  There is no primitive successor or subtraction symbol. `ℒₒᵣ` is this exact
  language, despite the historical “ordered ring” name.
* `Syntax/Predicate/Term.lean:27`: `Semiterm L ξ n` distinguishes bound
  variables `Fin n` and free variables `ξ`. `Semiformulaᵢ` at
  `FirstOrder/Intuitionistic/Formula.lean:18` has falsity, relations,
  conjunction, disjunction, implication, universal and existential binders.
* `FirstOrder/Intuitionistic/Deduction.lean:58`: `HilbertProofᵢ` has external
  schema axioms, modus ponens, generalization, verum, K/S, three conjunction
  and three disjunction axioms, and four quantifier axioms. `𝗜𝗻𝘁¹` at41 adds
  only ex falso. It has no built-in equality rule: equality enters as theory
  axioms. Its `Theoryᵢ.Proof` at306 uses a finite embedded theory context.
* `FirstOrder/Basic/Eq.lean:31–57`: the equality theory consists of reflexivity,
  symmetry, transitivity, function congruence, and relation congruence. At
  `ℒₒᵣ` this means the three logical equality axioms, four function-symbol
  cases(including constants), and two relation-symbol cases.
* `Arithmetic/PeanoMinus/Basic.lean:15–55`: PA-minus is that equality theory
  plus the seventeen arithmetic/order axioms listed below.
* `Arithmetic/Schemata.lean:19,27,53`: `succInd φ` is the **curried** classical
  formula `φ(0) → (forall x, φ(x) → φ(x+1)) → forall x, φ(x)`;
  `InductionScheme` takes the universal closure of each instance;
  `Peano` is PeanoMinus union all such instances.
* `FirstOrder/NegationTranslation/GoedelGentzen.lean:11`: positive relations
  become double negations, negative relations become single negations,
  conjunction/universal remain, and disjunction/existence become negative
  encodings. `Derivation.imply_doubleNegation` at134 proves the needed
  implication equivalence. `rew_doubleNegation`, `subst_doubleNegation`, and
  `emb_doubleNegation` at54–60 supply structural compatibility.
* `DiophantineConsistency.FoundationTheoryGG.theory_intuitionistic` already
  proves `T ⊢ φ → T.ToTheoryᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ L) ⊢ φᴺ`. It preserves
  the actual finite axiom list. It supplies no arithmetic axiom theorem.
* `DiophantineConsistency.HA.Derives` has actual intuitionistic natural
  deduction with `eqRefl` and Leibniz `eqElim`. `HA.Proves` is finite use of
  `SetTheory.PA.Formula.Ax_s`, the six ordinary arithmetic axioms plus fully
  closed formula-induction instances. `HA.Derives.erase` goes only to the
  classical PAHF calculus. `HADeduction` supplies actual finite-context proof
  composition; no converse erasure is available or justified.

## Proposed syntax/proof bridge

Use only narrow imports, initially Foundation intuitionistic deduction and
`DiophantineConsistency.HADeduction`. Do not import the DiophantineConsistency
umbrella or broad `Mathlib.Tactic`: Foundation declares its vector operation
`Matrix.map` at `Vorspiel/Matrix.lean:248`, while Mathlib declares its different
matrix operation at `LinearAlgebra/Matrix/Defs.lean:110`. Root has already
isolated this collision in another leaf. Existing compiled files are not a
proof that this new combination of imports is compatible.

**Proposed definitions**, in a fresh `FoundationPAHFSyntax` namespace:

```lean
term : {n : Nat} → Semiterm ℒₒᵣ Nat n → SetTheory.PA.Term
formula : {n : Nat} → Semiformulaᵢ ℒₒᵣ Nat n → SetTheory.PA.Formula
sentence (φ : Sentenceᵢ ℒₒᵣ) := formula (Rewriting.emb φ)
```

At depth n, translate `#i` to `.var i.val`, and `&j` to `.var (n+j)`.
Translate `0,1,+,*` literally to `zero,succ zero,add,mul`. Translate equality
to `.eq`. Translate `<(a,b)` to the capture-avoiding PAHF formula

```text
ex(eq(add(rename succ a, succ(var0)), rename succ b)).
```

All formula constructors map homomorphically. The additional binder in the
definition of `<` must participate in every renaming/substitution proof; an
unshifted witness formula would be wrong. It is useful to first define the
term translation with arbitrary bound/free target-term environments and prove
its substitution law, then specialize to the canonical environment above.

The first bounded implementation should supply these exact structural goals:

```lean
-- Proposed, with φ : Semipropositionᵢ ℒₒᵣ 1 and t : SyntacticTerm ℒₒᵣ.
formula (Rewriting.free φ) = formula φ
formula (Rewriting.shift ψ) = PA.Formula.rename Nat.succ (formula ψ)
formula (φ/[t]) = PA.Formula.subst (PA.Formula.instTerm (term t)) (formula φ)
formula (ψ/[]) = PA.Formula.rename Nat.succ (formula ψ)
```

The last equation uses the bound-variable shift of a proposition into one
new bound slot, not the free-variable `Rewriting.shift`; prove the appropriate
general depth version before specializing. Foundation's `Rew.q` fixes#0 and
shifts every other bound variable, whereas `Rew.free` opens the **last** bound
slot (`Rew.free_bvar_last`). The above free identity is for depth1 only;
an unrestricted identity at arbitrary depth would be false. Parameterized
rewrite compatibility and a nested-quantifier check should prevent that error.

Next, in a separate small proof-map leaf, the key **proposed theorem** is:

```lean
theorem hilbert_toHA {φ : Propositionᵢ ℒₒᵣ}
    (p : (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ) ⊢! φ) :
    HA.Derives [] (formula φ)
```

Induct on the existing Hilbert tree, using the intuitionistic natural
deduction rules, the exact instantiation/free identities, and no arithmetic
axioms. This is a proof-calculus interoperability map, not another GG
algorithm. Generalization has no undischarged assumptions at this pure
Hilbert level. Then expose the actual finite theory context via
`Theoryᵢ.Proof`: map its finite list, use the pure implication proof, and
compose with those finite translated axioms.

A useful relative endpoint has target axiom predicate
`B a := exists σ in T, a = sentence σ`; it constructs `HA.Relative B [] ...`
from the actual Foundation theory proof. This explicitly retains every axiom,
and must not be advertised as `HA.Proves` until the arithmetic cases below
are independently discharged. The syntax leaf is plausibly200–350 lines plus
focused checks, followed by a similarly bounded logical proof map. These are
scope estimates, not validated line-count or runtime claims.

## Arithmetic obligations that remain after the logical map

For the exact translated-axiom target, the central **proposed theorem** is

```lean
theorem peano_axiom_toHA {σ : Sentence ℒₒᵣ} (hσ : σ ∈ Arithmetic.Peano) :
    HA.Proves (sentence σᴺ)
```

Its PeanoMinus cases require actual derivations as follows. The proof library
should first derive conventional un-translated arithmetic facts, then obtain
these geometric/Horn axiom translations by constructive logical composition.
One cannot reuse Foundation's `weakerThan_of_models` instances for this step.

| Exact axiom(s) | Required HA proof content under the `<` definition |
|---|---|
| Equality reflexivity/symmetry/transitivity; four function and two relation congruences | Built-in `eqRefl`/`eqElim`; relation congruence includes substitution under the existential defining `<`. No new equality axiom is needed in PAHF HA. |
| `addZero`, `mulZero` | The corresponding sealed PAHF axioms, explicitly opened/closed. |
| `addAssoc`, `addComm` | Induction using `addSucc` and `addZero`; derive zero-on-left and successor-on-left as needed. |
| `mulOne`, `mulAssoc`, `mulComm`, `distr` | Recursion/induction from `mulSucc`, `mulZero`, and the additive lemmas. |
| `addEqOfLt` | Eliminate the `<` witness and use its successor as the requested summand. |
| `zeroLe`, `zeroLtOne`, `oneLeOfZeroLt` | Explicit predecessor/zero case decomposition, constructed by formula induction; zeroLtOne has witness0. Foundation `≤` means equality-or-strict-order. |
| `addLtAdd`, `mulLtMul` | Construct existential witnesses using the proved semiring laws; positive multiplicative factor is explicitly a successor. |
| `ltIrrefl`, `ltTrans` | Successor/addition cancellation and witness composition; no semantic linear-order instance. |
| `ltTri` | Constructive simultaneous/nested induction on naturals with successor injectivity and zero-not-successor. This is arithmetic comparison, not arbitrary-formula LEM. |

The arithmetic atoms here are not given decidability by the Lean metatheory.
Where a proof uses decidability of equality or order, HA must prove the
corresponding object-language disjunction. Many Horn/geometric translations
can instead avoid that detour: carry double-negated premises to a stable
translated conclusion, while introducing the actual existential witnesses
inside the proof under the original positive premises.

For an arbitrary induction instance φ, instantiate conventional HA induction
at the translated intuitionistic body `formula φᴺ`. Then:

* use `subst_doubleNegation` and the new syntax-substitution bridge for the
  zero and successor substitutions;
* convert `x+1` to `S x` by an actual HA equality proof from `addSucc/addZero`,
  and use equality elimination in the arbitrary translated body;
* use `imply_doubleNegation` and negative stability already present in
  Foundation to match the two translated implications;
* convert the curried induction premise to PAHF's conjunction-premise form;
* handle the complete universal closure of parameters explicitly.

Foundation `univCl` uses `fvSup`, `Rew.fixitr`, allClosure, and `toEmpty`
(`Basic/Syntax/Rew.lean:405,463`). PAHF `sealPA` uses `bound` and `closeN`.
Their literal syntactic equality is not established; a closure proof adapter
must open the sealed HA axiom and reclose the required finite parameter list.
The classical semantic induction theorems later in `Schemata.lean` are not
usable substitutes. No unrestricted induction on Lean predicates is needed.

After these cases, the finite translated-theory proof can be converted to
`HA.Proves`. This gives the **proposed composition**, using the frozen GG map:

```lean
theorem pa_negative_translation_toHA {φ : Sentence ℒₒᵣ}
    (h : Arithmetic.Peano ⊢ φ) : HA.Proves (sentence φᴺ)
```

This conclusion is the translated sentence, not yet an arbitrary original
negative arithmetic sentence.

## Which target-stability claim is actually needed

`HANegativeStability` proves `HA ⊢ ¬¬A → A` for its displayed fragment.
It does **not** prove `HA ⊢ Aᴺ ↔ A` for every member of that fragment.
In particular its constructor `Negative.neg` permits an arbitrary quantified
matrix. Replacing that matrix by its GG translation is a separate matter;
double-negation stability alone does not supply a double-negation shift,
Markov principle, or witness extraction under quantifiers.

The actual equation sentence is especially simple:
`closeN 14 (equation → bot)`, with one atomic equality as matrix. Foundation's
classical NNF universal closure of a negative equality translates to the same
universal closure of a single negated equality. Thus its conclusion bridge
can be a direct syntax identity after the term translations, plus proved
`x+1=S x` compatibility. No arithmetic equality-decidability theorem is needed
just to remove GG from this special no-zero shape. The huge constants can stay
opaque binary/Horner terms; no unary expansion or `splitNatural` evaluation is
required by these structural proofs.

For the refutation side, the exact represented predicate and its quantifier
structure still have to be fixed. If a bounded decidable verifier matrix is
used, prove its HA decidability/translation identity at that actual syntax.
Do not infer it solely from an external Lean primitive-recursive description.
The missing actual215 internal arithmetic calibration and the convention for
the represented ZFC refutation predicate remain separate obligations. Neither
the240-machine PA theorem nor external `ConZFC` is silently substituted here.

## Alternative: conventional HA directly in Foundation

A new `Theoryᵢ ℒₒᵣ 𝗜𝗻𝘁¹` can use manually written intuitionistic equality,
the seventeen un-translated arithmetic axioms, and induction for **all**
intuitionistic formulas. This avoids changing proof calculus in the middle of
the GG argument, and its induction-translation lemma should be short using
`imply_doubleNegation`. But its identification with conventional
`0,S,+,*` HA still needs exactly the arithmetic/order definitional-extension
proof above, plus a syntax map to bind the maintained PAHF equation sentence.
Blindly embedding classical NNF axioms is wrong: classical implication is
encoded as a disjunction, not intuitionistic implication. Merely renaming
such an axiomatization “HA” would conceal the main gap.

I therefore recommend the narrow syntax/proof map first. It makes the eventual
conclusion literally an existing `HA.Proves` statement and can be validated
without importing the large arithmetic theory closure or altering a vendor.
The base arithmetic derivations and arbitrary induction transport can then be
separate reviewable leaves. No complete HA endpoint is claimed by this audit.

## Pinned sources

Foundation paths below are relative to its `Foundation/` directory; current
module paths are relative to `Lean/DiophantineConsistency/`.

| Source | SHA256 |
|---|---|
| `Syntax/Predicate/Language.lean` | b5ef82f9c7198f984d2bfc2a765d67e2f815a6d7d65c1b66eebb3373789b676e |
| `Syntax/Predicate/Term.lean` | 18cf80e4614ea6048e4b277fd99b1f662a5330ae6d7853f57f6f4ce4d3a0601a |
| `Syntax/Predicate/Rew.lean` | 61d0551a3e119cf48cb840516751c9da917b11a7da56c064ccfa37e772ca5edc |
| `FirstOrder/Intuitionistic/Formula.lean` | 9618d2db39b856681799a1f2445ef572e47ae66f715170beb76583be998d149b |
| `FirstOrder/Intuitionistic/Deduction.lean` | c657f4f2f1789c6731ef93db03585d72c095051c116b8ed4c3a563b73f68c41b |
| `FirstOrder/Basic/Eq.lean` | f1a53113cb76030f89a78579f822dcfab1e53dccb1b8ede7caf8287630ab63d6 |
| `FirstOrder/Arithmetic/PeanoMinus/Basic.lean` | 856a38ddda30c1505f6d991e6033ef7c41ebc82418b503ab711dfe173dc72303 |
| `FirstOrder/Arithmetic/Schemata.lean` | 5b1a1d84b71c3f943a0867c14d3b0c8c381062ec742d984fefdacf9f2209a6fd |
| `FirstOrder/NegationTranslation/GoedelGentzen.lean` | 52fabd00a01e1f5671e1f078c36f9848f2e219e0a4e616deaad4e523057586ea |
| repository `Logic/Interpretability/PAHF/Lean/PAHF/PASyntax.lean` | 1c2a64fc5cd25092287a94af33c6ea4ce7815615965aa35c1c6fce6e18206b37 |
| `FoundationTheoryGG.lean` | e45262d232cf99f97ee2595f422b8f8afd7306e05eb6f4c8fcdb7c712f8cc2b0 |
| `HAProofs.lean` | c4af3acb35ed46bd4d1dc36eba36500ff0254e69c6e552aa3cef9b468a1cd943 |
| `HADeduction.lean` | fd71974da01171f90c516b64ecb3c994a761e1163bf978f14eb7b2b6f884bc19 |
| `HANegativeStability.lean` | e6b9bbc501a652444992de39e0924eb8a3596d7938ad3d0db8cb15bff19f586d |
| `ArithmeticExpression.lean` | 19fe455df9e5a2f504af9cddcc4f3af10522c97f11f119e20b64195cf96b7baf |
| Coq `FirstOrder/Arithmetic/PeanoMinus/Basic.v` | d441486ef6f60a0219290d41f84012b1634943e63810b6bdc43eca6c81a50759 |
| Coq `FirstOrder/Arithmetic/Schemata.v` | db6f4cee1b770ce3acb74475e38d9f59650f24924e19d59f0b3f6ad634c81ead |
| Coq `FirstOrder/NegationTranslation/GoedelGentzen.v` | cbaca0de5b793f34b92bc3baa24c3a8cfd9a30e65baabfd1e7e3687a3d01a521 |
