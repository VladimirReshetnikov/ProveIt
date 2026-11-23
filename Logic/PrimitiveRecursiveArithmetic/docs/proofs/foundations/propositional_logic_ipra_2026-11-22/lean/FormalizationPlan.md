# From finite propositional algorithms to object-level iPRA derivations

## Status and the target

The accompanying mathematical argument is a human proof in iPRA, with every
unbounded-looking construction replaced by a specified bounded loop or
primitive recursion. The Python code is independent executable evidence for
small instances. The Lean files are uncompiled proof candidates. None of
these three facts should be conflated.

For a closed numerical statement `phi : Fm PTm 0`, the final formalization
target is

```lean
LeanProofs.ConciseIPRA.Prf LeanProofs.ConciseIPRA.PRAAx [] phi
```

A theorem of type `Nat -> Prop` in Lean, a `Classical` proof of a semantic
existence statement, or a Python test run does not itself meet that target.

## Repository interface actually inspected

Pinned source: `VladimirReshetnikov/ProveIt` commit
`803d951d15834da5571e26d1f39988d921b29760`.

| Module / namespace | Relevant declarations | Intended use |
| --- | --- | --- |
| `ConciseIPRA.PR`, `LeanProofs.ConciseIPRA` | `PR.zero`, `PR.succ`, `PR.proj`, `PR.comp`, `PR.prec`; `PTm`; `PRAAx` | Explicit primitive recursive symbols and arithmetic object theory |
| `ConciseIPRA.Deduction`, `LeanProofs.ConciseIPRA.Prf` | `hyp`, `botE`, `andI`, `andE₁`, `andE₂`, `orI₁`, `orI₂`, `orE`, `impI`, `impE`, `weaken`, `subst`, `trans` | Actual object-logic proof construction and structural transformations |
| `IPRADerivations.Core.Pairing`, `LeanProofs.IPRA` | `pairT`, `fstT`, `sndT`, `fst_pair`, `snd_pair`; `simF`, `sim₁`, `sim₂` | Numeric tuples and simultaneous recursion |
| `IPRADerivations.Core.Search`, `LeanProofs.IPRA.Search` | `muF`, `mu`, `search_spec`, `search_found`, `search_minimal` | Search only within an explicit bound |
| `IPRADerivations.Foundations.BooleanBits`, `LeanProofs.IPRA.Foundations.BooleanBits` | `bnot`, `band`, `bor`, `bimp`, `Bit`; `*_bit`, `*_iff` | Boolean truth tables and decidable propositional cases |
| `IPRADerivations.Foundations.BoundedReflection` | `allB`, `exB`, `wit`, `all_reflect`, `all_dec`, `ex_elim`, `bounded_choice` | Bounded quantifiers represented by Boolean PR terms |
| `IPRADerivations.Foundations.BoundedSyntaxInduction` | `induction`, `induction_at`, `bounded_induction_closed` | Bounded-formula induction derived from quantifier-free induction |
| `IPRADerivations.Foundations.BoundedFixpoint` | `Ascent`, `valid_iter`, `fixpoint`, `fixpoint_closed` | The termination part of finite consequence/resolution saturation |

The `BoundedFixpoint.Ascent` fields are object-level validity preservation,
boundedness of a measure, constancy of its bound, and strict ascent on every
nonfixed step. Applying that theorem requires constructing all four fields.
The existence of the generic theorem does **not** mean that the propositional
closure instance is already formalized in the repository.

## Numerical definitions

Choose the already inspected pairing function
`pair(a,b) = (a+b)^2+a`. Its projections are primitive recursive bounded
arithmetic operations. One concrete formula encoding is:

- `bot = 0`;
- `var(i) = 5*i+1`;
- `and(a,b) = 5*pair(a,b)+2`;
- `or(a,b) = 5*pair(a,b)+3`;
- `imp(a,b) = 5*pair(a,b)+4`.

Positive numbers congruent to zero modulo five are invalid. In every valid
binary constructor, both children are strictly smaller than the parent code.
An explicit `isFormula(a)` bit is computed by a table indexed by `0..a`.
For an invalid input every exported numerical function returns a specified
default; theorems include the well-formedness premise. This makes all
functions total without assuming the input parses.

A list can be encoded by `nil=0`, `cons(x,xs)=1+pair(x,xs)`. Its tail is smaller
than its code. Length, lookup with a default, concatenation, set membership,
and a table update are primitive recursive course-of-values programs. To
avoid a hidden course-of-values assumption, implement the table accumulator
by one ordinary primitive recursion on the maximum index and prove that
lookup returns the earlier table entries.

For a formula code `a`, define the following total symbols and specifications.

1. `size(a)`, `subformulaList(a)`, `varBound(a)`, `subst(a,s)`, where `s` is a
   finite assignment of formula codes and all omitted variables map to
   themselves.
2. `eval(a,v)`, where `v` is a bit-vector of at least `varBound(a)` bits. Every
   binary node reads its children's already computed Boolean values. A dense
   support renaming may improve the bound; the simpler bound `2^varBound(a)`
   suffices for primitive recursiveness.
3. `allValuations(a)`, `taut(a)`, `sat(a)`, `entails(g,a)`, each a bounded scan
   through all bit vectors. Keep Boolean equivalence separate from IPC
   equivalence.
4. `proofCheck(c,p,g,a)`, where `c=0` checks IPC and `c=1` enables the additional
   LEM rule. `p` is a finite list of nodes; each node contains a finite context,
   conclusion, rule tag, and indices of earlier premises. The checker validates
   every tag, index, context extension, and conclusion. `weak` and `cut` may
   be accepted as derived structural rules, with explicit translations to the
   base natural-deduction calculus.
5. `modelCheck(M)`, verifying that a finite relation is reflexive, transitive,
   antisymmetric and that each atom's truth set is upward closed.
6. `force(M,w,a)`, computed in increasing formula-code order at all worlds.
   The implication clause is the bounded conjunction over `v<worldCount(M)`
   of `R(w,v) -> (force(M,v,b) -> force(M,v,c))`. This is Boolean evaluation of
   a *finite semantic relation*, not a classical interpretation of arbitrary
   arithmetic assertions.

Proof constructors produce bounded lists or DAGs. If a theorem refers to a
proof tree, a separate bounded DAG-unfolding transformation is required.
Its possible exponential blow-up is primitive recursive and is not a
polynomial-size claim.

## Dependency and proof order

### 1. Syntax, Boolean evaluation, and substitution

First prove projection, lookup, and append equations, then the strict
subformula-code bound. Convert each invariant over all indices up to the
current code to a Boolean bounded conjunction. Apply quantifier-free
induction to that conjunction using `BoundedReflection` or
`BoundedSyntaxInduction`. Establish substitution identity/composition,
support locality, and

`eval(subst(a,s),v) = eval(a, evaluatedSubstitution(s,v))`.

The complete recursive counterparts in `Propositional.lean` provide the
correct theorem statements and structural proof shape.

### 2. Numerical proof soundness

For a checked proof DAG of length `n`, the induction invariant is the bounded
conjunction asserting semantic validity of all earlier nodes. For Boolean
semantics, every context/valuation check is bounded. For finite Kripke
semantics, include persistence, checked beforehand by a bounded structural
induction, in the implication-introduction and elimination steps. The
corresponding universal numerical statement is an object-level theorem in
iPRA, since its proof uses induction only on a PR Boolean invariant.

The `lem` branch has a Boolean proof and is rejected in the Kripke/IPC checker.
A regression test explicitly verifies this separation.

### 3. Classical completeness and normal forms

Implement the valuation-literal proof constructor from the report. Prove its
correctness by simultaneous induction on the formula table, including both
truth and falsity cases. Combine all valuation branches by iterated LEM/case
splits. The numerical conclusion uses the explicit output proof code:

`taut(a)=1 -> proofCheck(1, classicalProof(a), [], a)=1`.

Canonical CNF/DNF, Shannon substitution, finite interpolation and forgetting
are separate bounded table transformations. Their specifications quantify
only over explicitly bounded valuations.

### 4. Resolution and SAT algorithms

Enumerate the at most `3^n` non-tautological clauses over `n` variables. The
resolution closure is a bit-vector and each newly added clause stores its
antecedent indices and pivot. The ascent measure is the number of present
clauses; the bound is `3^n`. Supply all four `Ascent` fields and instantiate
`BoundedFixpoint`. Prove every inference sound by the two values of the
pivot. Davis-Putnam elimination supplies completeness and model recovery.
DPLL uses recursion on the number of unassigned variables, with fuel bounded
by the full binary decision tree. Tseitin clauses have width at most three;
prove the gate identities and then existence/uniqueness of the extension
by induction over subformulas.

### 5. Finite IPC saturation

Let `S` be the duplicate-free subformula list of the goal and context, plus
bottom. Let `m=length(S)` and `N=m*2^m`. A finite relative consequence relation
is a bit-vector of `N` possible pairs `(context,conclusion)`. The saturation
operator adds the natural-deduction rules, weakening and cut, **with all
formulas restricted to S**. A complete scan has a fixed bound obtained by
enumerating rule tags, contexts and their at-most-three premises.

Store, with each newly set bit, a checked proof DAG node. Prove validity of
the witness table, then supply `Ascent` with measure the count of set bits and
bound `N`. A fixed point is obtained within `N` rounds. This proves bounded
termination without cut elimination and without searching unboundedly for a
proof. Intermediate rules may use a round table or in-place sequential scan;
the chosen implementation's invariant must match its update discipline.

### 6. Prime worlds and the truth lemma

A world is a context bit-vector `T<2^m` satisfying:

- `bot` is not in `T`;
- the fixed relation's row at `T` equals `T`;
- if an `or` formula is in `T`, at least one disjunct is in `T`.

Order worlds by inclusion and force atoms by membership. Enumerate all such
worlds; there are at most `2^m`. A greedy bounded extension scans S once,
adding a formula exactly when the fixed relation still does not derive a
specified target. Prove that the resulting maximal avoiding set is closed
and prime. Cut establishes closure; disjunction elimination establishes
primeness; implication introduction supplies an extension witnessing the
failure of an implication.

The structural truth lemma has the bounded form

`CanonicalModel(S,D,M)=1 -> forall world w, forall formula a in S,
 force(M,w,a)=membership(w,a)`.

Here `CanonicalModel` is a PR certificate predicate checking that D is the
specified fixed point, that the listed worlds are exactly the bottom-free
closed prime subsets of S, that the relation is inclusion, and that atom
truth is membership. Its bounded tests also entail `modelCheck(M)=1`.
`modelCheck(M)` alone would be an insufficient premise: an arbitrary finite
model need not be this canonical one.

Conclude the explicit proof-or-countermodel alternative for the input sequent.
All decisions in the prime-extension proof are equality tests on a finite
relation, so the argument does not import excluded middle for arbitrary
arithmetical propositions.

### 7. Porting schemata and closing numerical theorems

`ObjectExamples.lean` gives actual `Prf PRAAx` proof candidates for identity,
conjunction/disjunction commutativity, composition, double-negation
introduction, double-negated excluded middle, and explosion. These provide
small initial checks of the repository import and notation.

For each numerical metatheorem, assemble the object formula using `PTm.app`
and the compiled `PR` symbols, discharge all bounded invariants, and close
all numerical variables with the repository's universal-closure helpers.
Inspect the resulting theorem's type: it must be `Prf PRAAx [] phi`, with no
assumption whose content is the theorem itself. Generic certificates such as
`Ascent` are permitted only after their instance fields have been proved.

## Exact closed numerical endpoints

`ObjectExamples.lean` defines `applyOne` and `applyTwo` from the inspected
`PTm.app` constructor, and uses `Fm.all` to close the following actual
`Fm PTm 0` values:

- `classicalCompletenessSentence valid taut prove check` represents
  `forall a, (valid(a)=1 and taut(a)=1) -> check(prove(a),a)=1`;
- `ipcCompletenessSentence valid prove model check countercheck` represents
  `forall a, valid(a)=1 -> (check(prove(a),a)=1 or
  countercheck(model(a),a)=1)`.

In the first sentence, `check` validates an empty-context CPC derivation of
the given goal. In the second it validates an IPC derivation; `countercheck`
validates a *pointed nonempty* finite Kripke model refuting the goal. These
functions are fixed primitive recursive definitions of arity one or two,
not an unbounded interpreter for arbitrary PR programs. Their PR definitions
and proofs remain to be supplied. The endpoint of that work is a theorem
whose type is `Prf PRAAx [] (classicalCompletenessSentence ...)` or
`Prf PRAAx [] (ipcCompletenessSentence ...)`.

An eighth small object proof, `unary_predicate_identity`, already supplies a
constructor-only candidate for a closed quantified arithmetic statement,
`forall a, f(a)=1 -> f(a)=1`, for every fixed unary symbol f. It demonstrates
the exact type/quantifier interface; it is not a completeness theorem.

## Completion gates

1. Compile the standalone core and inspect theorem dependencies.
2. Compile the eight object examples in the pinned ProveIt project.
3. Prove totality/defining equations for the numeric encoders and all table
   operations, with explicit bounds on malformed-input behavior.
4. Complete object-level soundness and Boolean completeness.
5. Complete relative IPC closure, prime extension and finite truth lemma.
6. Export closed `Prf PRAAx` theorems and reproduce the report's examples from
   their numeric proof/checker witnesses.

The package completes the mathematical and executable-reference portions of
this path. It does not claim that gates 1–6 have been carried out in Lean.
