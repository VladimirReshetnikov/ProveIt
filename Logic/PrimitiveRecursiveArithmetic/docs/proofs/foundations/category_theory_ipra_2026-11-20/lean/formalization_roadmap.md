# Formalization roadmap: definitions, dependencies, and open work

This roadmap targets first-order intuitionistic primitive recursive arithmetic
(iPRA), not a fragment of ordinary Lean selected merely by avoiding `Classical`.
The pinned repository source is part of the evidence; new code is an uncompiled
integration draft. Every statement below separates existing syntax, inspected
derivations, and the work still needed.

## 1. Object language already present

`ConciseIPRA.PR` defines the following arity-indexed syntax:

```lean
inductive PR : Nat → Type
  | zero : PR 0
  | succ : PR 1
  | proj {k : Nat} (i : Fin k) : PR k
  | comp {m k : Nat} (f : PR m) (gs : Fin m → PR k) : PR k
  | prec {k : Nat} (f : PR k) (g : PR (k + 2)) : PR (k + 1)

inductive PTm (n : Nat) : Type
  | var (i : Fin n) : PTm n
  | app {k : Nat} (f : PR k) (ts : Fin k → PTm n) : PTm n
```

The finite functions in these inductive constructors are metatheoretic finite
tuples of syntax. They are not arbitrary number-theoretic functions inside
iPRA. Terms are scoped, and substitutions use `Fin n → PTm m` with the usual
identity, composition, lifting, and binder substitution laws.

`ConciseIPRA.Syntax` defines scoped formulas with equality, false, conjunction,
disjunction, implication, universal quantification, and existential
quantification. `Fm.QF` is recursively true exactly when no quantifier occurs.
`ConciseIPRA.Deduction` supplies intuitionistic natural deduction. `PRAAx`
contains the PR defining equations, successor injectivity and separation from
zero, and the induction schema restricted by an explicit proof of `φ.QF`.
Thus the target of a theorem is a term inhabiting `Γ ⊢[PRAAx] φ`.

Do not replace this machinery with a semantic structure containing arbitrary
functions `Nat → Nat` and assume that its Lean proof has become an iPRA proof.
Do not identify an externally terminating structural interpreter for `PR`
syntax with a primitive-recursive function of the program code and argument.

## 2. Category and family syntax

The existing `PresentedCategory.Pres` has:

| Field | Syntax type | Meaning |
|---|---|---|
| `Obj` | `Fm PTm 1` | valid object code |
| `Hom` | `Fm PTm 3` | valid arrow from first object to second |
| `Eqv` | `Fm PTm 4` | equality of parallel arrow codes |
| `idt` | `PTm 1` | identity code |
| `cmp` | `PTm 5` | composite, with endpoints and two arrows supplied |

The field `cmp(a,b,c,g,f)` denotes `g ∘ f`. Law fields provide object-language
derivation constructors for equality reflexivity, symmetry, transitivity,
identity and composition typing, composition congruence, units, and
associativity. The report additionally keeps endpoint-validity guards explicit
when they matter; those can be added as separate derivable laws without
changing the existing `Pres` type.

`Adjunction.Fun` contains object and arrow terms of arities 1 and 3; its laws
are object-language typing, congruence, identity, and composition rules.
A general natural transformation between specified `F,G` can be added as one
term `alpha : PTm 1`, plus laws for

```
Hom_D(F(a),G(a),alpha(a))
Eqv_D(F(a),G(b), G(f) ∘ alpha(a), alpha(b) ∘ F(f)).
```

Two specified transformations are equal when their components are equal at
every valid object. This is a formula schema or an explicitly quantified
formula for fixed term families, not an internal set containing all such
families. Define identity components and vertical composition by term
substitution and prove their laws from the category laws. Whiskering is term
composition with functor object/arrow terms. Horizontal composition and
interchange then need finite equational proofs, with no induction on formulas.

`Yoneda.Fam` already represents a parameterized presheaf by `Par : Fm PTm 1`,
`Car : Fm PTm 3`, `Sim : Fm PTm 4`, and `act : PTm 5`. `FamLaws` supplies
congruence and action laws. The report's complete setoid presentation also
includes carrier closure and equivalence laws wherever used; extend the law
record for any new theorem needing a field absent from the minimal upstream
record. The existing Yoneda proof uses only its listed minimal fields.

## 3. Existing checked-shaped derivations to reuse

The inspected source statements have the correct object-language shape:

* `PresentedCategory.inverse_unique_closed` closes the inverse uniqueness
  formula under five universal quantifiers.
* `Yoneda.yoneda_closed` closes the presentation-wise Yoneda identity.
* `Yoneda.rep_laws`, `yoneda_rep`, and `yoneda_rep_arrow` instantiate it at a
  representable family.
* `Adjunction.psi_phi` and `phi_psi` prove the two hom-correspondence round
  trips from the unit, counit, functor laws, and triangle equations.
* `Adjunction.corr_tri_left`, `corr_tri_right`, `corr_eta_nat`, and
  `corr_eps_nat` supply the converse from a specified natural correspondence.
* `SplitEquivalence` implements the quasi-inverse using explicit object
  representatives, isomorphisms, and hom-lifting terms.

“Inspected” is not a claim that a fresh local build has been executed. The
new adapter derives representability uniqueness from these interfaces, and
the second adapter records the algebraic identities needed by density.

There is one interface refinement: upstream `NatLaws` asks for one term
`alpha(p,A,x,f)` that is valid/natural uniformly in both `p` and `A`. For
representables that may demand arrows between object pairs where none exist.
The new `LocalYoneda.AtLaws` fixes `p` and `A` in the current context, proves
the same Yoneda calculation, and permits a genuinely single specified
transformation. The representability adapter uses this localized record.

## 4. Completing the density theorem

Use a fixed PR triple code `t = (a,x,f)`. At object `b`, define:

```
Gen(b,t) := Obj(a) ∧ Car(a,x) ∧ Hom(b,a,f)
Val(b,t) := act(b,a,f,x)
GenEq(b,t,t') := Sim(b,Val(b,t),Val(b,t')).
```

Parameter slots for the family are suppressed above but retained in actual
syntax. Reindex along `k : c → b` by `(a,x,f) ↦ (a,x,f ∘ k)`. The canonical
generator of `z ∈ P(b)` is `(b,z,id(b))`. `Density.generator_roundtrip` and
`reindex_value` are the object-language calculations for this presentation.

Remaining steps: construct the tuple terms; prove their projections; add the
carrier and equivalence law derivations; define the canonical maps using term
substitution; encode a **fixed uniformly supplied** cocone as a term with
explicit indexing slots; prove its mediator and uniqueness by the calculations
in the report. No transitive-closure quotient or arbitrary colimit existence
is needed, since equality is the value relation.

## 5. Finite limits, and the distinction between two results

For an arbitrary presented category, a supplied binary product has object,
projection, and pairing terms, together with equations and uniqueness. A
supplied equalizer has an object, inclusion, and lifting term. The
product/equalizer construction for a **fixed finite diagram** is a finite
metatheoretic construction on these terms and proofs. Its output is one iPRA
derivation for each fixed shape. This does not justify induction on the
unbounded formula “every diagram of size n has a limit.”

For finite sets, use explicit table codes. Here variable diagram size can be
handled by primitive recursion because validity and commutation tests are
bounded numerical tests. Use base `m+1` codes for maps `[n] → [m]`, checking
that each digit is strictly below `m`. There are `m^n` valid codes, with
`0^0 = 1`. The base is always positive, including when the codomain is empty.

The existing `FiniteLimits` module fixes the numbers of vertices and arrows
in the metatheory. It supplies the retention test `K` with separate soundness
and completeness hypotheses. Its source explicitly excludes constructing `K`
from arbitrary arrow tables. To complete the uniform theorem:

1. Encode the diagram by finite arrays of cardinalities, endpoints, and maps.
2. Define a bounded-product Boolean commutation test `K`.
3. Prove both `K` specifications by quantifier-free induction on the bounded
   conjunction accumulator, after expanding its characteristic function.
4. Prove the rank/select identities with quantifier-free numeric invariants.
5. Use the tuple rank as the mediator and projection uniqueness as in the
   report.
6. Handle the empty diagram (`[1]`) and any zero cardinality separately.

The positive-cardinality source theorems cannot discharge Step 6 by themselves.

## 6. Finite colimits and exponentials

For a finite diagram, let `N` be the cardinality of the disjoint union. Define
an initial Boolean adjacency matrix with reflexive entries and undirected
generator identifications. Define bounded Warshall closure by

```
R_(k+1)(i,j) = R_k(i,j) OR (R_k(i,k) AND R_k(k,j)),  k < N.
```

Use a Boolean, bounded numerical invariant describing paths whose internal
vertices have codes below `k`; encode bounded path tests and use only the
corresponding QF characteristic function in induction. Keep all paths bounded
in the finite graph. Show the final relation is the least coded finite Boolean equivalence relation
containing the generator identifications; choose least representatives by
bounded search. A compatible cocone is constant on adjacency, then on the
bounded closure, and hence factors uniquely through representative ranks.
Do not use unbounded equivalence closure on undecidable arithmetic relations.

For exponentials, `[m]^[n] = [m^n]`. A point is the increasing-code rank of a
valid table. Evaluation selects that table and then a digit; curry encodes
each finite row and takes its rank. The existing `FiniteSetClosed` proves the main digit and
round-trip equations with positivity guards. Extend it by explicit numerical
cases: `n=0` gives `[1]`; `m=0<n` gives `[0]`; a map into the empty set forces
an empty domain; `0^0=1`. These are mathematical proofs in the report and
tested in the executable model, but the new case-split derivations are not
included in this Lean draft.

## 7. Limits preserved by right adjoints

Fix a diagram and a supplied limit operation in `D`, plus `L ⊣ R`. Given a
cone from `x` to `R D_j`, apply `Ψ` componentwise, use naturality of `Ψ` to
obtain a cone from `Lx`, take its supplied mediator, and apply `Φ`. Derive
projection equations from naturality and the two round trips. For uniqueness,
apply `Ψ`, invoke uniqueness of the original limit, and then apply `Φ`.
For the dual colimit theorem use opposites. This needs definitions of a fixed
diagram, cone, mediator term, and universal-property law record; it does not
need a category of all diagrams or an unrestricted functor category.

## 8. Monads, Kleisli, Eilenberg–Moore, and idempotents

Add a monad record with a specified endofunctor `T`, terms `eta : PTm 1` and
`mu : PTm 1`, naturality rules, and the two unit and associativity equations.
For a Kleisli presentation set `Hom_K(a,b,f) := Hom_C(a,Tb,f)`; keep objects
and equality; set identity to `eta(a)` and composition to
`mu(c) ∘ T(g) ∘ f`. The associativity and unit proofs in the report are finite
equational chains. Encode every constructor directly as a `PTm`; supply
congruence and typing derivations before the equations.

For an Eilenberg–Moore presentation, code `(a,h)` with `h : T(a) → a` and
include the two algebra laws in the **object formula**. Its morphism formula
asserts `f ∘ h = k ∘ T(f)`. These formulas may be undecidable. Identity and
composition terms remain PR; validity is proved logically, never tested by
an algorithm. Add the free/forgetful terms and verify the displayed
hom-correspondence to obtain the adjunction.

For the Karoubi envelope, code `(a,e)` with `e ∘ e = e`. A morphism `f` from
`(a,e)` to `(b,d)` satisfies `d ∘ f ∘ e = f`; identity is `e`, not `id(a)`.
Prove typing, units, and composition from the finite equations. Split an
idempotent `p` at `(a,e)` through `(a,p)` using `p` as both structure maps.
The proof must show `ep=p=pe` from the envelope typing equation before using
`p` as the new object's idempotent. No image search is involved.

## 9. Validation gates for completion

1. Build the pinned upstream project and the new adapters with Lean 4.32.0.
2. Confirm that main theorems conclude `Prf PRAAx` formulas.
3. Close free term variables by the existing `closeUniv` machinery.
4. For each new numerical construction, give a concrete `PR` tree and actual
   QF invariants, rather than a semantic assertion of computability.
5. Keep law records explicit; supply them for every claimed concrete example.
6. Record hypotheses not discharged, including selected limits, split
   representatives, lower bounds, and any positivity conditions.
7. If independent checkable derivation files are desired, serialize proof
   syntax and validate the checker/serializer separately. Neither a tested
   Python function nor the absence of Lean placeholders replaces this gate.

The new mathematical work does not need stronger induction merely because
the predicates describing arrows or equality contain quantifiers: the
structural proofs instantiate and compose those predicates without inducting
on them. Numerical variable-size algorithms are where the QF-induction audit
must be performed explicitly.
