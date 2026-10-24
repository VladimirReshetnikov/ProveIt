# Explicit existential relations on shared natural registers

`NaturalRegisterRelation.lean` hides an explicit auxiliary input block after a
shared arithmetic circuit has been supplied. Its `Relation n P` stores the
auxiliary count, natural-register program, selected equality outputs, and a
checked biconditional between `P` and existence of those auxiliary inputs.
The record supplies all program data directly; it does not recover data from
an existential proposition.

`Relation.compile` turns this data into `Rep (Fin n) P`. A circuit with `m`
registers and `k` auxiliary inputs produces exactly `k+m` natural witnesses,
a polynomial of degree at most four, and an expression with at most `6m+4`
binary operations. Hiding inputs and renaming coordinates preserve the
quartic degree and operation bound.

`RegisterRelationLogic.lean` supplies nonnegative arithmetic identities for
conjunction and disjunction of output equalities. For natural `a,b,c,d`,

```
a*a+b*b+(c*c+d*d) = 2*(a*b+c*d)  iff  a=b and c=d;
a*c+b*d = a*d+b*c                iff  a=b or c=d.
```

These are universal algebraic theorems. The first is the sum of two squared
differences, and the second is the product of two differences, interpreted in
the integers. The circuit data require only natural addition and
multiplication.

## The direct annotated checker's pairing

`RegisterNatPairing.lean` implements **Mathlib `Nat.pair` and `Nat.unpair`**, the
max-square pairing used by the direct annotated proof and rename checkers.
It keeps both cases of the exact definition:

```
a < b:  pair a b = b*b+a;
b ≤ a:  pair a b = a*a+a+b.
```

A single natural slack certifies the chosen inequality. Each branch conjoins
its slack equation and value equation; the two branch certificates are then
disjoined using the identities above. `exists_certificate_iff` proves the
resulting unbounded certificate equivalent to `z=Nat.pair a b`. Both inverse
projections add the missing component as another natural witness, then use
`Nat.pair_unpair` and `Nat.unpair_pair` to establish their exact graphs for
every natural encoded input, including zero.

The supplied circuit has 39 shared registers. Each projection's compiled
quartic graph has exactly 41 natural witnesses and at most 238 binary
operations. Its selected output values reuse earlier registers, including the
encoded value's square shared by both branches. The universal theorems
`direct_left_correct` and `direct_right_correct` in
`checks/RegisterRelations.lean` audit the actual `Nat.unpair` graph predicates.
No finite sample test or supplied checker-equivalence theorem stands in for
these proofs.

## The older enumerator's separate pairing

`RegisterCantorPairing.lean` covers **EnumPerm `P` and `unP`**, the older
refutation enumerator's Cantor encoding. This is a distinct encoding from
Mathlib's max-square pairing. Its circuit shares the sum of the two components
and checks the denominator-cleared identity

```
2*z = (a+b)*(a+b+1)+2*b.
```

The two projection graphs have ten registers plus one auxiliary missing
component: eleven natural witnesses, degree at most four, and at most 64
binary operations each. These graphs serve the older enumerator and are not
claimed to parse the annotated checker's tree codes.

## Verification and scope

All four source modules and `checks/RegisterRelations.lean` compile cleanly.
The nineteen audits use only `propext`, `Classical.choice`, and `Quot.sound`,
sometimes a subset. No new axiom or admitted lemma is used. The program data
and syntax constructors are executable; ordinary `MvPolynomial` semantics
retain Mathlib's noncomputable algebraic interface.

The local quartics are not claimed smaller than the existing specialized
higher-degree pairing graphs. Their purpose is to certify data-valued
existential scopes and concrete checker arithmetic before expression
inlining. A shared compiler for the full proof checker still needs relational
composition, guarded arithmetic and its iteration/bounded-quantifier layer.
These modules introduce no smaller closed consistency equation and do not
prove the missing internal object-ZFC consistency biconditional.

The later [direct quadratic attachment](QUADRATIC_REGISTER_SYSTEM.md) proves
the same unpair graphs with four auxiliary witnesses and46 operations,
retaining degree at most four. The output-equality circuits here remain
checked baselines.
