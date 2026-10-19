# Replacing commutation by two-coordinate B6 collapse

## Concrete source rewrite

Retain **all** original rows, rules, formula tags, theory formulas and gates,
except replace rho4(a,b,c) by the numerical instance of

  DB(a,b,C): (exists a exists b forall a forall b C) -> C.

Existentials use the original relative-falsity abbreviation. In the source
builder's exact AST notation:

  Imp(Ex('a', Ex('b', All('a', All('b', 'c')))), 'c').

The original commutation row is

  Imp(All('a', All('b', 'c')), All('b', All('a', 'c'))).

Their exact emitted leaf/constructor words both have length 11:

  old: [a,b,c,all,all,b,a,c,all,all,imp]
  new: [a,b,a,b,c,all,all,exists,exists,c,imp].

The new row may share different subwords with retained rho6,
`[a,a,b,all,exists,b,imp]`. This is a concrete grammar/state-cost experiment,
not a claim that equal macro count guarantees a smaller machine. The full
logic is provably preserved as follows; no fresh-variable condition or
additional ex-falso row is needed.

## Exact interderivation

Write Q_i A for forall i A and D_i A for exists i A. Let N A denote A -> F.
Retained rho8 gives the ordinary implicational tautologies, including K, S
and Peirce. Retained rho6 is

  B6_i(A): D_i Q_i A -> A.

It also gives ex falso, exactly as in the existing native calculus: K yields
F -> (Q_i N Q_i A -> F), whose consequent is D_i Q_i A, and composing with
B6_i(A) gives F -> A. Thus all ordinary classical propositional manipulations
below are available with the literal relative F, including double-negation
elimination. This is why the rewrite does not incur the EFQ row needed by
the previously tested bare dual-rho6 replacement.

Retained QI plus GEN gives Q-monotonicity: if A -> B is a theorem, so is
Q_i A -> Q_i B. Contraposition then gives D-monotonicity. The same applies to
compositions of these operators. These facts require no commutation axiom.

### New DB derives the old commutation row

1. Contrapose B6_i(N A) and simplify double negations. This gives the familiar
   B form, for every i and A:

     A -> Q_i D_i A.

2. Fix a,b,A and write C=D_b D_a A. Two B instances are

     A -> Q_a D_a A,
     D_a A -> Q_b D_b D_a A = Q_b C.

   Lift the second under Q_a, then compose:

     A -> Q_a Q_b C.

3. Lift that implication under D_a D_b:

     D_a D_b A -> D_a D_b Q_a Q_b C.

4. Apply the new DB row at matrix C:

     D_a D_b Q_a Q_b C -> C = D_b D_a A.

   Hence D_a D_b A -> D_b D_a A.

5. In the preceding derivation swap a,b and substitute A=N P. Contraposition
   and double-negation elimination give

     Q_a Q_b P -> Q_b Q_a P,

   exactly the old rho4. Every invocation is an unrestricted numerical
   schema instance, so these substitutions are legitimate even when the
   code parameters coincide or the payload is the truth alias 0.

### The old commutation row derives new DB

Fix a,b,P. Apply old commutation inside the D_a D_b context:

  D_a D_b Q_a Q_b P -> D_a D_b Q_b Q_a P.

B6_b(Q_a P), lifted under D_a, gives

  D_a D_b Q_b Q_a P -> D_a Q_a P.

Finish with B6_a(P): D_a Q_a P -> P. Composing produces the exact DB row.

### Conclusion

The old and modified native numerical derivability predicates have the same
theorems: induct on a derivation, translating the only changed axiom by the
finite derivation above. Truth, MP, GEN, all equality rows, vacuity and the
set-theory bundle are unchanged. In particular their derivability of code 1
is equivalent in finitary arithmetic and hence in ZFC. The abstract command
compiler merely changes the fourth axiom leaf; its outer implication still
cannot equal 1, and all other proof enumeration arguments remain unchanged.
This route therefore targets exact Con(ZFC), not a stronger benchmark.

The argument is ordinary mathematics and is not yet a checked Lean proof or
a proof of a newly emitted binary table. The compiler workstream was sent the
exact AST and macro word for measured state costs. A source search found no
previous Double-B6 experiment in the pinned current ZFC reports; that is a
bounded repository search, not a claim of historical logical novelty.

## Diagnostic semantics

`double_b6_modal_check.py` independently checks all pairs of symmetric binary
accessibility relations on domains of size 1,2,3 and all truth assignments to
one propositional payload. Symmetry is exactly what the individual B6 law
requires for ordinary Kripke boxes. It confirms equivalence of the globally
valid old commutation row and DB, including non-reflexive frames. These finite
checks are supplementary; the schema interderivation above is the proof.

## First complete state-cost result (negative)

The compiler workstream tested 3,000 safe grammar candidates on the same
reviewed conjunction layout as the original 268-state control. Best DB result:
211 source decision nodes, maximum zero depth 7, and **273 working states**.
The matched original has 206 decision nodes, depth 7, and 268 working states.
The complete table, exact source DAG and emitted-edge re-extraction evidence
are in `../machine_encoding/double_b6/results.json` and its adjacent artifacts.
No state saving follows from this first fixed-layout family. Independent
parameter-role permutations and other layouts remain distinct possibilities;
the current proof is useful for checking them but does not predict their cost.
