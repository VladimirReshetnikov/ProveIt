# Formalization status and path

## Status

`Arithmetic.lean` contains proposed complete Lean proofs of the numerical
classification, conditional on the incidence equations and Euler identity.
It contains no proof holes and no additional axioms. It has **not been
compiled**: Lean, Lake and Elan were unavailable in the production environment.
It must therefore be treated as source-reviewed implementation material,
not as a kernel-checked result. `ConciseBridge.lean` is a short, likewise
uncompiled, integration adapter.

Neither file is a completed internal iPRA proof of the geometric classification.
`Arithmetic.lean` proves an ambient Lean theorem about integers. In particular,
an ambient `Nat` theorem, use of constructive tactics, or acceptance of finite
Python certificates does not establish an object-level `Prf PRAAx` theorem.

## Verified repository interface

All repository observations below are pinned to commit
`2811f73af20330d04bf3dae8428f87f7efa6580d` of
`VladimirReshetnikov/ProveIt`.

* `lean-toolchain` specifies `leanprover/lean4:v4.32.0`.
* The root `lakefile.toml` requires Mathlib `v4.32.0`, declares library
  `ConciseIPRA`, and gives source directory
  `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`.
* `ConciseIPRA/PR.lean` defines `PR k` using zero, successor, projection,
  composition and primitive recursion. `PTm n` is its term language.
  `PRAAx` consists of the defining equations, successor nonzero and
  injectivity, and induction for quantifier-free formulas.
* `ConciseIPRA/Deduction.lean` defines
  `Prf (Ax : Theory T) : List (Fm T n) -> Fm T n -> Prop`, a deeply embedded
  intuitionistic natural-deduction derivability relation. It includes
  conjunction, disjunction, implication, universal and existential rules,
  equality and falsity elimination; it has no excluded-middle rule.
* `PRA.qfInd` is the existing quantifier-free induction constructor for use
  in derived arithmetic libraries.
* `ConciseIPRA/NativeBiInterpretation.lean` defines `NFm.ofPRA` and proves
  `pra_iff_native`, transporting any completed `Prf PRAAx` derivation to
  the native scalar calculus.
* `ConciseIPRA/BiInterpretation.lean` supplies `biInterp`, `pra_iff_teq` and
  `teq_iff_pra` for the intermediate ordinary scalar theory.

The large README and the above source files were actually read. The
`docs/drafts` directory was inspected, but none of its binary draft archives
is used as a proved mathematical dependency. The package should not claim
that these drafts have been verified.

## Stage 1: run the arithmetic prototype

In this directory, with Lean and Lake installed:

```sh
lake update
lake exe cache get
lake build Arithmetic
```

The candidate source proves

* `allowed_of_inequality`: integer `p,q >= 3` and `pq < 2p+2q` imply
  one of the five ordered pairs;
* `arithmetic_classification`: the inequality follows from
  `pF = 2E = qV`, `V+F = E+2`, and `E > 0`;
* `counts_classification`: the five complete `(p,q,V,E,F)` rows;
* length five and nonduplication of the explicit candidate list.

Inspect the `#print axioms` output. This is an audit of Lean's ambient theorem
dependencies, separate from the iPRA derivability audit below.

## Stage 2: natural-number coding

Use one explicit primitive-recursive pairing and bounded-access list coding.
For example, `pair(a,b) = 2^a(2b+1)-1` has decoding by search bounded by the
input code. Encode a finite list by zero for empty and `pair(head,tail)+1`
for cons. Prove each coding operation's defining properties by
quantifier-free induction. A polynomial or more compact pairing is equally
acceptable; choose one and fix its exact equations.

Integers are signed magnitudes with canonical zero. Rationals are pairs
of such integers and positive denominators. Equality and order are tested
by cross multiplication. The input coordinate domain is a finite
constructible ordered-field tower: at stage j adjoin a specified
nonnegative square root of a nonnegative element of the preceding stage.
Represent an element at this stage by `a+b*s`, where `s*s=r`. The extension
may be redundant; therefore do not assume coefficientwise equality.

Signs are computed recursively: first handle `r=0`, `a=0`, `b=0` and
the same-sign cases; in the opposite-sign case compare `a*a` and
`b*b*r` in the preceding stage. Equality is sign zero. For inversion,
use `(a-b*s)/(a*a-b*b*r)` when the norm is nonzero; if the norm is zero
but the element is nonzero, its conjugate is zero and the element equals
`2*a`, so use `1/(2*a)`. Default to zero on inversion of zero.
Prove these assertions by finite ordered-ring calculations and recursively
reduce them to the preceding stage. The data structure and a majorant
for intermediate code sizes must be fixed when converting this recursion
to PR definitions. Depth-bounded structural operations and their explicit
size recurrences supply such primitive-recursive majorants.

The canonical examples use the simpler subfield `Q(phi)`, represented by
pairs `a+b phi` with `phi^2=phi+1`. Invalid tower codes are assigned fixed
default values, making every operation total. The exact models and input
validator require no arbitrary real-number oracle.

Encode finite face cycles, vertex tables, edge lists and all accompanying
certificates as lists. A bounded universal assertion is represented by a
primitive-recursive Boolean fold. Its invariant is an equation `b=1`,
so quantifier-free induction suffices. A bounded existential search returns
an explicit least index or a failure sentinel; no unbounded search is used.

This is a fixed set of PR definitions. Do not introduce a purported total
primitive-recursive universal evaluator for all primitive-recursive programs.

## Stage 3: fixed certificate validators and their internal correctness

Port the finite algebraic verifier to PR definitions. Separate:

1. well-formed tables and denominator/nondegeneracy checks;
2. exact supporting-plane signs and face incidence;
3. regularity of each face, a common face size and common valence;
4. the finite combinatorial/geometric certificate used to prove the
   Euler identity and uniqueness;
5. the five explicit model tables and their successful validations.

Each validator is a terminating bounded loop over explicitly coded lists.
The internal proof must establish its intended meaning using invariants;
an external execution of a Python checker is evidence for certificate
values, not an internal soundness theorem.

If the chosen representation includes a sphere, shelling, or projection
certificate, prove its construction from the stated convex-input hypotheses.
Do not silently define a 'Platonic solid' as an arbitrary object already
satisfying the conclusion. The geometry in the article determines the
exact certificate and its correctness lemmas.

## Stage 4: internal arithmetic derivation

Avoid integer subtraction in the object theory by writing `p=a+2`, `q=b+2`,
where `a,b >= 1`. From the incidence equations and `V+F=E+2`, derive the
natural-number identity

    E*a*b + 2*p*q = 4*E.

Since `E,p,q` are positive, cancellation gives `a*b < 4`. Decidable
arithmetic case distinction gives precisely

    (a,b) = (1,1), (2,1), (1,2), (3,1), (1,3).

Addition and multiplication identities, cancellation, and order trichotomy
for the fixed coded naturals all have quantifier-free induction proofs.
The final five-way disjunction is constructed using `Prf.orI₁` and
`Prf.orI₂` and eliminated using `Prf.orE`; it is not obtained by applying
ambient Lean `omega` directly to an object-language goal.

## Stage 5: uniqueness and exact witnesses

Port the article's uniqueness proof, not merely the Schlaefli-pair bound.
The target is a returned correspondence with one of the five models.
Use a coded vertex permutation plus a similarity certificate when needed.
It is convenient to encode a similarity as `x |-> A x + b` with
`A^T A = lambda I`, `lambda > 0`; this avoids requiring a separate
square root of the scale factor. Recover `A,b` from four affinely
independent vertices by a fixed 3-by-3 inverse calculation.

A finite incidence certificate does not by itself prove geometric
uniqueness. Every geometric lemma used in reconstruction or rigidity must
have a finite algebraic proof and appear among the internal obligations.

## Stage 6: final object-language statement

Let the fixed PR symbols `Valid`, `Class`, `Model`, and `Match` implement the
representation, the five-way classifier, the canonical models, and the
finite isomorphism/similarity certificates. Construct a closed formula
`classificationFormula : Fm PTm 0` expressing

    for every c, Valid(c)=1 implies
      Class(c)<5 and Match(c,Model(Class(c)))=1,

as well as `Valid(Model(i))=1` for each of the five numeral indices and
pairwise non-equivalence of the models. `Match` can validate the explicitly
returned certificate, so a total PR witness function is preferable to an
unbounded existential statement.

The main formal endpoint is a term of

    Prf PRAAx [] classificationFormula.

Use `pra_iff_native` to produce

    NPrf [] (NFm.ofPRA classificationFormula).

`ConciseBridge.lean` records this final transport exactly. It does not
supply the missing premise. A theorem about arbitrary real-coordinate
polyhedra must additionally state its constructive representation and the
bridge to finite arithmetic codes; finite radical towers should not be
silently advertised as quantification over all set-theoretic reals.
The article's arbitrary-real classical corollary and its internally coded
constructive theorem should remain explicitly distinguished.

## Integration

The arithmetic prototype is standalone. `ConciseBridge.lean` belongs in a
ProveIt checkout with the existing `ConciseIPRA` library available, and is
not part of the standalone Lake target. After adding the full project,
build its target and inspect the final theorem's axioms. Record a successful
build log and the repository commit in the delivered archive. Until that
happens, retain the present uncompiled-source and incomplete-object-proof
status statements.
