# Logical bases and the next compression step

Research note for the requested ProveIt report, 16 October 2026.

## Scope and source pins

This note was checked against ProveIt commit
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7` and Jeffrey Ketchersid's
`jeff87654/busy-beaver` commit
`297ab8df7e5de329605c3875b4934643b371a5e3`.
The relevant public source files are:

* [ProveIt TarskiCalculus.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiCalculus.lean).
* [ProveIt TarskiComplete.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiComplete.lean).
* [Public CD254.v](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/CD254.v).
* [Public Comp_Prop254.v](https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/Comp_Prop254.v).

The equality-free PSC interpretation is already a repository result. In
particular, the monochromatic decoder and hereditary-saturation/purity-cut
arguments in the accepted source08 and source13 reports must not be
presented as discoveries of the present report. The new finite obstruction
below concerns a different proposed change: replacing the classical
propositional basis by K and S while hoping that rho6 restores classical
logic.

## 1. Exact status of the existing propositional interface

The named calculus has genuine bottom, implication, universal
quantification, membership and equality. Its classical row is

    L(p,q,r,s) = ((p -> q) -> r) -> ((r -> p) -> (s -> p)).

The pinned `TarskiComplete.completeness` theorem still takes arguments
`hC` and `hC0`, asserting the classical propositional properties of the
theorem predicate for the requested theory and for the empty theory. Its
header refers to `Lukasiewicz.lean`, but that file was absent at the stated
pin. Consequently a report should describe the completeness theorem as
conditional on these explicit basis hypotheses at that pin. The missing
mathematical derivations are elementary finite proof obligations, not a
new unproved mathematical conjecture: the public Coq source supplies them.

The attached `lukasiewicz_certificate.json` is a portable rendering of the
public mathematical derivation DAG. It has 107 schema rows, one L root and
106 modus-ponens rows. Its targets are K at row 16, identity at 17, Peirce
at 25, composition B at 91 and S at 106. `verify_basis.py` independently
checks every substitution and every modus-ponens edge by exact syntax-tree
equality. Six deliberate corruptions were rejected. This is an independent
replay of attributed public proof data, not a claim to have discovered the
Lukasiewicz theorem or the public proof.

The files `LukasiewiczCertificate.lean` and `TarskiClosedBasis.lean` give
explicit proposed adapters. They were generated against the stated source
interfaces but were **not compiled** in this environment, which had no
Lean executable. No theorem-checking claim is made for these files.

### Ex falso needs rho6 as well as implication

Pure L does not treat its designated formula F as falsity. K, S, B and
Peirce follow from L; the assertion F -> A requires additional information.
In this calculus it follows from rho6. Let

    E = exists i forall i A = (forall i ((forall i A) -> F)) -> F.

K gives F -> E, and rho6 gives E -> A. Composition B then gives F -> A.
This proof is not circular: it uses K and B before constructing the
`Classical` record, and never invokes a deduction theorem whose hypotheses
already include ex falso. In the genuine-bottom presentation F is bottom.
The source's relative-falsity numerical codec needs its own normalization
and theory bridge, as the public Coq development already records.

## 2. A six-element counterinterpretation: K and S do not suffice

### Theorem

Take the genuine-bottom named Tarski calculus with K and S in place of L,
retain all the other rows of the pinned calculus, including rho6,
quantified implication, commutation, equality existence, Euclidean
equality, both membership transports and atomic vacuity, and retain modus
ponens and generalization. In the empty nonlogical theory this calculus
does not derive every Peirce instance.

The theorem rules out a specific shortcut in the logical proof. It does
not by itself show that a particular extension by CP/GIC or PSC has the
wrong consistency strength.

### Algebra

Let X have three points 0,1,2, with 0 < 1 and point 2 incomparable with
both. Encode an upset by its three-bit incidence mask. The Heyting algebra
of upsets is

    H = {0,2,3,4,6,7},   bottom = 0,   top = 7.

Implication is

    a => b = {i in X : upward(i) intersect a is a subset of b},

where the principal upward sets have masks 3,2,4. The exact table, with
the column and row order 0,2,3,4,6,7, is:

| => | 0 | 2 | 3 | 4 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 7 | 7 | 7 | 7 | 7 | 7 |
| 2 | 4 | 7 | 7 | 4 | 7 | 7 |
| 3 | 4 | 6 | 7 | 4 | 6 | 7 |
| 4 | 3 | 3 | 3 | 7 | 7 | 7 |
| 6 | 0 | 3 | 3 | 4 | 7 | 7 |
| 7 | 0 | 2 | 3 | 4 | 6 | 7 |

Every universal quantifier, irrespective of its label, acts by the same
operation Q:

| a | 0 | 2 | 3 | 4 | 6 | 7 |
|---:|---:|---:|---:|---:|---:|---:|
| Q(a) | 0 | 0 | 2 | 4 | 4 | 7 |
| not a | 7 | 4 | 4 | 3 | 0 | 0 |
| not Q(not Q(a)) | 0 | 0 | 3 | 4 | 4 | 7 |

Give every equality atom the value 7 and every membership atom the value 4.
Give genuine bottom value 0. Extend recursively to all formula syntax with
the displayed implication and Q. The only designated value is 7.

### Verification

K and S are valid in every Heyting algebra; they can also be checked
directly over the displayed finite table. The table has
`a => b = 7` exactly when `a` is included in `b`, so modus ponens preserves
the designated value. Generalization preserves it because Q(7)=7.

The quantified-implication row is valid because

    Q(a => b) <= (Q(a) => Q(b))

for every pair a,b in H. All quantifier operations are identical, hence
their commutation row is valid. The last line of the second table is
pointwise below its first line, proving rho6 for every formula value.

Equality existence has value `not Q(not 7) = 7`. The equality and
membership transport rows are immediate from the constant atom values.
Both atom values 4 and 7 are Q-fixed, so even all the ungated atomic-vacuity
instances hold. This proves soundness of the entire modified logical
calculus for this algebra by induction over derivations.

Now put

    P = forall v0 (Rel(v0,v0) -> bottom).

Its value is Q(not 4)=Q(3)=2, whereas not-not P has value 3. Peirce at P and
bottom has value

    ((P -> bottom) -> P) -> P = 6 != 7.

It is therefore not derivable. Notice the precise mechanism: a fresh
quantifier fixes every atom, but its action on a negated atom need not fix
that formula. Assuming full vacuity from atomic vacuity while relying on
classical propositional manipulations is exactly the circular step this
example exposes.

`verify_ks_countermodel.py` performs all 420 declared finite checks and
produces `ks_countermodel.json`. The mathematical soundness argument is
the finite table calculation followed by structural induction on a
derivation. No automated search result is being substituted for that
argument.

### Limits of the counterinterpretation

This is an algebraic interpretation of the formal derivation system,
which is sufficient for a nonderivability proof. It is not an ordinary
first-order structure. It is not asserted to satisfy CP, GIC or PSC. It
also has `value(Rel(0,0))=4` and `value(bottom)=0`, so it does not identify
the numerical alias F=Rel(0,0) with genuine bottom. A proof about a concrete
aliased enumerator must check its exact normalization and theory axioms.
The valid conclusion is that the proposed pure logical completeness
shortcut fails. A different equiconsistency proof using an artificial
logic remains logically possible but would need new work.

## 3. A complete three-parameter alternative: K, B and Peirce

The correct candidate for deleting the fourth formula-parameter read is
to emit three complete schema rows:

    K(p,q)   = p -> (q -> p)
    B(p,q,r) = (p -> q) -> ((q -> r) -> (p -> r))
    P(p,q)   = ((p -> q) -> p) -> p.

Every row has at most three independent formula parameters. This is the
Tarski-Bernays basis, as stated in Section 2.1 of Frank Pfenning's primary
paper, [Single Axioms in the Implicational Propositional Calculus](https://www.cs.cmu.edu/~fp/papers/cade88.pdf)
(1988). A complete emitted schema family is required; fixing or correlating
parameters without proof is a different proposal.

For an explicit self-contained derivation, first obtain

    D(p,q,r) = ((p -> q) -> r) -> (q -> r)

by modus ponens from K(q,p) and B(q,p->q,r). Setting p=q=r=a and applying
Peirce with first parameter a->a and second parameter a gives a->a.

Next obtain

    E(p,q,r,s) = (((p -> q) -> (r -> q)) -> s) -> ((r -> p) -> s)

from B(r,p,q) and B(r->p,(p->q)->(r->q),s). Substitute

    p=a->b, q=b, r=a, s=a->b.

The antecedent becomes Peirce(a->b,b), and modus ponens gives contraction

    W(a,b) = (a -> (a -> b)) -> (a -> b).

Here is the admissible implication-combination rule. From theorems
`h -> (a -> b)` and `h -> a`, use B twice to derive, successively,

    (a -> b) -> (h -> b),
    ((a -> b) -> (h -> b)) -> (h -> (h -> b)),
    h -> (h -> b).

W(h,b) yields h->b. This is precisely the step needed to prove the
deduction theorem by induction on a derivation: use K for axiom/retained
hypothesis cases, identity for the discharged hypothesis, and the
displayed rule for modus ponens. Starting with hypotheses
`p->(q->r), p->q, p`, derive r and discharge those three hypotheses. The
result is the S schema. Thus KBP proves KSP and is classically complete.

The attached `kbp_closed_certificate.json` records an independently
constructed finite proof of this argument. Its three roots are K,B,P;
its 325 rows contain 322 exact modus-ponens steps, with S at row 324. The
certificate is not optimized for proof length. All substitutions and
steps were checked by `verify_kbp.py`, and invalid self-reference and a
false K root were rejected. The arithmetic size of this off-machine
correctness certificate has no direct effect on the number of machine
states.

The proof uses only substitution into displayed terms and modus ponens.
It imposes no injectivity condition on the implication constructor. As an
abstract proof algebra it therefore transports to numerical constructors
with aliases. This observation covers the propositional derivations only;
it does not prove that a changed proof enumerator emits exactly the
required roots, traverses all proofs, or simulates on the final tape.

Replacing L by KBP or KSP removes the need for a fourth independent
propositional parameter, but it adds emitted rows. The net compiler result
must be measured, including their output stack entries, all reads and
resets, selector layout, shared helpers, dispatcher depth and blank-tape
initialization. No state saving is claimed in this note.

## 4. Other single implication axioms

Toshihiko Sekimoto's primary paper, [On the Uniqueness of the Shortest
Single Axiom for the Implicational Calculus of Propositions](https://www.jstage.jst.go.jp/article/pjab1945/48/5/48_5_290/_pdf/-char/ja)
(Proceedings of the Japan Academy 48, 1972, 290--292), establishes that the
13-symbol L row is unique up to variable naming. Consequently arbitrary
bracket or antecedent rotations at that length cannot be treated as
alternative complete single bases.

Pfenning lists the longer complete single bases

    L4 = ((p -> q) -> (r -> s)) -> (t -> ((s -> p) -> (r -> p)))
    L5 = ((p -> q) -> (r -> s)) -> ((s -> p) -> (t -> (r -> p))).

They have 17 symbols and five independent variables. They could in
principle compile more compactly if their words share substantially more
code, but their fifth parameter has a real cost and the attached CD254
certificate proves consequences of L1, not L4 or L5. The shortest-formula
theorem is not a lower bound on machine states, and this distinction is
especially relevant to a grammar-sharing compiler.

## 5. Exact logical goal for any next machine

For the final blank-tape machine M and the explicitly coded recursively
enumerable theory T, one needs both internal directions

    ZFC proves: M halts <-> not Con(T),
    ZFC proves: Con(T) <-> Con(ZFC).

The nonhalting target then follows by classical propositional logic in
ZFC. An ordinary mathematical proof formalizable in ZFC is sufficient for
this specification; a serialized proof-code translator is a valuable
verification artifact but is not a separate mathematical requirement of
the user. Conversely a finite run or a proof in a richer metatheory does
not, by itself, establish this internal statement.

The theory-calibration proof must be uniform over coded formulas and
finite derivations. The accepted PSC proof has the right fixed
first-order interpretation and uniform syntactic shape. The remaining
task is to connect that comparison to the actual enumerator and binary
machine. For the public 253 baseline, the complete Lean bootstrap is a
finite-prefix result; subsequent arbitrary runtime simulation and the
internal consistency bridge are separate endpoints.

## Deliverable inventory

Ready to include:

* `verify_ks_countermodel.py`, `ks_countermodel.json`: new finite logical
  obstruction with exact scope and exhaustive checks.
* `lukasiewicz_certificate.json`, `verify_basis.py`,
  `basis_verification.json`: attributed public L proof, independently
  replayed.
* `kbp_closed_certificate.json`, `verify_kbp.py`,
  `kbp_verification.json`: independently constructed positive KBP-to-S
  proof, with exact replay.
* `LukasiewiczCertificate.lean`, `TarskiClosedBasis.lean`: proposed
  integration adapters, explicitly uncompiled.

The exploratory search programs and downloaded reference Coq source are
scratch intermediates. They need not be shipped as final artifacts unless
full generation provenance is desired. The three verifiers and their
certificate data are self-contained; `verify_kbp.py` imports
`verify_basis.py` from the same directory.
