# EPSC2: a complete certificate path with fixed environment projections

Research note, 16 October 2026. The logical rules are standard signed tableaux.
The new implementation contribution is their integration with the fixed
two-parameter empty-seed kernel: the entire axiom path has no named-variable
substitution, alpha conversion, or matrix duplication. The scope of every
claim below is the abstract certificate checker, not a literal Turing table.

## 1. Source audit and the obstruction that must be addressed

The current pinned source is ProveIt commit
`af518abcf8ca2a7c1b795c07973885041aee0d25`. Its commit
`e7c4cadf9b180e4b1801755b09777a7572412360` correctly distinguishes two
252-state experiments. The PSC-only experiment has genuine Bottom but its
reduced logic admits the constant-true universal operator; the frozen C/G
experiment uses a different existential bundle, which that particular
algebra does not satisfy. The source therefore does not itself conclude
that the old C/G candidate is nonrefuting.

The newer incoming archive `zfc_consistency_machine_research.zip`, however,
contains a stronger argument in `sections/countermodel.tex`. I independently
checked its full mathematical case split against the emitted formulas:

* Domains are D_i=[0,d_i), d_0=2, d_(i+1)=d_i+2^(d_i).
* Same-sort membership is false. Object 1 is universally inhabited by every
  different sort; object 0 is empty. A higher sort represents every subset
  of each lower sort by a designated block of binary masks.
* The container row is true by universal objects when a,b,c are distinct.
  When a=b, the literal diagonal guard is false; the remaining root member
  is supplied by the outer universal object.
* For collection, a=b uses the empty output. If b<c, use a finite exact
  representative of the guarded output range. If b>c, the matrix with code
  c cannot mention b or c, so an empty or universal output suffices.
* The gate excludes b=c. Both original and dual rho6 are valid. The
  distinguished formula R(0,0) stays false under all variable updates.
* The code-zero truth alias is handled compositionally: I(0,0)=0, and
  true implies true is true. All other decoded children are strictly smaller
  than their parent code.

Thus the incoming finite-sort theorem covers the entire emitted raw C/G
calculus, not only its isolated logical fragment. It is a prior result, not
a new result of this note. Given a faithful simulation theorem, it proves
nonhalting in ZFC itself, excluding the required equivalence under Con(ZFC).
Its application to an actual table still depends on the compiler bridge.

Adding same-variable specialization alone cannot restore completeness.
Already the simpler algebra in the previous incoming proposal interprets
every Q_i as identity and independent membership strings as independent
Boolean variables. It validates the retained rows, atomic vacuity, and
Q_i A -> A, but can refute (forall x R(x,z)) -> R(y,z). The actual repair
must transport variables across binders and atomic argument positions.

Repository source URLs:

* https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/psc_backend_experiment.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/dual_quantifier_gap.md
* https://github.com/VladimirReshetnikov/ProveIt/blob/af518abcf8ca2a7c1b795c07973885041aee0d25/Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.md

## 2. The exact two-parameter schema compiled here

Let epsilon(x) mean forall z not(z in x), and let y subset b abbreviate
forall z(z in y -> z in b). EPSC2 consists of the sentences

    forall p forall q (
      [forall x exists b forall y (rho(x,y;p,q) -> y subset b)]
      -> exists C (
        [forall x ((epsilon(x) or x in C)
                    -> forall y (rho(x,y;p,q) -> y in C))]
        and [forall y (y in C -> exists x rho(x,y;p,q))])).

This is the curried form of the theory agent's EPSC2 axiom. The two forms
are classically equivalent because the guard does not depend on y. Input
matrices have only free slots x,y,p,q, but may have arbitrary bound variables,
arbitrary nesting, and negation. Either or both ordinary parameter slots may
be unused. No seed parameter or logical equality is present.

The separate theory argument claims ZFC proves Con(EPSC2) iff Con(ZFC).
The checker theorem below is independent of that strength claim; it searches
exactly the displayed recursively enumerable theory in complete ordinary
equality-free logic with primitive false and nonempty domains.

## 3. Matrix syntax and the complete absence of named substitution

Use the grammar

    A ::= Bottom | R(i,j) | Imp(A,A) | All(A).

An open matrix is checked at depth 4. At a subformula beneath d internal
binders, each atom index is less than d+4. Indices 0,...,d-1 refer to those
binders. Indices d,d+1,d+2,d+3 refer to x,y,p,q. This is not a restriction
on the number of bound variables. It is the ordinary de Bruijn encoding of
formulas with four distinguished free slots.

A formula occurrence is stored with an environment eta of parameter names.
R(i,j) denotes R(eta_i,eta_j). Universal instantiation prepends one name.
All syntactic variable transport is performed by environment lookup. Distinct
names and distinct slots may denote the same domain element; no disequality
assumption is introduced.

The fixed EPSC2 wrapper has three matrix markers. Each occurs at depth 5.
The complete projection table is:

| Occurrence | Wrapper environment, innermost first | Matrix environment |
|---|---|---|
| Local subset bound | [y,b,x,q,p] | [eta_2,eta_0,eta_4,eta_3] |
| Recurrent closure | [y,x,C,q,p] | [eta_1,eta_0,eta_4,eta_3] |
| Global support | [x,y,C,q,p] | [eta_0,eta_1,eta_4,eta_3] |

Each marker evaluates the same matrix pointer under the four indicated
entries. No renamed copy of the matrix is constructed. Internal matrix
binders prepend names to this projected environment and cannot capture a
free slot accidentally. Parameters p,q retain the same values at all three
occurrences. In particular, the runtime performs no free-variable collection,
fresh wrapper-name search, textual substitution, alpha comparison, or matrix
expansion. It does still parse and scope-check the matrix.

After expanding Not, Exists, And and Or into Imp/Bottom/All, the template has
49 tree nodes, including the three matrix markers. It has 36 distinct nodes.
These are expression counts, not Turing-machine states. The Python structure
shares the template and stores each selected matrix once; a compiled program
must implement and charge that sharing explicitly.

## 4. Projection theorem and proof preservation

Let phi be scoped over r outer slots, and let sigma map [0,r) into [0,s).
It need not be injective. Define lift_sigma(phi) recursively. At binder
depth d, replace atomic index i by

    i                         if i < d,
    d + sigma(i-d)            otherwise.

Implication preserves d and All increments d. For every environment eta
of length s and every ordinary relational interpretation,

    eval(lift_sigma(phi), eta) = eval(phi, eta composed with sigma).

Proof: structural induction on phi. The atomic case is lookup. The Boolean
case follows by induction. In the universal case the newly prepended element
has index zero on both sides; all other indices are shifted uniformly. This
proves the identity for every matrix, every assignment, and every bound depth.

Expand each template marker using this lift. The result is the ordinary
fully written, closed EPSC2 axiom. The table in section 3 gives its exact
capture-avoiding meaning. Virtual and expanded closures have the same exposed
constructor; corresponding children satisfy the same projection identity.
Their atom lookups yield exactly the same ordered parameter pair.

Consequently every finite tableau certificate has exactly the same acceptance
result with virtual template roots as with their expanded ordinary roots.
No proof step is added by exposing a marker, and branch indices are unchanged.
This is a proof-preserving compilation of the axiom representation, rather
than just an equivalence of isolated truth values. The general claim is an
ordinary inductive mathematical proof. The included tests check 145 pairs of
the same certificate in both representations; there is no Lean theorem about
the Python implementation yet.

## 5. Six complete signed-tableau productions

Entries remain available after use. The checker accepts these productions:

| Selected entry | Required continuation |
|---|---|
| T(A -> B) | Two closed children, adding F A and T B respectively |
| F(A -> B) | One child adding T A and F B |
| T All(A) | One child adding T A with a selected parameter prepended |
| F All(A) | One child adding F A with a fresh parameter prepended |
| Opposite signed atoms | Close iff their evaluated ordered pairs coincide |
| T Bottom | Close |

Bottom is a primitive false constructor. F Bottom never closes. Atomic
closure compares interpreted parameter pairs, not source indices or labels.
This supplies exactly the variable transport that the stripped Hilbert rows
lacked. For example, the checker accepts a demonstration of the universal
closure of

    (forall v0 (v0 in v1)) -> (v2 in v1),

the ordinary logical theorem refuted by the full finite-sort countermodel.
It also accepts All(Bottom) -> Bottom, refuted by the constant-true quantifier
control. Neither demonstration is a refutation of EPSC2.

### One-counter parameter allocation

For sentence roots initialize m=1, reserving name 0 so the model domain is
nonempty. All names occurring on a branch are less than m. A positive
universal may select k<=m. If k<m it reuses an allocated name; if k=m it
introduces the next name and increments m. A negative universal must select
exactly m; the checker does this itself, then increments m. No used-name set
or maximum-name scan occurs during checking.

Every ordinary finite parameter tableau can be transformed into this form.
Traverse each branch while maintaining an injective renaming of the names
already introduced. The first occurrence of any previously unseen name is
renamed to m, then m increases. An old name uses its previous image. Eigenname
freshness guarantees the negative-universal case introduces a new name.
The two children of an implication may extend their common prefix renaming
independently, since there is no cross-branch identity condition. Atom closure
and all rules are preserved. Thus the counter restriction loses no refutations.

### Soundness

If a branch is satisfiable, a true implication has a satisfiable child; a
false implication forces both additions. Universal truth permits any chosen
parameter. A false universal has a witness that can be assigned to the fresh
name without changing prior entries. Closure leaves are unsatisfiable. An
induction over a finite accepted tree therefore excludes a model of its roots.
Section 4 identifies those roots with the actual EPSC2 axioms.

### Refutation completeness

If EPSC2 is inconsistent, finitely many of its instances are unsatisfiable.
Classical first-order parameter tableaux are complete for this grammar. A
direct proof fairly adds every applicable Boolean decomposition, witnesses
each false universal, and instantiates each true universal at every parameter
eventually introduced. An infinite saturated open branch gives a model with
parameter names as its nonempty domain; positive atoms define the relation.
The truth lemma follows by formula induction. Thus an unsatisfiable finite
root set has a finite closed tableau. The allocation normalization above
puts it in exactly the checker's certificate format, and the projection
theorem replaces its ordinary roots by the virtual roots.

The standard completeness theorem is being applied to full equality-free
first-order logic. It is not applied to the repository's stripped code
calculus or to an unproved deletion from a Hilbert presentation.

## 6. Fair enumeration and the exact abstract endpoint

Let P be Cantor pairing. The matrix encoding is

    e(Bottom) = 0,
    e(R(i,j)) = 1 + 3 P(i,j),
    e(Imp(A,B)) = 2 + 3 P(e(A),e(B)),
    e(All(A)) = 3 + 3 e(A).

Every natural decodes to a finite raw matrix. Scope checking determines
eligibility. The decoder is total because each recursive formula child is
strictly smaller than its positive parent. The encoder is inverse to the
decoder on all primitive raw formulas. All valid four-slot matrices occur.

Lists use nil=0 and cons(h,t)=1+P(h,t). Proof nodes use residues modulo six
for the six productions, with paired branch references, child codes, and
positive-universal parameters. Recursive proof subcodes are at most floor(n/6)
and strictly smaller than n. The complete certificate pairs a matrix-list code
with a proof code. Both directions are implemented in the reference.

For each n=0,1,2,..., decode the certificate and run the total finite checker.
Halt exactly on acceptance. A malformed syntax, invalid scope, or invalid
proof is rejected. A resource failure in the host Python runtime is not a
mathematical rejection and never an accepted contradiction. The abstract
program has unbounded finite storage; each candidate terminates.

With Con(EPSC2) defined using a standard complete ordinary calculus,

    ZFC proves: search halts iff not Con(EPSC2).

Composing with the separate EPSC2 calibration gives the requested abstract
nonhalting/Con(ZFC) equivalence. The additional endpoint needed for a state
bound is a literal binary blank-tape table and a proof of its exact simulation
of this search. None is supplied or claimed by this contribution.

The numeric coding is selected for an uncomplicated completeness proof and
potential reuse of existing pairing routines. Cantor codes of long nested
proofs can have enormous bit lengths. Demonstration certificates are kept as
ordinary trees; the test suite never constructs astronomical integers merely
to encode the long schema-identity demonstrations.

## 7. Comparison of complete repair routes

| Route | Benefit | Cost that must still be charged |
|---|---|---|
| Retain the original complete equality-bearing calculus | Existing soundness/completeness bridge is reusable under its exact hypotheses | Equality rows and coding; changed theory still requires translation |
| Standard K/S/C/UI/UD Hilbert checker | Familiar complete finite schema basis; simple proof list | Capture-safe arbitrary specialization and quantifier side conditions |
| EPSC2 environment tableaux, supplied here | Fixed axiom template, genuine false, no equality logic or substitution routine | Branch storage, environment lookup/projection, scoped matrix parsing, witness counter |
| Ground Herbrand/propositional refutations | Small propositional terminal checker; no unification needed if candidates are enumerated | Prenex/Skolem transformation, function-symbol dependencies, term syntax, all ground-instance checks |

Herbrand certificates are eligible because proof-search speed is secondary.
They do not eliminate the front end for arbitrary quantified matrices. Its
exact transformations must be included in the small program or independently
checked in a certificate. No source-length or formula-node comparison settles
which complete route produces the smallest binary table.

## 8. Evidence and provenance

Run:

    python checker/test_epsc2_tableau.py

The current evidence is:

* 145 four-slot matrices, including nested binders and negative formulas.
* 2,610 comparisons with both independent expansion and the direct EPSC2
  semantic definition on all one- and two-element relations.
* 69,600 direct matrix-projection comparisons under varying environments.
* 145 identical finite certificates accepted with virtual and expanded roots.
* 11 deliberately invalid inputs rejected, including fifth parameters, false
  Bottom closure, eigenname override, invalid atom closure, and target injection.
* 10,000 matrix-code round trips and 10,000 proof-code round trips.
* 2,000 finite enumeration controls; no public refutation was found.

These are finite regression checks, not proofs of global consistency, formal
soundness, or a machine-state bound. The general logical arguments are above.
The standard tableau/environment idea is already present in the incoming
`zfc_consistency_proposal` archive and is not claimed as new. The delta is
the exact EPSC2 parameter restriction, the fixed projection compiler, and the
one-counter certificate discipline with their preservation arguments.

Primary background sources:

* N. G. de Bruijn, "Lambda calculus notation with nameless dummies, a tool for
  automatic formula manipulation, with application to the Church-Rosser
  theorem," Indagationes Mathematicae (Proceedings) 75 (1972), 381--392.
  https://research.tue.nl/en/publications/lambda-calculus-notation-with-nameless-dummies-a-tool-for-automat/
  Author-institution full text: https://pure.tue.nl/ws/portalfiles/portal/4304839/597619.pdf
* Melvin Fitting, First-Order Logic and Automated Theorem Proving, 2nd ed.,
  Springer, 1996. The sections on first-order tableaux provide the standard
  background for the completeness argument reproduced above.
  https://link.springer.com/book/10.1007/978-1-4612-2360-3

