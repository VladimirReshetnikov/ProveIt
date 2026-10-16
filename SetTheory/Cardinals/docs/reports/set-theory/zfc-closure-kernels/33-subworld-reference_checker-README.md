# K2+ reference refutation checker

This directory supplies an executable **reference** semidecision procedure for
the raw subworld kernel proposed in the accompanying report. It supplies no
Turing-machine transition table, state bound, machine compiler, or ZFC
formalization of the Python implementation. In particular, the test suite does
**not** exhibit a refutation of K2+.

The core is `k2_tableau.py`; it uses only the Python standard library. Run:

```sh
python -m unittest -v test_k2_tableau.py
```

`verification.json` records a real run, the Python version, and SHA-256 hashes.
`example_certificates.json` records the hand-written synthetic equality test.

## Exact input theory

The primitive language is `Bottom`, `Member(i,j)`, `Eq(i,j)`, `Imp(A,B)`, and
`All(i,A)`. Terms are variable names only. Equality is interpreted as identity;
Bottom is false. Domains are nonempty. The usual classical definitions of
negation, existential quantification, conjunction, and biconditional expand
into these primitives.

A matrix is any formula whose free variables are contained in `{0,1,2}`. These
are `a,b,z`, respectively; the other template names are `x=3`, `y=4`, and `W=5`.
Bound variable names are unrestricted. In particular, a matrix may bind name
5 internally. It may not have free name 5.

For a matrix `phi`, `kernel_components` constructs exactly:

```
Splus(phi) = exists y [y in W and
               (x in W -> forall z [
                 (z in y -> (z in x and phi)) and
                 (z in x -> (phi -> z in y))])]

REDcurried(phi) = a in W -> (b in W ->
                   (phi -> exists z [z in W and phi]))
```

`kernel_sentence(s, matrices)` constructs the **one** closed sentence

```
exists W [AND(phi in matrices)
  forall a b x z (Splus(phi) and REDcurried(phi))].
```

The empty conjunction is true, and a singleton conjunction is its sole member.
One World witness is shared by the entire pool. Every matrix has four literal
occurrences in its row after primitive expansion. Internal arena sharing is
merely a representation detail; it introduces no new logical connective or
axiom. The inner existential in `REDcurried` deliberately rebinds name `z`.
There is no syntax substitution operation hidden in the template.

With `extensionality=True`, the builder adds one conjunct
`forall a b ((forall z (z in a iff z in b)) -> a=b)` inside the same existential
World closure. The default is the raw theory without extensionality.

### Why finite pools use a shared existential

Let `T_W` be the recursively enumerable theory with a new constant `W` and all
the displayed universally closed matrix instances. A finite proof of a
contradiction uses a finite pool of these instances. Such a pool has a model
with its constant interpreted precisely when the corresponding constant-free
sentence `exists W AND(pool)` has a model. Consequently, first-order
completeness and the finite character of formal proofs give

```
T_W is inconsistent
  iff some finite-pool existential sentence has a closed tableau.
```

This also follows syntactically by the deduction theorem and the usual
fresh-constant/existential rules. The shared witness is essential to this
argument; giving each individual matrix its own existential World is a
different construction.

## Certificate format

An instruction is a natural number
`pair(rule, pair(index, parameter))`. Indices are zero based in the currently
active branch. Pending branches form a stack; a true implication checks its
negative-antecedent branch before its positive-consequent branch.

| Rule | Name | Required selected formula | Effect |
|---:|---|---|---|
| 0 | `CLOSE` | None; both arguments must be zero | Require an atomic clash or true Bottom; close this branch. |
| 1 | `T_IMP` | True `A -> B` | Remove it and split into false `A`, or true `B`. |
| 2 | `F_IMP` | False `A -> B` | Remove it and add true `A` and false `B`. |
| 3 | `T_ALL` | True `forall v A` | Retain it; add true `A` with `v` assigned the specified allocated parameter. |
| 4 | `F_ALL` | False `forall v A` | Remove it; allocate a fresh parameter ID and add false `A` with that assignment. |

Only `T_ALL` uses the parameter argument; all other parameter arguments must
be zero. Every branch initially has parameter 0, representing the nonempty
domain. Further IDs are allocated locally to the branch. Fresh IDs need not
denote distinct objects: positive equalities may identify them.

An entry contains a sign, a formula ID, and an environment from variable names
to parameter IDs. Quantifier steps extend a **copy** of the environment. Thus
shadowing a name, including name 5, cannot change the interpretation of a
sibling formula. Atomic closure first forms the equivalence relation generated
by all positive equality atoms. A negative equality inside one equivalence
class closes the branch. Membership atoms close it if a positive and negative
pair coincide after quotienting both coordinates. True Bottom also closes it.

The checker rejects a wrong rule, bad index, unavailable parameter, malformed
matrix, premature closure, unfinished branch, or trailing instruction after
all branches have closed. A certificate cannot supply a false-quantifier
witness ID; the checker allocates it itself.

## Natural coding and termination

Let `P(x,y)=(x+y)(x+y+1)/2+y` be Cantor pairing. Formula codes are the bijection

```
Bottom       = 0
Member(i,j)  = 1 + P(0, P(i,j))
Eq(i,j)      = 1 + P(1, P(i,j))
Imp(A,B)     = 1 + P(2, P(code(A),code(B)))
All(i,A)     = 1 + P(i+3, code(A)).
```

For a positive code, unpairing `n-1` distinguishes the constructors. Every
recursive formula child is strictly smaller than `n`. Lists use `0` for nil
and `1+P(head,tail)` for cons, again with strictly smaller recursive children.
Candidate 0 is reserved and rejected; a positive candidate is

```
1 + P(code_list(matrix_formula_codes), code_list(certificate_instructions)).
```

`check_code(n, extensionality=False)` therefore terminates for every natural
input in the mathematical, unbounded-resource interpretation. Formula decoding,
free-variable computation, formula encoding, and certificate checking avoid
Python recursion. `first_refutation()` tests candidates `0,1,2,...` in order.
Every finite pool and finite certificate occurs, so no search branch is lost.

Cantor coding is intentionally simple and extremely inefficient. Deep syntax
and long lists can require enormous integers; it is a specification device,
not a compression result. Real host resource failures, including `MemoryError`,
are allowed to abort a run and are never caught as a logical rejection. A
resource-aborted enumeration is not a completed semidecision run. Adding a
timeout and skipping unfinished candidates would invalidate the fairness
argument. The production code catches only its dedicated `InvalidMatrix`
exception.

## Correctness argument

**Soundness.** Interpret a branch by an arbitrary assignment to its allocated
parameters. The signed implication rules preserve satisfiability in at least
one child branch. A true universal permits every allocated parameter as an
instance. A false universal permits extension of the assignment by a witness
for its fresh ID. A closed branch has no satisfying interpretation, because
identity equality respects both arguments of membership and Bottom is false.
Induction backward through a finite accepted certificate therefore proves that
its closed root sentence has no model.

**Completeness.** These are the usual full signed tableau rules for classical
first-order logic with identity equality and a function-free relational
language. Expand both implication branches, introduce witnesses for negative
universals, and fairly instantiate each retained positive universal at every
parameter that appears on its branch. If no finite closed tableau exists,
the finitely branching construction has an open fair branch. Quotient its
parameters by the equivalence relation generated by positive equalities.
The atomic clash test makes its signed membership assignments consistent on
the quotient and respects every negative equality. A truth induction on
formulas, using the retained universals and witness entries, gives a model.
Contraposition gives a finite closed tableau for every unsatisfiable sentence.
Its depth-first traversal has exactly the certificate format above.

Combining this result with finite pools and their shared existential closure
gives, in ordinary mathematics,

```
first_refutation() halts iff raw K2+ is inconsistent.
```

The report separately addresses the consistency calibration of K2+ and the
stronger requirement that a *literal compiled machine* satisfy the desired
equivalence in ZFC. Neither endpoint is inferred merely from these tests or
from the existence of this Python implementation.

## What was actually tested

The suite has seven test groups. It checks 5,000 natural formula, list, and
Cantor round trips; all 2,580 listed template equivalence comparisons over
every one- and two-element membership structure for five representative
matrices; binding and shadowing of variable name 5; four matrix occurrences;
the free-variable guard; equality congruence in both membership arguments;
positive-universal retention and new parameter instantiation; and malformed
or incomplete certificates. One satisfiable two-element sentence rejects a
purported refutation that would become possible if witness IDs were reused.
A 3,000-universal example exercises the iterative checker beyond the ordinary
Python recursion depth.

The finite comparisons check `Splus(phi) <-> (inhabited(W) and SS(phi))` and
`forall z REDcurried(phi) <-> RED(phi)` with the original existential RED.
Their small finite scope is explicit: they are regression evidence, not a
proof of the general equivalences or of equiconsistency. Accepted equality
certificates assert the synthetic contradiction
`exists a b z (a=b and (a in z and not(b in z)))`, or its other-argument variant.
The same certificate is rejected when its essential equality is weakened to
`a=a`; exhaustive two-element semantics independently finds a model then.
