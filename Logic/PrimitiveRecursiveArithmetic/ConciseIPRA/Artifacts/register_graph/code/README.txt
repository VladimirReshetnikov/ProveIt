COUNTER-AWARE REGISTER-ITERATOR ARITHMETIC: REFERENCE PROOF CHECKER
================================================================

This is a complete, readable standalone checker for closed theorems of the
ordinary first-order theory described below. It is not a small-source record
candidate. It does not import another checker, evaluate numerical programs,
invoke a theorem prover, or execute certificate text as code.

Run one proof certificate:

    python3 checker.py < certificates/functional_coverage.json

Expected output is exactly ACCEPT with exit status zero. Recognized invalid
syntax and inferences produce REJECT: and a diagnostic, with exit status one.
Any other exception, interruption, or resource failure is rejection as well:
only exit status zero together with the exact ACCEPT line denotes acceptance.
In particular,
ACCEPT never hides a nonempty user-supplied assumption context: every public
certificate has exactly two fields, goal and proof, and the root context and
free-variable scope are empty. A sequent is submitted by explicitly closing
its assumptions as implications and its parameters as universal quantifiers.

Run the reproducible regression suite and source measurement:

    python3 test_checker.py

The script writes metrics.json, validation.json, and the individual fixtures
under certificates/. It runs every fixture through the public stdin driver,
both normally and with Python -O. No correctness assertion relies on Python's
assert statement, which -O would disable.

THEORY
------

There is one numerical sort. Terms are variables, 0, and J(n; i,r.h), in
which the old-counter variable i and old-state variable r are distinct and
bound only in h. The counter n is outside their scope. The update h is fixed,
finite term syntax, with any other variables as passive parameters. It is
not an object-language function variable or numerical program code.

Write S(t) := J(t; i,r.0), and 1 := S(0), with i,r unused in 0. The nonlogical
axiom schemes are:

  J0:    J(0; i,r.h) = 1.

  STEP:  J(Sn; i,r.h) = b iff
           ((h[n/i,J(n;i,r.h)/r] = 0 and b = S(J(n;i,r.h)))
             or h[n/i,J(n;i,r.h)/r] = S(b)).

  SEP:   0 = 1 -> bottom.

The substitutions in STEP are simultaneous and capture avoiding. The iff
is the conjunction of the two implications; it is not a new connective.

The additional induction rule is contextual induction for one literal
equation E(x). From Gamma |- E(0) and Gamma,E(e) |- E(Se), infer
Gamma |- E(t), where e is fresh for Gamma, t, and the passive parameters.
Gamma may contain arbitrary quantified formulas. Compound induction
matrices are rejected, even when their atomic constituents are equations.

The logic is ordinary intuitionistic natural deduction with actual equality:
Hyp, reflexivity, equality elimination, bottom elimination, and the usual
introduction/elimination rules for and, or, implication, forall, and exists.
Contexts are reusable lists, so weakening, exchange, and contraction are
admissible structural operations, rather than extra certificate nodes.

JSON SYNTAX
-----------

Variables are names matching [A-Za-z][A-Za-z0-9_]*. Terms are:

  ["v", "x"]
  ["0"]
  ["j", counter_term, "i", "r", body_term]

Formulas are:

  ["=", left_term, right_term]
  ["bot"]
  ["and", left_formula, right_formula]
  ["or", left_formula, right_formula]
  ["imp", left_formula, right_formula]
  ["all", "x", body_formula]
  ["ex", "x", body_formula]

All constructor arities and sorts are checked. Bound-variable shadowing is
permitted and handled lexically. Bound-name changes are compared modulo
alpha equivalence. Undeclared free variables are rejected. Numeric term
values are never represented by untyped JSON integers; the only integer
field is a nonnegative hypothesis index, which rejects booleans and floats.

Every proof node has rule and conclusion fields. Its additional fields are
exactly those listed below; missing and extra fields are rejected.

  hyp          index
  refl         none
  j_zero       none
  j_step       counter, index, state, body, output
  separation   none
  eq_elim      equality, premise, variable, motive
  imp_intro    proof
  imp_elim     implication, argument
  and_intro    left, right
  and_left     proof
  and_right    proof
  or_left      proof
  or_right     proof
  or_elim      disjunction, left, right
  all_intro    eigen, proof
  all_elim     universal, term
  ex_intro     witness, proof
  ex_elim      existential, eigen, proof
  absurd       proof
  induction    variable, equation, term, eigen, base, step

Fields naming premises contain complete proof nodes. Term/formula fields
use the syntax above. The variable field of eq_elim and induction names a
fresh template variable, not a free variable silently added to the theorem.

For implication introduction the antecedent is appended to the context.
For disjunction elimination the appropriate disjunct is appended in each
branch. Existential elimination appends the opened witness instance, under
its fresh eigenparameter. Induction appends the current equation instance
only to its step branch. Hypothesis indices start at zero in the current
context; appending an assumption preserves all previous indices.

For equality elimination, equality proves s=t. The numerical template hole
is variable, motive is F(variable), premise proves F(s), and the submitted
conclusion must equal F(t), modulo alpha equivalence. Substitution descends
through both numerical and logical binders and renames binders as needed.

The j_step fields supply the four finite schema arguments and the two bound
names. The checker independently reconstructs the entire STEP formula and
compares it with the advertised conclusion. It does not trust an annotation
saying that an arbitrary equation is a computation.

CORRECTNESS ARGUMENT AND LIMITS
------------------------------

The intended mathematical checker is sound by induction on the finite
proof tree. Syntax validation and alpha equivalence provide ordinary terms
and formulas. The simultaneous substitution routine implements the usual
capture-avoiding substitution: it removes mappings shadowed by a binder,
renames binders that would capture a free variable of an inserted term, and
does not substitute recursively into replacement terms. Its structural
recursion is finite.

For each accepted node, recursively accepted premises have exactly the
formula instances checked by the corresponding natural-deduction rule.
The scope set records all currently admitted free parameters. Freshness
against that set implies freshness for the retained assumptions and outer
goal, and the ordinary eigenvariable conditions follow. The induction
branch additionally checks a literal equation root. J0, STEP, and SEP are
checked against their exact schemas. Thus every accepted root is a closed
theorem of the stated theory.

Conversely, an ordinary finite derivation in this rule inventory can be
serialized with these constructors. Alpha-renaming supplies fresh names;
explicit context indices supply hypotheses; each arithmetic instance is
expressed by its finite term body. Therefore the resource-unbounded
mathematical procedure is complete for this presentation. Standard Python
and hardware resource limits can reject or prevent execution of very large
valid certificates; no fixed practical machine checks all finite proofs.

This is a written correspondence argument, not a Lean/Rocq verification of
the Python implementation or of the bi-interpretability theorem. Finite
tests exercise concrete rule instances and known attacks; they do not prove
universal implementation correctness.

VALIDATION
----------

The initial run used CPython 3.12.14 and passed 104 of 104 public-driver
executions: 24 positive and 28 negative cases, each with and without -O.
All 20 inference families occur in positive proofs. Positive arithmetic
certificates derive positive loading, conditional increment, and the closed
functional-coverage theorem

  forall a (a=0 or a=S(J(1; i,r.a))).

Negative controls cover compound induction, nonreflexive equality, invalid
axiom instances, undeclared free variables, universal and existential
eigenvariable escape, false generalization of an existential witness,
capture in logical and numerical binders, malformed syntax, invalid indices,
extra rule fields, changed advertised goals, duplicate JSON keys, nonstandard
NaN/infinity, trailing JSON, and a parser-limited excessively long integer.

SOURCE METRICS
--------------

The complete checker is measured, including docstrings, grammar validation,
scope handling, substitution, alpha equivalence, inference checking, strict
JSON handling, and public driver. The producer, fixtures, and tests are not
trusted checker code and are excluded. No code golfing is used.

The measurement script reports raw source bytes, ast.unparse-normalized bytes
(with one trailing newline), significant tokens, AST nodes, and deterministic
gzip level-9 sizes of both raw and normalized source. Gzip is information,
not an optimization objective. See metrics.json for exact counts and SHA-256.
These counts substantially exceed the current ConciseIPRA compact-checker
frontier; this artifact establishes executable explicitness, not a size win.
