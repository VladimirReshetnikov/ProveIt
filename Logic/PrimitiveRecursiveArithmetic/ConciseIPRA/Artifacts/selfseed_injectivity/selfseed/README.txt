A COMPLETE READABLE CHECKER FOR THE SELF-SEEDED THEORY
===================================================

checker_without_injectivity.py is a standalone natural-deduction proof
checker for T_F^-. checker_with_injectivity.py is its exact matched control
for T_F. The second file differs only by one additional successor-injectivity
axiom branch. Both files read JSON themselves, validate all consumed syntax
and scope, check complete proofs, and print ACCEPT on success. Neither
imports a local helper, evaluates supplied Python, uses a theorem database,
or delegates proof checking to another executable.

The proof in the main research report derives successor injectivity in
T_F^-, so deleting that branch preserves the mathematical theorem set.
This directory supplies a transparent implementation comparison. It does
not contain a full natural-deduction certificate for the new injectivity
proof; its proof certificates exercise the kernel and its important side
conditions. The main report, rather than the finite tests here, establishes
the axiom deletion and the inherited iPRA bi-interpretation.

MEASUREMENTS
------------
CPython 3.12.14; complete modules; ast.unparse plus one final LF. All comments
and docstrings in the raw files are counted in raw size; normalized size
retains the common module and function docstrings. Both modules have the
identical documentation and structure except for the one axiom branch.

                             raw    normalized  tokens   AST   gzip-9
T_F^-                       8700       8698       1897    2192    2172
T_F                         8898       8896       1947    2247    2199
Deletion saves               198        198         50      55      27

Gzip compresses normalized source at level 9 with mtime=0. The compressed
copies are supplied for inspection, not used by either checker. These
readable fully validated checkers are much larger than the compact native
scalar profiles, which use different syntax and input contracts. No
cross-contract frontier claim is made.

RUN
---
  python3 checker_without_injectivity.py < fixtures/equation_induction_used_hypothesis.json
  python3 checker_without_injectivity.py < fixtures/recursor_binder_capture_control.json
  python3 verify.py

Success is normal exit and exactly ACCEPT followed by LF. Exceptions reject.
The implementation uses explicit require checks, so python3 -O does not
disable verification. Mathematical completeness means finite ideal execution;
a physical Python process also has memory and recursion limits.

THE MATHEMATICAL THEORY
-----------------------
One numerical sort, with terms x,0,S(t),epsilon(s,t),F(n;v.h). Only v is
bound in h. In particular the original F has no initializer and its body
has no separately supplied counter parameter. Write 1=S(0).

Nonlogical schemes:
  F(0;v.h) = S(h[0/v]);
  F(S(n);v.h) = h[F(n;v.h)/v];
  epsilon(s,t)=0 OR epsilon(s,t)=1;
  epsilon(s,t)=1 IFF s=t;
  0=1 -> false.

Literal-equation induction, with arbitrary side assumptions Gamma:
  Gamma proves E(0),
  Gamma,E(z) proves E(S(z)),
  ---------------------------------------
  Gamma proves E(t).
Here E is literally an equation, z is fresh for Gamma, the template E,
and the target term t, and the extra E(z) assumption is discharged.
The checker chooses z outside the entire current parameter set, which
is a harmless stronger freshness convention because names can be renamed.

Ordinary intuitionistic first-order natural deduction with actual equality
is included in full. No excluded-middle or double-negation-elimination
rule is included. A biconditional is represented by the conjunction of
its two implications. The matched control additionally has
  S(s)=S(t) -> s=t.

Source definition: VladimirReshetnikov/ProveIt, pinned commit
78edba03ee060644464f76e388578584b356520a, file
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch08_seed.tex
(git blob 80c36f262206c8382e5188dd26008d585c3935b9).
The theory is inherited; these explicit readable checker modules are new.

INPUT SYNTAX
------------
The entire document is a JSON object with exactly two keys:
  {"goal": CLOSED_FORMULA, "proof": PROOF_TREE}.
There are no proof imports or external assumptions at the root.

Term arrays:
  ["0"]                 zero
  ["v", "name"]         a scoped named free parameter
  ["b", j]              de Bruijn bound index j (exact integer >=0)
  ["S", t]              successor
  ["e", s, t]           equality test
  ["F", n, h]           F(n;v.h), with one extra slot in h only

Formula arrays:
  ["false"]
  ["=", s, t]
  ["and", A, B]
  ["or", A, B]
  ["imp", A, B]
  ["all", A]            one extra bound slot in A
  ["ex", A]             one extra bound slot in A

Index 0 denotes the nearest enclosing numerical binder, whether it is a
quantifier or an F-state binder. The F counter is outside its state binder.
The public goal has no unbound indices and no named free parameters.
Booleans are not accepted as integers. Every declared constructor has
exactly the stated arity; unknown tags and surplus fields reject.

The kernel's instantiate operation removes one outer slot from a template
and substitutes a term validated in the current numerical scope. Such an
image has no unbound index, although it may contain its own F binders, so
copying the image below a new binder is capture-free. The abstract operation
turns one fresh named parameter into the corresponding bound index, tracking
both quantifier binders and F-state binders.

PROOF TREES
-----------
Each premise named below is itself a proof tree. The checker synthesizes the
conclusion of each tree and compares premises exactly; de Bruijn indices
make alpha-renaming irrelevant. Context indices start at 0 in the outermost
assumption, and new discharged assumptions are appended.

  ["hyp", i]                         use context entry i
  ["refl", t]                        infer t=t
  ["replace", p, B, q]               p proves s=t; q proves B(s);
                                     infer B(t), B has one template slot

  ["andI", p, q]                     conjunction introduction
  ["andL", p], ["andR", p]           conjunction projections
  ["orL", p, B]                      infer A OR B from p:A
  ["orR", A, p]                      infer A OR B from p:B
  ["orE", p, q, r]                   p:A OR B; q:C under A;
                                     r:C under B; infer C
  ["impI", A, p]                     p:B under A; infer A -> B
  ["impE", p, q]                     p:A -> B, q:A; infer B
  ["falseE", A, p]                   p:false; infer A

  ["allI", "name", p]                check p with a new parameter, then
                                     bind it in the synthesized conclusion
  ["allE", p, t]                     specialize a universal premise at t
  ["exI", B, t, p]                   p:B(t); infer EXISTS x B(x)
  ["exE", p, "name", q]              open p:EXISTS x B(x) with a fresh
                                     parameter and assumption B(name);
                                     check q:C and reject if name escapes C

  ["ind", E, t, p, "name", q]         p:E(0); q:E(S(name)) under E(name);
                                     infer E(t). E is a literal equation
                                     template with one bound slot.

Axiom nodes:
  ["axiom", "F0", h]
  ["axiom", "FS", n, h]
  ["axiom", "range", s, t]
  ["axiom", "reflection", s, t]
  ["axiom", "separation"]
Only the control file also recognizes:
  ["axiom", "injectivity", s, t].

Axioms F0 and FS take the literal F-body h in a one-slot numerical scope;
there is no hidden evaluator and no extension by graph-defined functions.

SOUNDNESS AND COMPLETENESS OF THE IMPLEMENTED CALCULUS
-----------------------------------------------------
The well-formedness validator follows the displayed mutually sorted syntax.
Tree induction proves that instantiation preserves well-formedness and gives
capture-avoiding substitution, and that abstraction binds exactly the chosen
fresh parameter. The two inductions increment depth only in quantifier bodies
and F bodies, never in F counters.

Induction on prove(proof,context,parameters) establishes this invariant:
a successful return is a well-formed formula in the current parameter
scope, derivable from the supplied well-formed context in the displayed
calculus. Each axiom branch constructs exactly its declared instance.
Equality replacement checks both its equality major and its matching source
instance. Connective rules are the standard intuitionistic rules. allI's
new parameter is absent from every old assumption. exE additionally checks
that its witness does not escape its result. The induction branch validates
E before allocating its fresh parameter, insists on a literal equation,
and checks base and successor premises in their correct contexts. At the
root the context and parameter set are empty, and the synthesized formula
must equal the validated closed requested goal. Thus acceptance implies a
theorem of the stated theory.

Conversely, translate any finite derivation in those natural-deduction
rules to its displayed proof tree, choosing fresh parameter strings where
necessary and encoding bound variables by de Bruijn indices. Every rule
then passes the corresponding branch by the substitution lemmas. Standard
weakening is implemented by context-index renaming; all ordinary finite
intuitionistic derivations can be expressed in this rule basis. Consequently
every theorem of this presentation has an accepted finite ideal certificate.
This is a written structural correspondence argument, not a new mechanically
verified Python semantics proof.

VALIDATION AND LIMITATIONS
--------------------------
verify.py checks the exact single-branch source difference, reproduces all
metrics, and runs 35 fixtures through both programs in normal and -O modes:
140 isolated executions, zero unexpected outcomes. Positive cases include
F computations with used state, equality-test reflection and range,
universal and existential rules, conjunction/disjunction/implication,
capture-sensitive F bodies, and the actual used-hypothesis induction proof
  forall n, F(n;v.v)=1,
also under an additional fixed side assumption. The witnesses, not just
expected formulas, are provided as complete JSON proof trees.

Negative cases include incorrect computation endpoints, false 0=1,
compound induction, missing induction steps, negative/Boolean indices,
unallocated parameters, reused eigenparameters, unknown rules and surplus
fields. Two attacks would prove the literal false equation 0=1 if the
relevant side condition were deleted: collision of two escaping existential
witnesses and generalization of a parameter present in a side assumption.
They are rejected by both implementations. The control-only primitive
injectivity certificate is intentionally accepted by T_F and rejected as an
unknown primitive tag by T_F^-; theorem equality relies on the derived
proof from the main report, not on unchanged certificate languages.

The tests support implementation review; they do not prove bi-interpretability,
the new axiom-deletion theorem, or universal soundness. The two checker files
are fully explicit and suitable for further independent verification.
