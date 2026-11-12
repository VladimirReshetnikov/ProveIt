EQUATION-ONLY ALIASES AND NEWEST-PARAMETER SPECIALIZATION
November 12, 2026

RESULT
Both backward equality replacement and fresh-alias substitution may be
restricted to literal equations while a retained clause is still specialized
only at the newest numerical parameter (at zero in the empty scope). The
resulting raw calculus has the same native consequences as the repository's
raw clause calculus and therefore inherits its whole-domain bi-interpretation
with full first-order iPRA.

This strengthens the mathematical restriction of the incoming alias_back
proposal, which retained Alias at compound exported formulas. It does not
beat the current checker-size frontier. The additional checks make the
matched complete programs 18 significant tokens, 23 AST nodes, and
66 normalized bytes larger. No smallest-axiomatization claim is made.

Read THEOREM.txt for the complete language, all inference schemes, the
uniform proof procedure construction, both interpretation directions, and
further questions. In particular, its positive-depth local transport lemma
avoids weakening a proof obtained when a parameter happened to be newest.
No local version of the atomic transport lemma is assumed.

CONTENTS
  code/atomic_alias.py          complete, readable standalone checker
  code/atomic_alias_small.py    complete checker with scope=context length
  code/compiler.py              untrusted formula-rank/source-proof compiler
  code/build_examples.py        builds the two compound-specialization examples
  controls/                    exact inherited matched acceptance modules
  source_tests/                source certificates, including 32 inherited ones
  tests/                       compiled target certificates and rejection cases
  verify.py                    rebuilds/rechecks certificates and measures modules
  measure.py                   pinned normalization/measurement convention
  evidence/                    measurements, every process result, open examples
  PROVENANCE.json               exact source-file hashes and change description
  LICENSE.txt                  inherited MIT-0 licence

RUN
  python3 verify.py
  python3 code/atomic_alias.py < tests/compound_specialization_rank2.json

Use CPython 3.12.14 for the exact frozen measurements. Only the Python
standard library is required. An acceptance is normal exit and exactly
ACCEPT followed by a newline. Exceptions/nonzero exits are rejections.
The compiler is not imported by either standalone acceptance module.

VERIFICATION
  34 closed source derivations compiled and replayed:
     32 inherited proofs and two new compound-specialization examples
     at matrix depths 1 and 2.
  196 standalone process executions, including normal and -O Python:
     both target checkers accept all 34 translated proofs;
     both reject 13 adversarial/forbidden-rule cases;
     both matched general-alias controls accept the two specifically
     disallowed compound Alias/Back certificates.
  3 additional open-sequent compiler examples:
     non-order-preserving parameter embeddings, non-contiguous clause
     occurrence maps, duplicated irrelevant clauses, and antecedent depth2
     against body depths0,1,2.

Finite executions support the implementation; the general metatheorem is
proved in THEOREM.txt. No Lean/Rocq verification of this extension is claimed.

MEASUREMENTS
Normalized by removing true docstrings, ast.unparse, one trailing newline.
Tokens exclude layout/comments; all AST nodes are charged. Entire standalone
modules include parsing, validation, inference checking, and CLI behavior.

                               tokens     AST    normalized bytes
  atomic_alias.py                 843     989       3215
  general_alias.py (control)       825     966       3149
  atomic_alias_small.py            791     939       2969
  general_alias_small.py           773     916       2903
  template_source.py               764     883       2918

The small variants exploit the invariant that every new numerical scope
appends exactly one clause, starting from an empty root. The readable
checker's derive function supports the independently recorded open examples,
where scope and context length need not coincide. All public-goal grammar
checks and all consumed-term checks are retained. A premise field attached
to an antecedent-free clause is unused under the inherited input convention.

PROOF FORMAT
Terms: 0; negative free numerical parameters; positive bound indices;
[0,t] for S(t); [n,a,h] for the iterator. Formulas: [s,t] or [B] for D B.
A D binds two positive indices; only the iterator's third child binds one.
A certificate is exactly {"goal": closed_formula, "proof": instruction_tree}.
Instruction tags are:
  c(counter,seed,body)              one of the two computation equations
  u(clause_index,premise)           specialize at newest parameter
  v(equation,major,minor)           EqBack, newest equality source
  a(outer_term,branch)              EqAlias, equation branch result only
  e(goal,major,branch)              paired elimination
  i(paired_goal,witness,branch)     inherited witness-selected introduction
All terms are raw. No computation normalization or hidden proof oracle occurs.
