SUCCESSOR-SEEDED J: COMPLETE-CHECKER CERTIFICATES
==============================================

Run from this directory:

  python3 verify.py

The runner first regenerates every fixture with the untrusted named proof
producer, then starts fresh complete checker subprocesses for every case,
both with ordinary Python and with -O. The packaged runner uses
../code/checker.py, ../code/checker_direct.py, and ../code/checker_ast.py.
The accompanying JSON receipt records their exact SHA-256 hashes.

There are 36 distinct fixtures: 33 common cases (17 accepted derivations and
16 rejected inputs), plus three deliberate raw-encoding profile boundaries.
All three boundary aliases are accepted by the iterable checker and
rejected by both list-dispatch checkers. This makes 216 complete ordinary
and -O checker runs. Four deliberate unsafe modifications are also tested
against one targeted rejection fixture each, for each checker and mode:
24 mutation-control runs. The receipt reports the observed counts and any
failures. Successful finite tests do not replace a soundness proof.

ARITHMETIC ADAPTATION
--------------------

The trusted numerical computation rule now starts at S(seed):

  J(0,a;v.h) = S(a)
  J(S(n),a;v.h) = h[J(n,a;v.h)/v].

The producer has been rebuilt for those equations, not merely relabeled:

* Its compute helper returns S(seed) in the zero case.
* Reflexivity uses the constant-update equation J(1,0;v.term)=term.
* Equation-induction identity closures prove J(n,a;v.v)=S(a), actually
  using their induction hypotheses.
* Nested closures retain an arbitrary passive initializer parameter.
* The zero witness is the provably zero, truthy term J(1,0;v.0).
* A nonvacuous D elimination opens, uses, and discharges its witness.
* The contextual congruence example retains a gated 2=1 hypothesis for
  the base and uses its separate equation induction hypothesis in the step;
  no explosion rule is used in that generated derivation.
* Gating equations and the forged compound-progress example end at 1,
  consistently with the successor seed.

The proof producer maintains named symbolic contexts and fresh labels.
It does not import or call a checker or its validation routine. It emits
named proof trees, full raw JSON certificates, and command/allocation traces.

COVERAGE
--------

Positive common cases cover J0 at nonzero and compound initializers; JS
with active and constant states; derived reflexivity; atomic induction
with zero and nonzero initializers; specialization at an arbitrary compound
term; nested Q and nested D case introductions; nonvacuous witnesses and
D elimination; retained assumptions during induction; equality transport
under Q; and both kinds of neutral endpoint/target mismatch followed by a
valid proof of the unchanged formula.

Rejections cover 0=1; an unproved major; a neutral command followed by an
unproved target; free/future labels; malformed arities, mappings, recursive
seeds, and counters; the obsolete I0 equation; a nonzero replacement for an
essential zero witness; replacement of the actual induction hypothesis by
its base; and a forged compound-progress proof. The latter is a real
named derivation that requires a forbidden compound hypothesis, not merely
a malformed command.

The mutation controls verify that the designated rejection becomes
acceptance after exactly one relevant safety/semantic obligation is removed:

  omit_major_proof                  failed_major_does_not_fall_through
  permit_compound_progress          forbidden_compound_progress
  omit_recursive_image_validation  two_child_counter_constant_update
  restore_wrong_I0_semantics        old_I0_equation_is_false_for_J

The last mutation changes the numerical theory back to ordinary iteration;
it demonstrates sensitivity to the new successor seed, not a claim that
the old ordinary-iteration theory is itself unsound. Mutant source files
exist only in a temporary directory and are removed after the run.

FILES
-----

  producer.py        Named proof constructors, serializer, case inventory.
  verify.py          Complete-program runner and targeted mutation controls.
  PROTOCOL.txt       Readable canonical protocol and alias boundaries.
  cases.json         All certificates, meanings, named trees and traces.
  fixtures/          One JSON input per fixture for direct CLI invocation.
  test_summary.json  Full results, exact checker hashes, and Python version.
  test_summary.txt   Compact readable frozen-run receipt.

ATTRIBUTION AND PROVENANCE
-------------------------

The named syntax, four-field endpoint serializer, and original example
organization are adapted from VladimirReshetnikov/ProveIt:

  docs/drafts/ipra_generated_assumptions_2026-11-10.zip
  ipra_generated_assumptions_2026-11-10/tests/producer.py

SHA-256 of that inherited producer:
d2cfe29ea5296eee3cb0b114bee301cc7152b9d3fed8f9d4bb54f09e0ca2548f

The repository snapshot inspected here is
2fdcf5bf988bead821c416649f713f98b7ed8776. The original producer in turn
credits the named-specialization draft. The inherited MIT No Attribution
license is included at ../reference/PROVEIT_LICENSE.txt. The main report
separately credits the existing unresolved successor-seeded basis and the
inherited scalar finite-cycle/saturation predecessor strategy.

These fixtures are substantial finite regression evidence. They do not
kernel-formalize the full predecessor term, the arithmetic bootstrap, the
native-to-iPRA bridge, or the bi-interpretation metatheorem. The complete
mathematical proof and the finite numerical diagnostics are delivered
separately and labeled according to their actual verification status.
