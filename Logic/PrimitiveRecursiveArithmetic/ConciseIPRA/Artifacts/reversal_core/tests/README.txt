FOCUSED REV CERTIFICATES AND EXECUTABLE CHECKS

rev_producer.py constructs the new equality derivations as explicit named
proof trees, then serializes their primitive REV rules. It is an untrusted
producer: no checker imports it. The named AST, substitution, and most
serializer code are reused from the attributed upstream native_producer.py.

The new equality fixtures exercise:
  - reflexivity at zero, a numeral, and a nested iterator;
  - constant-template reversal, including a contextual proof from 0=1;
  - joining two nonliteral terms both provably zero;
  - literal-zero-source congruence through nested iterator binders;
  - unrestricted equation transport reconstructed from the new macros.

Further translated fixtures cover witnessed atomic progress, QX at a
compound target, case introduction above Q, nonvacuous D elimination,
contextual equation induction, and transport through Q and D formulas.
The certificate format uses witnessed DI-progress, as the small published
source_dispatch programs do. The report relates this rule to the current
Lean core's direct QI-progress by explicit derivations in both directions;
the tests preserve the distinction between their primitive inventories.

The negative controls exercise false goals, unproved majors, lost induction
hypotheses, forbidden compound progress, invalid witnesses and specialization
targets, malformed public goals, and exact JSON typing. Unused non-int/list
prefixes are deliberately accepted by the untyped variants and rejected by
the whole-JSON typed recommended checker. These expectations are explicit.

The supplied run checked 36 cases and 362 complete-process expectations across
five checker profiles, each run normally and under Python -O, plus a matched
non-REV orientation control. Every expectation passed. Acceptance always
means exit status zero and stdout exactly ACCEPT followed by a newline.
The receipts record code hashes, runtime, and every outcome. The independent
readable checker passed another 72 process expectations on the same cases.
The portable package-level receipts are ../evidence/all_rev_reproduction.json
and ../evidence/readable_reproduction.json. These finite tests do not prove
universal soundness or bi-interpretability.

For one exactly identical closed goal, the inherited zero-symmetry fixture
uses 114 commands and 5,435 compact JSON bytes, while the new REV fixture
uses 37 commands and 1,259 bytes. proof_size_comparison.json records the
comparison. This measures that derivation only, not a general proof-length
bound and not proof-checker complexity.

FILES

  rev_producer.py        New equality macros and REV proof emitter.
  test_rev.py            Regeneration and subprocess harness.
  cases.json            Named cases, intended meaning, and expectations.
  certificates/         []-neutral certificates.
  certificates/zero_neutral/
                        Identical certificates with only command major []
                        changed to integer 0 for the zero-neutral variant.
  results.json          Recorded full run and exact checker source hashes.
  profiles/             Two byte-exact []-neutral REV profiles used by the
                        full reproduction. The three zero-neutral profiles
                        are the packaged programs under ../code/.
  upstream/native_producer.py
                        Pinned attributed producer reused by this package.

REPRODUCTION

From the package root, reproduce measurements and all 362 REV process
expectations, the readable checker's 72 expectations, and the 40 neutral
representation checks:

  python3 reproduce.py

From this tests directory, reproduce only the full 362-expectation REV suite:

  python3 test_rev.py

This default uses only files in the extracted package. It checks the two
profiles in profiles/, the three profiles in ../code/, and the matched
orientation control ../controls/control_shared_typed.py. The result is saved
to ../evidence/all_rev_reproduction.json. No working tree or network is needed.

To check only the recommended typed profile:

  python3 test_rev.py --single-checker ../code/checker_rev_typed.py \
      --profile full --zero-neutral --typed --receipt typed_rerun.json

The optional --checkers-dir argument remains available for the original
working-tree layout; it is not used by any default package command.

To check an individual zero-neutral certificate:

  python3 ../code/checker_rev_typed.py \
      < certificates/zero_neutral/conditional_zero_symmetry.json

UPSTREAM ATTRIBUTION

Repository: VladimirReshetnikov/ProveIt
Commit: 1517d9d79ce33f631e0f82960c849427cbba23bf
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/source_dispatch/tests/native_producer.py
URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/1517d9d79ce33f631e0f82960c849427cbba23bf/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/source_dispatch/tests/native_producer.py

The upstream file contains its earlier attribution chain. Its source was
retained byte for byte. The new work is rev_producer.py's explicit
root-reversal equality constructions, REV emitter, focused fixtures, and
test_rev.py's process checks. The repository's MIT-0 license applies to the
reused source and is included at ../reference/LICENSE-ProveIt.txt.
