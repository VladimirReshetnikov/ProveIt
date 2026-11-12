GROUPED CERTIFICATES FOR THE CURRENT GUARDED iPRA CHECKER
========================================================

This is a small certificate-format refinement, not a new arithmetic or
logical axiom. It does not meet the stronger request for one mathematical
construction below every current complexity coordinate.

The pinned comparison is ProveIt commit
36d37fc1071fe289371f6bcd7dcfa0eac593a5a6.

                       Significant tokens  AST nodes  Normalized bytes
Existing token checker          251            283             605
Grouped token checker           250            281             604
Matched strict control          403            453             972
Grouped strict companion        402            451             971

The current compact coordinate envelope is (251,275,502), attained by
three different programs. The new compact program improves its token
coordinate to 250. Its 281 AST nodes exceed the incumbent 275-node minimum;
its 604 bytes exceed the incumbent 502-byte minimum. The inherited strict
byte checker in progress_independence has (421,471,869), so the strict
companion is not a byte record either. A distinct native public-goal
interface has (327,375,643); its contract must not be conflated with the
guarded interface and whole-certificate alphabet check used here.

Usage
-----
  python3 translate.py < flat.json > grouped.json
  python3 code/checker_grouped.py < grouped.json
  python3 code/checker_grouped_strict.py < grouped.json
  python3 translate.py --reverse < grouped.json > flat.json
  python3 verify.py

The checkers print ACCEPT only after a successful finite check. An exception
or a nonzero exit status rejects. The mathematical recognizer convention,
as in the repository, allows whatever finite resources a finite certificate
requires. The compact try/traversal scanner can run indefinitely on a
nonempty string under idealized unlimited resources; such strings are
outside its promised integer/list syntax and are rejected before checking
by the strict companion.

Files
-----
  code/checker_grouped.py          Complete 250-token compact module.
  code/control_tokens.py           Matched 251-token source from the repo.
  code/checker_grouped_strict.py    Includes the actual input/public validator.
  code/control_tokens_strict.py    Same validator on the matched control.
  translate.py                    Explicit forward/backward format maps.
  PROOF.txt                       Exact simulation argument and limitations.
  verify.py                       Complete-source metrics and regressions.
  PROVENANCE.json                 Pinned paths and source hashes.
  fixtures/                       The two certificate representations.
  evidence/results.json           Reproduced metrics and 65 checks.

Sixty upstream/derived fixture pairs and five strict alphabet checks pass.
All 39 available upstream cases were retained. The upstream manifest names
one absent fixture; evidence/missing_upstream_fixture.json records it.
Twenty-one positive legacy fixtures use null for the false major marker;
the derived integer-marker copies replace that marker by 0, its exact same
branch value. The strict companion rejects the legacy null input and accepts
only the copies whose public goal satisfies its guarded grammar.

No Lean verification of these Python modules is claimed. The mathematical
iPRA bridge and canonical compiler are inherited from ConciseIPRA; the new
universal statement is the elementary format simulation in PROOF.txt.
