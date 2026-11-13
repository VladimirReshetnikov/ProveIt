476-BYTE COMPACT iPRA CHECKER

Result: compact476.py improves the observed normalized byte record from
477 to 476 bytes under exactly the inherited compact public-input
contract. It has 274 significant tokens and 306 AST nodes, so it does
not improve the independent 244-token or 265-AST-node records. This is
a composition of two existing implementation refinements, not a new
smaller inventory of mathematical axioms or a proof of minimality.

Run a certificate:
  python3 compact476.py < fixtures/compute_s0_u0_t0.json

Reproduce source transformation, full-module metrics and all fixtures:
  python3 verify.py

Expected result: 306 fixtures, 1,224 process executions, no failures.
Both normal and optimized Python execution are checked for candidate
and control. No assertion is used in the measured checker itself.

The complete input is a JSON stack with final header [goal,0] and
four-field preceding packets [m,s,u,t]. The public formula is promised
to be canonical closed guarded Eq/D syntax, and every datum is promised
to be an exact integer/list tree. The checker does not itself validate
this entire promise. Administrative majors are [] in this protocol.
It is not interchangeable with the older scalar-zero-major protocol.

See PROOF.txt for the universal successful-trace simulation, canonical
completeness, unchanged iPRA interpretation, explicit limits, and
credit for both inherited ingredients. The reference/ files reproduce
the earlier arguments used in the composition. They are excerpts, not
independent compilable documents or new proof-assistant verification.

Files:
  compact476.py                  complete measured candidate
  control477.py                  exact complete measured current control
  verify.py                      untrusted verification harness
  verification.json              exact measurements and execution outcomes
  independent_census_check.json independent remeasurement of prior census
  fixtures/                     original 306 candidate-protocol fixtures
  PROOF.txt                      correctness and precise scope of claims
  PROVENANCE.json                source/archive hashes and fixture manifest
  LICENSE-upstream.txt           upstream MIT-0 attribution/license
