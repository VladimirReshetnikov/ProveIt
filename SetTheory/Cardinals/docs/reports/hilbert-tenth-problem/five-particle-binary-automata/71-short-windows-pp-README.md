# Short-exactness radius proof packet

The requested shortening succeeds for a NEW full-shift rule. Both edge and phase blocks use triple exactness b=4D+5; pair exactness stays L=3D+4. Both blocks are individually conservative full-shift involutions and preserve the entire inherited admissible five-particle simulation, including inverse steps and exact clocks.

- Main sufficient bound: 76D+105+3J
- A separately proved one-site output-support corollary, for the SAME rule: 76D+104+3J
- Inherited universal-ledger substitutions: 38,722,713 and 38,722,712 respectively
- Status: source proof complete; fresh independent review pending

Start with PROOF.md. It specifies every endpoint and predicate, proves full-shift safety and all-admissible preservation, addresses both signed corridor equality cases and the old reverse-endpoint anchor, and gives explicit malformed inputs distinguishing each new block and the composite from both predecessors. It also refutes the naive additional shortening of pair exactness with the unchanged template ranges.

check_static_algebra.py is a fresh, fully inspected STATIC AFFINE ARITHMETIC checker. Its 408 checks cover radius identities, separation inequalities, and 44 endpoint-support corner cases, including the phase t=L,d=D equality. It contains no CA evaluator or source interpreter and produces static-algebra-certificate.json. The symbolic proofs, not this arithmetic check, establish full-shift involutivity and admissible agreement.

Dependencies are copied unchanged and individually hashed. The source packet manifest pin is f1c19ca86641cbf5ebaed81d0c78e82563258753bbf8f38f2f46229247b71fa0, and combined audit manifest pin is 3bfe65db1ad9c0aab9fd13641cfbad843a292d2c2dbec444fa0f7ebb856876b1. The universal-source table is absent; its ledger and universality remain inherited. No old malformed-input arithmetic certificate or runtime count automatically transfers.

No Report26, Report70, or frozen source file was edited. PRESERVATION.md gives before/after evidence and discloses any separately observed concurrent live-report changes. No upstream/author programs, source interpreters, physical/trajectory simulations, schedules, or Lean were run. No public mutation occurred. This is not a minimal-radius, priority, new-source-universality, or implementation-certification claim. The radius-two appendix of the predecessor is not part of this continuation.
