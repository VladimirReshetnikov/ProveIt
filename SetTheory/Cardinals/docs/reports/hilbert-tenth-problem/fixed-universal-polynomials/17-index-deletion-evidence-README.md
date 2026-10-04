# Full first-index-deletion counterfamily

The 81/82-operation deletion candidates collapse: for every genuine
fixed compiler numeral tuple and every ordinary positive input, there
is a full positive candidate zero whose missing h is not integral.
The established85-operation upper bound is unchanged.

Read FULL_COUNTERFAMILY.md for the self-contained infinite construction.
SOURCE_CORRESPONDENCE.md connects every supplied port and all six factors
to the two exact saved source arrays. The witness values are defined
parametrically; giant factorial-radix/Pell integers are not materialized.

The main new step is a factorial exponent t=L! that makes the odd part
of t divide2^t-1. A CRT choice of the residue exponent and Z then makes
the exact packed R congruent to that exponent modulo t, while a1100-block
radix makes R divisible55. This completes transport and genuine input
arithmetic for the dyadic family p=55u,n=40u,X=2^(55u),Y=2^(33u-1).
Both auxiliary quotient modes complete canonically, and the deleted h
has exact nonzero remainder25u-1.

## Files and evidence

- FULL_COUNTERFAMILY.md: full mathematical construction and precise scope
- SOURCE_CORRESPONDENCE.md: literal port/register/factor correspondence
- scout.json and the two parent JSON files: authenticated inert source
- PROOF.md: preceding noncircular p=R and exact-defect reduction
- SCALED_FAMILY.md: preceding genuinely scaled subsystem obstruction
- audit_bootstrap/: independent review and independently authored checks
- CHECKS.json: own static-source/reduction/scaled-family exact checks
- FULL_CHECKS.json: own full-construction lemma and component exact checks
- provenance/: pinned primary recipe notes, plus comparison to the later
  upstream scaled-subsystem note at93c34e817c7bf726becd47326d22ec5e511a4251
- MANIFEST.json: final frozen file SHA256 inventory, once review is complete
- FINAL_RELEASE_REVIEW.md: exact original independent binding, final root
  review, the two final clarity corrections, and honest replay attribution

The mock arithmetic test ports are explicitly not claimed to be genuine
compiler instances. The full theorem instead quantifies over an arbitrary
unchanged genuine compiler tuple and constructs its witnesses symbolically.
Neither finite tests nor a necessary-mask tuple replace that theorem.

## Replays

From any working directory:

    python3 /workspace/shared/first-index-attack-20261003/check_reduction.py --expect /workspace/shared/first-index-attack-20261003/CHECKS.json
    python3 -O /workspace/shared/first-index-attack-20261003/check_reduction.py --expect /workspace/shared/first-index-attack-20261003/CHECKS.json
    python3 /workspace/shared/first-index-attack-20261003/check_full_counterfamily.py --expect /workspace/shared/first-index-attack-20261003/FULL_CHECKS.json
    python3 -O /workspace/shared/first-index-attack-20261003/check_full_counterfamily.py --expect /workspace/shared/first-index-attack-20261003/FULL_CHECKS.json

Normal and optimized output is deterministic and byte-identical. The
checkers use explicit exceptions, so checks remain active under -O.
Both scripts are newly authored; no upstream code or saved arithmetic
schedule is executed. They do not materialize a full astronomical zero.
Default invocation writes canonical JSON only to stdout. --expect compares
exact bytes; optional --output creates only a fresh external file and
rejects paths within this packet or existing/expected output files.

The optional search_scaled.py was a candidate-generator exploration,
followed by exact independent Pell verification. Its records are preserved
only as intermediate subsystem evidence; they are not full-zero evidence.

No repository clone, public mutation, upload or publication was performed.

The completed independent full-family review is
audit_bootstrap/FULL_COUNTERFAMILY_AUDIT.md, verdict PASS. Its finite
checks and exact reviewed proof hash are recorded separately. The earlier
reduction review remains as historical dependency analysis; its open-case
language is superseded by the full counterfamily.

The release copies of its checkers can also be replayed read-only:

    python3 audit_bootstrap/check_bootstrap.py --expect audit_bootstrap/bootstrap_release_replay.json
    python3 -O audit_bootstrap/check_counterfamily.py --expect audit_bootstrap/counterfamily_release_replay.json

These relative commands assume this packet as working directory. Original
independent sources, receipt bindings and reports are preserved; release
CLI hardening and reruns are transparently attributed to the author.
Use python3 verify_manifest.py for final byte-integrity verification.
