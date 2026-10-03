# Independent audit verdict

Status: PASS for the shared-offset primitive-source quartic core, its paid
nonnegative-real selector extension, exact retained clock, and the bounded
implementation audited here. The optional positive-period multiplier is a
NATURAL-only or mixed-domain corollary, not an all-real-orthant corollary.

Audited implementation:
`primitive-certificates/certificate.py`

SHA-256:
`1401d008dcf27d2211e6a99911ecf382e6cc22cd012703bf45337f3d260a40cb`

The final source used the post-shift zero guard `e*z_post,tested`, rather
than a substituted old-counter sum. See `INDEPENDENT-PROOF.md` for the
soundness, completeness, entire-fiber uniqueness and domain arguments.

## Executable evidence

Both ordinary Python and `python -O` passed the independent script:

- 53,786 explicit checks per run, none relying on Python assert
- 136 expected strict-domain/schema/mutation rejection calls per run
- 7,056 primitive-program, input, horizon and optional-layer cases
- 8,748 complete bounded natural-witness assignments, including every
  offset and shifted-counter coordinate, for complementary Z/P sources
- Independent source interpreter and arithmetic residual evaluator agree
- Exact collected row support, written slots, nonzero rows, and ordered
  square-product ledger agree with small materialized polynomials
- Collected fully expanded polynomial evaluates identically to the SOS
- All five primitive forms and both counters are exercised
- Guard counter deliberately differs from branch side in test cases
- H=0, immediate halt, blocked runs, and forbidden post-halt padding covered
- Every coordinate of successful witnesses is individually perturbed
- Rational midpoint selectors demonstrate the unpaid-real pathology and
  are rejected by the paid norm
- Initial source mutations, frozen objects, map mutation and explicit
  constructor re-entry cannot change the certificate snapshot
- bool, float, Fraction-in-natural-domain, negative, malformed and fake
  primitive inputs are rejected at the supported exact APIs
- Branch.enabled, Branch.mask and Machine.kappa helper entry points are
  also exact-domain checked after their hardening during review
- Literal-source H=0,1,2 and H=10^30 closed-form ledgers are evaluated
- Default witness, residual-list and expanded exports reject oversized
  literal H>=1 certificates before constructing a horizon polynomial
- Source file hash is pinned, and code hash is unchanged across each run

The producer's separate 13-test suite was independently rerun under both
ordinary Python and `python -O`; both passed. These runs used unittest
module loading and did not invoke the producer's artifact-writing main.

Receipts: `audit-normal-receipt.json`, `audit-optimized-receipt.json`.
Development logs are omitted from this portable bundle. The receipts were
regenerated using the adapted portable script; see `PACKAGING-ADAPTATIONS.md`
at the release root for exact provenance.

## Counts and costs

For the literal source, B=141561, Z=23429, P=52036, M=66066. Core:

- Witness variables: 141565H
- Squared residual slots: 23435H+1
- Degree: at most four
- Written raw residual terms, H>=1: 566225H
- Exact retained clock: one variable, one square, with
  273693H-66065 additional written terms
- Paid nonnegative-real selector norm: H additional squares and 141562H
  additional written terms

The implementation reports three genuinely different costs: written
slots (including zeros/duplicate terms), collected row support, and sum of
squared collected row lengths. The last is ordered multiplication work,
not globally distinct support. It is explicitly not claiming that full
expansion is practical. See the separately generated literal ledgers and
`INDEPENDENT-PROOF.md` for the large expansion bounds.

## Required qualifications

1. Primitive-source schema is essential. Compound Boolean guards,
   positive-threshold tests, and guarded increments are outside this API.
2. Source determinism is enforced. Reversibility is independently recorded
   or optionally required; it is not needed for the source certificate.
3. Natural selectors are essential for the unpaid core. The paid norm
   establishes onehotness over the nonnegative real orthant only.
4. Numeric evaluation of the real variant supports exact ints/Fractions.
   The real-orthant theorem follows mathematically; finite rational tests
   are not being claimed as a proof over arbitrary reals.
5. H is a syntactic horizon parameter, not an existential variable. The
   objects provide an indexed family of ordinary finite polynomials.
6. The optional clock is the compiler's forward CA microedge count. It is
   not a TM step count or a literal source-transition count.
7. Optional return-period interpretation needs the referenced clean-input
   nonblocking and nonrepetition theorem. It is not established for
   arbitrary malformed encodings or arbitrary finite CA configurations.
8. A positive-return multiplier u must be natural. Making u merely
   nonnegative-real would certify t=Pi+1 with u=1/Pi. The least-period row
   introduces no multiplier and does not have this defect.
9. Python frozen dataclasses are an ordinary API immutability contract,
   not a sandbox against deliberate object.__setattr__ or code tampering.
10. Exact degree can drop in degenerate cases, especially H=0; four is the
    uniform upper bound. Counts include written zero residual slots.

## Findings resolved during audit

The original helper-level domain gap (unchecked public Branch.enabled,
Branch.mask flag and Machine.kappa input) was reported to the producer and
fixed before the stabilized runs. No remaining mathematical or executable
core defect was found. The return-multiplier domain caveat was identified
and kept separate from the core PASS verdict.

## Final proof review and portable replay

The producer PROOF.md was independently read in full. The count comparisons,
post-shift guard argument, direct P-slack comparison, offset-eliminated
clock cost, and natural/mixed-domain period qualifications are correct. The
standard semialgebraic impossibility argument is also sound; its cited Basu
survey Theorem 2.1 was independently checked on PDF page 5 at
https://www.math.purdue.edu/~sbasu/raag_survey2011_final-sep4-2014.pdf .
The supplementary multiplier requires a height bound depending on T: the
augmented tuple is bounded by max(core-with-clock bound,T).

The independent audit is replayable after moving the files:

    python audit_certificate.py --certificate-root PATH_TO_MODULE --literal-source PATH_TO_SOURCE_JSON --output PATH_TO_RECEIPTS
    python -O audit_certificate.py --certificate-root PATH_TO_MODULE --literal-source PATH_TO_SOURCE_JSON --output PATH_TO_RECEIPTS

The module and source are read-only inputs; the output directory receives
receipts and three literal ledgers. Defaults locate the module and source relative to this portable bundle. The implementation hash is checked before and after each
run to exclude untracked concurrent source changes.
