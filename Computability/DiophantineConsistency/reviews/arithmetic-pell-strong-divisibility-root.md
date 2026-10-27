# Internal Pell strong divisibility: ROOT acceptance

27 October 2026. Accepted after complete review of the196-line main,
46-line Checks, author receipt, executed driver and freeze script, followed
by an independent fresh pair. Both objects and complete logs match the
author; all seven reports use only propext, Classical.choice and Quot.sound.

For arbitrary internal indices m,n in every IΣ1 model, the actual represented
functions satisfy gcd(Y(m),Y(n))=Y(gcd(m,n)) and Y(m)|Y(n) iff m|n.
The theorem includes either index0. The norm derives a natural coefficient
unit certificate for X(m) against any divisor of Y(m), including divisor0
when permitted. Addition and that certificate derive Euclidean reduction
of common divisors. Genuine Sigma1 order induction uses a bounded
two-index invariant; both subtraction branches retain their order guards.
The index converse uses derived strict growth, with no modulus positivity
or assumed coprimality. Multiplying the actual gcd certificate proves the
scaled common-divisor endpoint even for scale0, without cancelling it.

Independent main6.720s/Checks2.205s have peak RSS1,826,436/1,794,100KiB.
Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false, one thread, fresh regular
outputs and a512MiB reserve. The main log is empty. ROOT's fully reviewed
author-derived runner adds frozen-source, object, complete-log and report
comparisons; ROOT separately reviewed the full proof and fresh outputs.

Exact reuse is97 custom modules,95 Foundation,382 custom artifacts and38
boundary names with114 total boundary artifacts:38 primaries and76 companions.
All496 actual first artifact providers match, along with all selected source
headers and object pins. No dependency is refreshed. Final runner
authentication covers1,095 distinct paths. Only Recurrence and the accepted
GcdNormalization are direct imports; existing provenance qualifications are
retained, with no Foundation or package rebuild claim.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticPellStrongDivisibility | a98ec37a7c16151236e8dacdd433c6ecd2e7d870c7a58c4b710267f6c9fd6c92 | 51fe8bb3ed563268ec08c8e00a42a46825daac58f58874228713895b71de2385 |
| ArithmeticPellStrongDivisibilityChecks | 589bd12f7607f6f462d15427796dfb9e161452fe213434e776169fe3dc215ab6 | 96e243fff405cb5f9fc4a933f68a431cf3d9f9a6535422b4b241ca426236ee45 |

Accepted independent provider:
`/tmp/arithmetic-pell-strong-divisibility-root-mljfsamm/lib`.
The [ROOT packet](arithmetic-pell-strong-divisibility-root-replay.json) and
[manifest](arithmetic-pell-strong-divisibility-root-replay/FILES.json)
preserve this replay. The [author packet](arithmetic-pell-strong-divisibility-replay.json)
and24-file manifest retain both attempts and the unused first Checks input.
The first main failed only on two global rewrites in the scaled gcd helper;
explicit congrArg multiplication fixes them without changing statements,
imports, induction or caps.

The large-c estimate forcing e*p|n, cubic congruences, complete relaxed
integrality, Qh/cofinal witnesses and the final equation/PA/HA equivalence
remain open. The displayed equation and all size metrics are unchanged.
