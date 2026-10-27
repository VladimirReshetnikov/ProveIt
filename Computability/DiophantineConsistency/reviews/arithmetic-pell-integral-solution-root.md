# Actual relaxed norm gives an integral Pell solution: ROOT acceptance

27 October 2026. Accepted after complete final169-line main and41-line
Checks review, complete author receipt/driver/freeze review, and an
independent fresh pair. Both objects and complete logs match; all five
reports use only propext, Classical.choice and Quot.sound.

The actual positive norm R=i*c*c, c=Y_p(a), p,i,f>0, and
(a+2)*delta(a)*delta(a)<c now derive a positive internal m with p|m,
f=X_m(a), R=delta(a)*Y_m(a). A literal truncated-input adapter derives
its additive norm only after f>0 justifies the subtraction.

The proof invokes the actual common-unit theorem once and derives the
index multiple e*p|n before constructing m=p*k. Its proper-gcd argument
uses actual strong divisibility, derived positivity, 2*g≤e*p, and doubling
growth to contradict the supplied large-c bound. The same composition
witnesses then restore the original base. The caller supplies no common
unit, desired index multiple, gcd, coprimality, minimum or standardness.
The strict coordinate inequality includes index0; doubling explicitly
requires a positive index. Final c|m is not yet included.

Independent main4.689s/Checks1.889s have peak RSS1,809,640/1,794,944KiB.
Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false, one thread, fresh regular
outputs and a512MiB reserve. The main log is empty. ROOT's fully reviewed
author-derived runner adds frozen-packet, object, complete-log and report
comparisons; ROOT separately reviewed the proof and fresh outputs.

Exact reuse is101 custom modules,95 Foundation,386 custom artifacts and38
boundaries with114 total boundary artifacts:38 primaries and76 companions.
All500 actual first artifact providers match, along with every selected
source header and object pin. No dependency is refreshed. The final runner
authenticates1,256 distinct paths. The frozen original inventory is retained;
its separately reviewed supplement selects the independently accepted
StrongDivisibility ROOT object with identical bytes. Existing boundary and
trace provenance qualifications remain; no broad rebuild is claimed.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticPellIntegralSolution | 358d56e418a32843cd93c58266f406d49db3ae9373561ffb879307d7a0e927d1 | 7814dd0443e0438a5f110beca8dee926e32a5104fa96f279936aeeaa9f29a1af |
| ArithmeticPellIntegralSolutionChecks | e6b121a8e0188dd1f689dddbf72e8cf1330822ffe01c3ec8a4277d01b08ef0d2 | e74b9b5ba112d456b5138d1054b6a0f02fd6d62bf92c99707094ebd530df79e6 |

Accepted independent provider:
`/tmp/arithmetic-pell-integral-solution-root-awcmdrel/lib`.
The [ROOT packet](arithmetic-pell-integral-solution-root-replay.json) and
[manifest](arithmetic-pell-integral-solution-root-replay/FILES.json)
preserve this replay. The [author packet](arithmetic-pell-integral-solution-replay.json)
and25-file manifest retain both attempts, including the unused first Checks.
Its only failed main needed explicit1+1=2 normalization in the quotient
bound; statements, imports, induction and caps were unchanged.

The remaining c|m argument, complete relaxed auxiliary norm, subsequent
index recovery and cofinal witness construction, and the final equation/PA/HA
equivalence remain open. The equation display and all size metrics are unchanged.
