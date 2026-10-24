# Wave-ten proposals and the current targets

The eight packages 68–75 arrived at `9513bd88ce` and were placed beside
the earlier reports at `d79b41884d`. All eight complete normal release
replays pass. The four guard/root-transfer packages also pass their full
optimized replays. The other four have the more specific optimized-check
coverage recorded in the [native review](PROPOSAL_REVIEW_WAVE10_NATIVE.md).
The [guard review](PROPOSAL_REVIEW_WAVE10_GUARDS.md) and both machine-readable
receipts record the original archive hashes and the exact replay scope.
The delivered trees were not repaired or rewritten during these checks.

## Decision

Keep the local whole-tuple compact54-sharp H2082 equation as the current
**nine-positive-variable operation target: 443 operations, degree
1,845,940**. Its natural companion uses 450 operations. Package 71 adds
**478 operations, degree 1,379,730**, a lower-degree alternative with a
larger coefficient payload. It does not dominate the operation target.

The largest structural changes are **38 unrestricted integer variables at
degree four**, independently from packages 69 and 71, and **11 positive
variables at degree 325 and 113 operations** from package 70. Preserve
these as alternative targets. The integer constructions use distinct
coefficient tuples and new sign-restoration arguments; no arbitrary port
substitution between them is justified.

The [one-page P69](candidates/one-page/README.md) remains the completed
presentation target. Its equation and every fixed constant fit on one page
using the permitted fixed sums, arithmetic, powers and quotient/remainder.
Its four compact54 ports are independently reproduced byte for byte, and
its action seed is bound in Lean to the actual dense K215 machine. The new
proposals do not yet supply an equally complete one-page coefficient
specification, nor a complete Lean/internal-ZFC consistency calibration.

There is still no single size ordering that makes one candidate simplest.
Variables, domain, degree, live operations and fixed coefficient size are
kept separate. Neither K215 nor Jones compression is a requirement on the
final construction; the direct proof-checker route remains active.

## New frontier points

Operations count live binary additions, subtractions and multiplications,
including scalar multiplication and squares. Fixed numeral leaves and
reuse of registers are free in this convention. A named register is not
an additional quantified variable.

| Package / construction | Domain | Variables | Degree | Operations |
|---|---|---:|---:|---:|
| 69 cone / 71 determinant guard | integers | **38** | **4** | not optimized |
| 69 cone / 71 determinant guard | integers | **32** | **6** | not optimized |
| 69 cone / 71 determinant guard | integers | **27** | **8** | not optimized |
| 68 nested joint positivity | integers | **26** | 16 | not optimized |
| 68 free-Lucas finalizer | integers | 10 | **1,576,864** | **481** |
| 70 three-root transfer | positive | 11 | **325** | **113** |
| 69 rational Pell merger | positive | 12 | **82** | **102** |
| 74 centered product | positive | 12 | 110 | **100** |
| 74 centered SOS | positive | 12 | 164 | **99** |
| 73 adaptive carrier | positive | 13 | 30 | **92** |
| 72 congruence carrier | positive | 13 | **28** | **98** |
| 72 retained product coordinate | positive | 14 | **24** | **101** |
| 71 composed nine | positive | 9 | **1,379,730** | **478** |

These are additions to the earlier multi-measure frontier, not a list of
all surviving earlier points. For example, the older 12-positive 89-operation,
degree-258 equation and the 15-positive 66-operation, degree-157 equation
remain different cost/degree choices.

Across all eight arrivals, 69's 82/102 dominates 70's 84/103 at twelve
positive variables. Package 74's 110/100 and 164/99 preserve the lower-cost
tradeoffs and dominate the corresponding 12-variable entries from 71,
73 and 75. Package 73's 13-variable 30/92 dominates 74's 30/93 and
70/75's 30/94; 72's 28/98 trades operations for lower degree. The 28-variable
octic from 68 is dominated in variable count and degree by the 27-variable
octic from 69/71, while its 26-variable degree-16 equation remains distinct.

The 10-integer 481-operation equation improves both cost and degree over
the reviewed wave-nine ten-integer frontier. Its fixed threshold is a
numeral leaf; charging five historical gates for constructing that fixed
leaf would give 486 operations. This convention must be stated when
comparing counted circuits.

## Coefficients and proof assessment

The two 38-variable quartics save variables by different positivity
arguments. Both prove soundness for arbitrary signed assignments and
completeness by regenerating canonical native witnesses. Their new
canonical bounds are not properties of every old zero. The cone tuple
uses 881,696 raw bytes for six fixed payloads; the determinant tuple uses
615,883 bytes. Their parent source-34 tuple uses 532,479 bytes. Consequently
these are variable-count improvements with a coefficient-size cost.

The 34-variable compact reanchored sextic from 73 uses the smaller whole
compact44 tuple, 295,388 raw bytes, with 437 symbolic-port terms. The
34-variable congruence sextic has 368 symbolic-port terms with the larger
source-34 tuple. No exact scalar-circuit comparison has been supplied for
these integer systems. The 12/13-positive constructions in 69/74/75 also
use compact44, whereas 68 and 75's signed sextic use source-34. None
licenses mixing those ports with compact54. Every MF port is already
shifted once.

The reviews found no additional local mathematical flaw in the new
ordinary arguments. In particular, they checked the rational-integrality
steps in both root mergers, the signed bootstrap before orientation,
the determinant/cone completeness bounds, and the recovered transport
quotients. Each still inherits named unbounded native/compiler, Pell and
literal machine/refutation interfaces. Finite coefficient reconstruction,
algebra, degree and topology checks do not prove those interfaces.

Package 68 also develops a direct single-conclusion flow encoding. Its
17-witness branch relation and 23-witness affine accumulator are local
components. The global polynomial remains uncompiled, unmaterialized and
uncounted: unbounded aggregation and two bounded-forall blocks still
need a compiler. These counts cannot be substituted for a closed
consistency equation.

## Formalization priority

Continue the authentic compact54 native calibration and the independent
direct numeric proof checker in parallel. Both address the outstanding
semantic endpoint. The existing literal quartic compiler is already proved
correct over all internal naturals, with an actual unconditional ZFC
derivation of its no-zero equivalence. Completing the internal checker
coding can therefore avoid the native-machine route entirely.

The small new arithmetic lemmas remain useful independent targets:
simultaneous positivity, universal determinant-sign soundness and
three-root rational integrality. A fully compiled candidate must ultimately
identify its actual object-language consistency predicate and prove the
requested biconditional in ZFC. No wave-ten release supplies that theorem
in Lean. The goal remains open.
