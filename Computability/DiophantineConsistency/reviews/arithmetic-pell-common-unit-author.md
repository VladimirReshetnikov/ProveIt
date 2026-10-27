# ArithmeticPellCommonUnit: author validation

27 October 2026. The complemented47 agent authored and fully read the
148-line main and 43-line Checks. The final private pair is PASS with an
empty main log and four standard-only axiom reports. All three attempts,
including both unexecuted Checks snapshots, are preserved. No frozen proof,
shared cache, equation/display or Git state changed.

The only main imports are `ArithmeticGcdNormalization` and
`ArithmeticPellKnownUnit`. In any internal IΣ1 model, the public setup takes
only `R>0`, `f>0`, and the actual equation
`R*R+delta a=delta a*(f*f)`, where `delta a=(a+1)*(a+3)`.
It derives internal `b,e,n,S`, with positive e,n,S and `S<a+2`, satisfying
`S=ycoord e b`, `a+2=xcoord e b`, `f=xcoord n b`,
`delta a=delta b*S*S`, and `R=delta b*S*ycoord n b`.

Gcd normalization first supplies positive d,s,t with
`delta a=d*d*s`, `R=d*s*t`, and `f*f=1+s*t*t`.
The original parameter gives the known solution `(a+2,d)` for the same
positive discriminant s. One invocation of KnownUnit supplies b,v and a
single classification function. Applying it to `(a+2,d)` and `(f,t)`
derives both indices at exactly this b,v. The identities
`d=v*ycoord e b`, `t=v*ycoord n b`, and `delta b=s*v*v` give the
required common-unit formulas by ring identities. Positive d,t exclude
zero indices; positive d excludes S=0. The recurrence norm and `delta b≥1`
prove `S*S<(a+2)*(a+2)`, hence `S<a+2`.

The reusable `composition` helper assumes only the coordinate identity
`a+2=xcoord e b`. It derives its discriminant identity from the norm and
uses genuine Sigma1 successor induction at arbitrary internal p on the
conjunction of both coordinate equations. The accepted addition formulas
at `e*p+e` prove the step. This is not standard-Nat recursion and does not
assume composition, a desired index or scale positivity. The zero query is
included. `common_unit_composition` supplies this helper's coordinate
identity from the actual norm, retaining the same b,e,n,S for every p.
`common_unit_tsub` handles the literal truncated input only after deriving
`f*f-1+1=f*f` from f>0. No caller supplies a unit, gcd, coprimality,
minimality, source, desired-index or fundamental-unit premise.

Focused checks retain generic composition at arbitrary p and p=0, actual
setup, and the literal truncated endpoint with simultaneous witnesses for
all query indices. The four audited theorems are `composition`,
`common_unit_setup`, `common_unit_composition`, and `common_unit_tsub`.
Each reports only `propext`, `Classical.choice`, and `Quot.sound`.

| Module | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticPellCommonUnit | ec63496db122b74dede3417231e5752dff9ba0ea15e63618738617a87a69b089 | 274259f176d6f15ec83e534eff12f28d956d5868d98c5c681611a03a7af231d9 |
| ArithmeticPellCommonUnitChecks | e016d9406ee600f98549539664e95ae691d5dde3c36ae694233fd22791068cfd | 4f8fda2c74f8dc839676ee53cccb9fbc231677615d0797e6a085eafed2472d16 |

The frozen proposal SHA256 is
`7ab5627b00a4c6fc0459978c6d4d7d58aff0b053d1dc69bb2a71e57c61d04402`.
Its original cache plan SHA256 is
`7081d8c2bc515ea333aadb90fd3d6506643b09c26a5686f1f049c000438a0942`.
The latter preserves its historically provisional Gcd provider description.
Before any overlay or compiler, the separate accepted-Gcd supplement
`research/arithmetic-pell-common-unit-accepted-gcd.json`, SHA256
`30dd84a1b14560c94ed2bdb78e9c6ec1e09c6375106f6f199427f2fc5e7453c2`,
was frozen, fully reviewed by ROOT, and launch-approved. The driver uses
that supplement's exact accepted object, not a prose path substitution.
It changes only the in-memory provider record; original plan bytes stay
unchanged. Gcd's accepted ROOT object and full logs are byte-identical to
the earlier author record. KnownUnit also uses its accepted ROOT provider.

Exact reused closure is 99 custom modules, 95 Foundation, 384 custom
artifacts, 38 boundary names and 114 total boundary artifacts (38 primary
plus 76 companion), with zero refresh. Every selected source/object and
current import header, implicit Init and every one of 498 actual first
artifact providers are authenticated. The accepted supplement's full pins
are rechecked along with the original inventory. Cached prerequisites retain
their accepted source/trace provenance; this is not a Foundation or package
rebuild. No Checks module is imported as a dependency.

Every final source/Checks/driver was fully read before its compiler run.
Pinned Lean4.32 uses `-M6000 -j1 -DElab.async=false`, one thread and a
512MiB reserve. New target objects are regular files; cached inputs are
private links. The final provider is
`/tmp/arithmetic-pell-common-unit-author-gcwf9m_3/lib`.
The unchanged executed driver SHA256 is
`fa421cd5f9a83fca58780016c1a28f1f7e163d9650a56bfdf97269bedc3c419d`.

| Attempt | Main result / seconds | Checks result / seconds |
| --- | --- | --- |
| 1 | failed / 6.108 | not run; snapshot retained |
| 2 | failed / 6.724 | not run; snapshot retained |
| 3 | PASS / 7.071 | PASS / 2.070 |

Attempt1 found two order-helper application issues in the final S<A bound:
proving delta≥1 by simp, and supplying the wrong side's nonnegativity to
square comparison. Attempt2 corrected those and exposed the addition-side
helper mismatch in that same bound. Attempt3 uses explicit positivity-to-one
conversion, the correct square-comparison argument and two-sided addition
monotonicity. No mathematical statement, import, induction, cap or scope
changed. Final peak RSS is 1,819,512/1,784,700 KiB; final diagnostics are
empty apart from the requested axiom reports.

The [replay packet](arithmetic-pell-common-unit-replay.json) has SHA256
`f0d1fa0262177ebc9428ae2553dbe07c863628e2e38677f1f76654a4b51e3c0d`.
The [34-file evidence manifest](arithmetic-pell-common-unit-author-replay/FILES.json)
has SHA256 `bbea505f01ff11dfdc4239c4b91c273afd03f1d2e38cbf5f6a8eb7a6157c526b`.
It retains all three exact sources, Checks, drivers, input/provider records,
commands, complete logs/timings and the accepted-Gcd supplement. Final freeze
rehashing checked 3,420 observations across 1,942 paths, binding draft-source
records to their exact preserved snapshots.

The controller agent separately read the original 145+43 draft and found
no mathematical/interface issue; that was a source-only challenge, not a
compiler or provenance review. The final source differs only in the three
order-helper applications above. ROOT has read the intermediate proof and
will independently review/replay this final frozen packet.

Sequence strong divisibility, the large-index divisibility argument, cubic
congruence, full relaxed integrality, Qh/cofinal witnesses and final PA/HA
equivalence remain outside this packet. This is author validation only.
