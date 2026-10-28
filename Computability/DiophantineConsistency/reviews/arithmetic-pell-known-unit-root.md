# Internal known-unit classification: ROOT review

27 October 2026. Accepted after complete review of the206-line main,
50-line Checks, author receipt, executed driver and freeze script, followed
by an independent fresh pair. Both compiled objects and complete logs match
the author, and all four public axiom reports use only propext,
Classical.choice and Quot.sound. No dependency refresh was required.

For every internal IΣ1 model, a positive norm solution A²=1+D*S² with
D,S>0 and A>1 supplies a bounded least positive unit F,v. The bounded
Delta0 search includes the given seed. Any smaller ordinate solution also
has abscissa at most A, so the resulting minimum applies to all solutions,
including those not initially restricted to the seed box. F≥2 gives the
actual recurrence parameter b=F-2.

The same derived b,v classify every internal x²=1+D*y²:
there exists n≤y with x=xcoord(n,b) and y=v*ycoord(n,b).
The proof justifies both conjugate subtractions, proves the new ordinate
strictly smaller, retains the exact inverse equations and uses genuine
Sigma1 order induction with bounded universal abscissa. Its public endpoint
supplies no minimality, index, standardness or fundamental-unit oracle.
Checks use the same base/scale for two arbitrary solutions, cover y=0,
and expose the minimum's validity outside the original seed box.

Independent main19.676s/Checks1.856s have peak RSS1,865,088/1,795,280KiB.
Pinned Lean4.32 runs with -M6000 -j1 -DElab.async=false, one thread, fresh
regular outputs and a512MiB reserve. The main log is empty, with no final
diagnostics. ROOT needed one clean pair and no source correction. Its
reviewed runner derives from the author driver and adds frozen-source and
explicit object/full-log/report comparisons; the proof review and private
compiler invocation are independent of the author.

Exact reuse is97 custom modules,95 Foundation,382 custom artifacts,
38 external boundary names and zero refresh. All496 first artifact
providers match. The frozen plan's field external_companions=114 counts
all114 recorded boundary artifacts:38 primaries and76 companions. This
clarifies the historical field name without changing the frozen inventory
or scope supplement. Accepted cached provenance is retained; no Foundation
or external-package build is claimed. The driver rechecks1,069 distinct
observed paths after the final pair.

All three author attempts are preserved. The first two mains failed on
addition-side API elaboration, with one explicit numeral normalization in
the first attempt. Every input, including unexecuted Checks, has an exact
historical snapshot. ROOT's final authentication rebinds old source records
to those immutable snapshots and verifies the actual successful outputs.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticPellKnownUnit | c676e7c29719fbedf87aea549cefd57bee1df8844ef443a72a9d87467a9e3cb9 | efbe7eed7d2ec64cbcfbbce9e65812a489886be7ceed6f05c34aacb018c60cf8 |
| ArithmeticPellKnownUnitChecks | 9fd672d63abffe7011298c5d2323d2fdb82a204e5709a21ac9eaaba64ea0f12d | fe839490ea6ceaa6d3712212661996b981dd65f8c478a295d0e534e294d6260d |

Accepted independent provider:
`/tmp/arithmetic-pell-known-unit-root-rha8oka_/lib`.
The [ROOT packet](arithmetic-pell-known-unit-root-replay.json) and
[bundle manifest](arithmetic-pell-known-unit-root-replay/FILES.json) retain
the replay and final authentication. The separate
[author packet](arithmetic-pell-known-unit-replay.json) preserves all three
attempts under its33-file manifest.

Internal gcd/common-discriminant construction, composition, strong
divisibility and full relaxed integrality remain open, as do Qh congruences,
cofinal witnesses and final PA/HA assembly. The equation is unchanged.
