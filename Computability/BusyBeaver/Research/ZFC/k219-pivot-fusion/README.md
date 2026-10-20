# K219 independent-pivot fusion and fourth-field cost measurements

The four-parameter membership fusion preserves the native calculus by finite
proof transformations. Reusing the fourth field already read by rho8 avoids
an additional input decode. The measured source saves **123 primitive
occurrences**, but adds **35 distinct subtrees**; the research compiler cannot
bind its newly exposed continuation entry. This is a calculus and source
experiment, with no smaller verified binary machine.

The separate code-dependent membership experiment removes the fourth input
field. Three layouts have one fewer distinct subtree, but all require 47 more
primitive occurrences. A conservative allocator produces decoder-bound raw
tables with 230–232 states. Their primitive runtime and initialization have
not been checked, and their consistency calibration remains open.

## Independent pivot

Write `R`, `E`, `Q`, `I` for the existing native constructors. Replace the
ungated rho5 output by truth code 0 and replace the membership-vacuity
conjunct inside the unchanged gated K bundle by

```
M(a,b,c,u) = E(u,a) → (R(u,b) → Q_c R(a,b)),   c ≠ a,b.
```

The pivot `u` is independent of `a,b,c`. The gate compares only `c` with the
two public labels. Unrestricted rho8, the G equality helper, rho1/rho2/rho6,
the other native rows, and the exact private-code K construction remain.
The [proof](proof.md) recovers every old rho5 and gated vacuity instance and
derives every new bundle in the old calculus. It preserves the same sole
falsity code 1, including degenerate and coincident-label cases. This is a
relative finite-proof equivalence using the inherited classical bridge; it
transports the old ordinary consistency calibration. It is not a newly
checked Lean theorem or internal PA equivalence.

The [schema checker](code/check_derivation.py) records 51 new-to-old and six
old-to-new steps, with 320 exhaustive Boolean valuation checks for its
classical-tautology steps. Its [result](results/derivation.json) explicitly
treats the inherited all-native-code classical bridge as a dependency.

The source temporarily stores `u` in logical register 0 while pairing its
old cache value onto register 8. After the final bundle is constructed it
restores both original cache and input tail, before the old freshness gate.
The former rho5 slot emits truth, preserving the number of AX outputs.
All splices replace closed factors. The input-read count is unchanged.

| Quantity | Original K219 | Pivot source |
| --- | ---: | ---: |
| Primitive occurrences | 4,744 | 4,621 |
| Distinct source subtrees, including leaves | 206 | 241 |
| Maximum address depth | 38 | 41 |
| Maximum zero run | 6 | 6 |
| Extra input fields | — | 0 |

The [actual receipt](results/pivot-v1/result.json) includes 250 finite
save/restore checks and two independent complete source-CFG constructions.
The all-natural register argument is given in the proof note; finite tests
do not prove it. The exact K219 identity compilation reproduces all 438
original transition rows. Compilation of the changed source fails at
`('CC',3)` as a new right leaf. No candidate table or binary state count is
reported for the pivot source.

## Removing the fourth field with a membership builder

For the existing propositional row

```
L(A,B,C,U) = ((C → U) → A) → ((A → C) → (B → C)),
```

we measured `U=R(codeX,codeY)` for each ordered pair of distinct variables
from `A,B,C`. The numerical formula codes become variable labels in this
new membership atom. These are separate restricted calculi, with no claim
that the constructed atom represents an arbitrary fourth formula.

Each replacement comprises the original closed `PUSH_COPY(X)`,
`PUSH_COPY(Y)`, and `RELATION` macros. Both binary associations of those
three atoms were measured. This is **not** an exhaustive association search
inside the macros. Both constructions have 80 primitive occurrences in
place of the old 33-step input read, hence 4,791 occurrences overall. They
preserve depth 38 and maximum zero run 6. The remaining input register is
unchanged by the replacement; the alternative proof encoding omits the old
fourth field. All other primitive occurrences, including the original rho5
and gated V/K bundle, remain in the same order.

| Fourth parameter | DAG, left association | DAG, right association | Raw states, left / right |
| --- | ---: | ---: | ---: |
| R(A,B) | 205 | 207 | 230 / 232 |
| R(A,C) | 206 | 207 | 231 / 232 |
| R(B,A) | 207 | 206 | 232 / 231 |
| R(B,C) | 205 | 207 | 230 / 232 |
| R(C,A) | 207 | 205 | 232 / 230 |
| R(C,B) | 207 | 207 | 232 / 232 |

The [first allocation attempt](results/membership-origin-reuse/result.json)
fails the exact decoder-prefix check in all 12 cases. That allocator can
repurpose an old decoder state which remains relevant to another path or
helper. The [protected successor](code/measure_protected.py) changes one line:
it disables all old-state repurposing. It retains old exact-subtree entries,
allocates changed nodes afresh, prunes graph-unreachable rows, and validates
the complete intended source/decoder relation. All 12
[protected allocations](results/membership-protected/result.json) pass that
check and retain 15 contextual aliases. Every reported count includes the
retained initialization states. It does not establish that initialization
or the arithmetic leaves still implement the new source.

Each run also checks all 81 small full-register inputs per variant (972
checks) against the exact native pairing formula and unchanged cache,
parameters, scratch registers and input tail. The larger raw allocations
are evidence against this immediate implementation, not a lower bound on
these calculi or on a better allocator. There was no further search.

The [fourth-parameter analysis](../k219-fourth-parameter/README.md) explains
why these membership builders escape the inherited HC range obstruction.
That semantic observation is not a consistency calibration. Syntax/DAG
savings and failure of one countermodel do not supply a smaller independent
machine.

## Reproduction and provenance

The immutable baseline is the maintained [K219 source](../candidate-k219/sites219.json)
and [native table](../candidate-k219/k219.native.tm), with SHA-256
`0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`
and `b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`.
Both measurement programs reject other bytes.

The two imported pure utilities are the pinned K221 `source_language.py`
and `build221.py`. Recover the original packages using the
[batch-185 guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-185-reproduction.md).
Unpack its `K220_Construction_2026-10-20/portable/vendor/K221_Construction_2026-10-20.zip`
into another fresh scratch directory. Use the resulting K221 wrapper as
`--k221`. The utilities' exact hashes are in the programs and every actual
receipt. Their executable main functions are not invoked.

From the repository root, using fresh output names:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-pivot-fusion/code/check_derivation.py --out /tmp/pivot-proof-fresh.json
python3 -B Computability/BusyBeaver/Research/ZFC/k219-pivot-fusion/code/measure.py --k219 Computability/BusyBeaver/Research/ZFC/candidate-k219 --k221 /tmp/k221-parent/K221_Construction_2026-10-20 --out /tmp/pivot-source-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-pivot-fusion/code/measure_membership.py --k219 Computability/BusyBeaver/Research/ZFC/candidate-k219 --k221 /tmp/k221-parent/K221_Construction_2026-10-20 --out /tmp/member-original-fresh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-pivot-fusion/code/measure_membership_protected.py --k219 Computability/BusyBeaver/Research/ZFC/candidate-k219 --k221 /tmp/k221-parent/K221_Construction_2026-10-20 --out /tmp/member-protected-fresh
```

The allocator adapts Source 138's `research/encoding/scripts/recompile.py`
(SHA-256 `4b50df00e13c689f771c020d926dc1264df1c33b70fb2422a5951f6d7d9610b1`),
with a K219 set-valued check for its duplicated old subtree role. The
independent-pivot logical idea appears in Source 138's membership-fusion
supplement; the register-storage implementation, measured variants and
explicit derivation trace are follow-up work. Original notices and the
MIT No Attribution license are retained under [licenses](licenses/).
The [inventory](inventory.json) pins the research inputs and generated
evidence. The published K219 candidate is unchanged.
