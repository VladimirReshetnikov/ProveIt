# Actual first-step configuration and literal machine colors

Date: 2026-10-26. Independent full source/check review and fresh replay:
ROOT. See author receipts for [initialization](decimal-machine-initialization-author.md)
and [configuration colors](wang-machine-encoding-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| DecimalMachineInitialization.lean (139 lines) | 748587f903a4a1cc0d0c475ebc0ba9628887eaff0584e6d3a7944f4115b6b82f |
| DecimalMachineInitializationChecks.lean (85 lines) | 60cf20b9b63f90a53e03b9250130c57c9c5769a955b865d917baf941c63a5ee9 |
| WangMachineEncoding.lean (171 lines) | 0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e |
| WangMachineEncodingChecks.lean (91 lines) | eb23dd938d3e890fa6578f50911266ff15e8fd6fd975e70b527bb38b7397ed23 |

ROOT read each complete frozen source before fresh direct execution with
`lake env lean -M6000 -j1`. Both main outputs went to separate temporary
objects; checks imported frozen author-built main objects. All four runs
passed. Main logs are empty; all thirty-six axiom reports contain only
standard axioms or no axioms. No entire dependency or umbrella rebuild
is claimed.

The first decoded action is bound through the authenticated actual430
action table, without reevaluating the715-digit numeral. The actual
transition writes1, moves right and enters state1. Its exact clock1
configuration has head1 and finite-support tape[0], whose read bit is1
precisely at integer position0. The actual clock shift and blank-halting
equivalence explicitly exclude blank time0 as halted. StartSouth1, head
initializerSouth4 and both side rowsSouth0 agree with these exact components.

The configuration encoder sends operating state someq to its actual
number and none to215; the state map is injective. At the actual head it
uses the table constructor2*q+b+2; every other cell is the tape bit.
Head colors2..433 are disjoint from plain0/1, recover state and bit, and
identify the configuration's unique head. The initialized color function
is exactly1 at0,4 at1,0 elsewhere.

An action entering halt still writes at the old head and moves before
encoding its resulting head as432/433. Synthetic left-moving write/erase
checks distinguish the moved halted head from the old plain cell and
exercise both final read bits. No tape-list normalization or all-blank
post-step assumption is introduced.

These are actual operational and color facts, without tiling/run
calibration premises. Relating entire later tile rows to actual steps,
extracting a halting run, the converse/controller and internal-ZFC proof
remain further obligations. The decimal equation and metrics are unchanged.
