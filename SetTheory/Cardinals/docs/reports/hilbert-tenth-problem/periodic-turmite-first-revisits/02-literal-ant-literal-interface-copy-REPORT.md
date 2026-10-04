# Literal COPY and delayed pair-instruction interfaces

## Result and scope

**PASS, finite physical constructions:** right-to-left COPY, moved COPY in both directions, fanout2/3, a two-activation delayed COPY, and delayed two-slot DUP/MOVE_RIGHT/MOVE_LEFT. These are fixed binary RL cell maps built from the exact primary-source primitives and newly constructed literal connectors. All legal histories described here are simulated microstep by microstep, including later optional output reads, with an aggregate maximum of **two departures per owned cell**.

The canonical geometry has bit-column pitch **600**. Ordinary COPY runs between storage rows at `y=50` and `y=250`. Delayed instructions preserve their old boxes during an unconditional eastward pass at `y=75`, then copy selected data during the westward return at `y=305`, into new storage boxes at `y=450`. All boxes retain the original orientation: WRITE from above, READ from below.

This report does not turn a finite local interface into a universality assertion. Physical row turnarounds, the complete mixed instruction atlas including NAND, aliases for vertically shared storage, growing layouts, initial configurations, and any acceptance/halting observable require separate evidence. The current packet's root work may supply some of those separately.

## Primary source and construction boundary

Source: Maldonado, Gajardo, Hellouin de Menibus, and Moreira, *Nontrivial Turmites are Turing-universal*, arXiv:1702.05547v1, 18 February 2017.

- Exact paper: https://arxiv.org/pdf/1702.05547v1
- Exact source archive: https://arxiv.org/src/1702.05547v1
- Figure 6 COPY/moved-COPY/fanout assets: `copy.pdf`, `copymov.pdf`, `copytri.pdf`
- Figure 9 row layout: `acdetalle.pdf`
- Literal primitive maps: Figures 10–12, supplied in `../common/primitive_maps.json`

The source figures motivate the control topology, not these new dimensions or connector pixels. No upstream program was run. The own-script router chooses a finite alternating-axis simple path inside specified corridors and initializes every departure cell according to its necessary left/right turn. The resulting ant uses only the fixed map. Primitive rotations preserve their original cell colors; no reflection or color-conjugation trick is used.

Reproduction imports only this packet's own `../common/geometry_kit.py` and the primitive JSON data. The earlier frozen packet is not modified and is not needed by the current scripts.

## Coordinates, parity, ownership and trace data

Coordinates: x east, y south. Headings: N=0, E=1, S=2, W=3. A step reads the current cell, turns right for color0 or left for color1, flips that cell, then moves one cell. Trace rows are

`[x, y, heading_before, color_before, x_after, y_after, heading_after]`.

Every JSON has a complete INIT0 board, exact primitive placements and rotations, connector maps and head-state paths, and one owner for every cell. Primitive bounding rectangles are reserved during route construction, including uncolored holes. Supports are pairwise disjoint; no shared ownership is assumed within a macro. Exit cells are the first cells outside support and are not counted as processed by the upstream resource. Independent verifiers run until that first undefined cell rather than trusting a requested stopping time.

Every external port and every simulated state has invariant

`I = (heading is horizontal) XOR ((x+y) mod2) = 0`.

Translations by 600 horizontally and 200 or 400 vertically preserve I. Connector terminals match the full next entry state, including heading. There is no phase repair by drawing a line between mismatched ports.

The source box translated to `(a,b)` has state cells `(a+4,b+4)` and `(a+5,b+4)`. INIT0 gives both color1; direct INIT1 changes exactly those cells to color0. WRITE into INIT0 also represents1 but changes additional cells. The constructions check direct INIT1 and prior-WRITE0 separately.

## Ordinary normalized COPY family

The primary normalized records are:

| File | Input box | Output boxes | Width | Owned cells | Optional-read histories |
|---|---|---|---:|---:|---:|
| `normalized_copy.json` | (100,50) | (100,250) | 600 | 3134 | 6 |
| `normalized_moved_copy_left.json` | (700,50) | (100,250) | 1200 | 6734 | 6 |
| `normalized_moved_copy_right.json` | (100,50) | (700,250) | 1200 | 6502 | 6 |
| `normalized_fanout2.json` | (100,50) | (100,250),(700,250) | 1200 | 6831 | 15 |
| `normalized_fanout3.json` | (100,50) | (100,250),(700,250),(1300,250) | 1800 | 10528 | 48 |

Control ports are `(width,105,W)` to `(0,105,W)`. Each support lies in `1≤x≤width`, `50≤y≤259`. Adjacent width600 COPYs therefore have disjoint ownership and exact W seams. In particular, the right neighbor terminates at the left neighbor's owned entry cell.

For a top box `(a,50)`, external WRITE is `(a+2,50,S)` to `(a+7,49,N)`. A bottom box `(a,250)` has external READ entry `(a+3,259,N)`, zero exit `(a-1,256,W)`, and one exit `(a+9,256,E)`.

Canonical single COPY primitive placements are:

- INPUT box `(100,50)`, rotation0
- OUTPUT box `(100,250)`, rotation0
- read_cross A offset `(190,105)`, rotation180°
- write_cross B offset `(140,181)`, rotation0
- UNION offset `(41,108)`, rotation270°

Its nine exact connector endpoint pairs are:

1. `(600,105,W)` → `(190,105,W)`
2. `(184,99,W)` → `(103,59,N)`
3. `(109,56,E)` → `(190,99,W)`
4. `(184,105,W)` → `(140,181,E)`
5. `(146,187,E)` → `(102,250,S)`
6. `(107,249,N)` → `(145,182,W)`
7. `(140,188,S)` → `(44,108,N)`
8. `(99,56,W)` → `(44,100,S)`
9. `(40,105,W)` → `(0,105,W)`

For input0, read_cross is used FIRST only, the input box returns0, and the upper UNION input is used. For input1, read_cross executes FIRST→SECOND; write_cross executes FIRST→SECOND; the output is written; and the lower UNION input is used. In fanout, the one branch writes each output box in left-to-right order before returning through write_cross. UNION is activated on exactly one branch.

Macro departure counts, excluding separate prior input WRITE and optional output READs:

| Member | Input0 | Input1, either representation |
|---|---:|---:|
| COPY | 1376 | 2892 |
| moved left | 2576 | 6492 |
| moved right | 2576 | 6260 |
| fanout2 | 2576 | 6564 |
| fanout3 | 3776 | 10236 |

A prior WRITE adds18 departures. Each later output READ adds19 for0 or23 for1. All ordered subsets of distinct output readers are checked: 2 possibilities for one output, 5 for two outputs, and16 for three outputs. The shared per-phase trace records are referenced by exhaustive history records, avoiding repeated copies of identical long control traces.

`independent_family_receipt.json` certifies81 histories and545,417 micro-prefix instances including history initials, plus90 extension replays. It reconstructs each map from primitive data and route records and uses a separate vector-turn interpreter without importing a generator.

The original smaller `copy_macro.json` and `*_family_member.json` files remain as passing preliminary constructions. The normalized files above are the canonical row-interface records.

## Two-activation delayed COPY

`delayed_copy.json`: 5664 owned cells, eight primitive placements,16 connectors.

- Old box `(100,50)`; new box `(100,450)`
- Forward E pass `(0,75,E)` → `(600,75,E)`:1208 departures, completely preserves old box
- Return W pass `(600,305,W)` → `(0,305,W)`:2204 departures for0,3816 for1
- Old WRITE `(102,50,S)` → `(107,49,N)`
- New READ `(103,459,N)` → `(99,456,W)` for0 or `(109,456,E)` for1

Three extra source crossings prime the later vertical return paths:

| Resource | Primitive and placement | E pass | Later W pass |
|---|---|---|---|
| forward_zero_cross | B at(34,75), rotation0 | FIRST | SECOND only for0 |
| forward_read_cross | A at(94,75), rotation0 | FIRST | SECOND always |
| forward_one_cross | B at(220,81), rotation0 | FIRST | SECOND only for1 |

The ordinary COPY read/write crossing complex is shifted down200: read_cross A at(190,305), write_cross B at(140,381), UNION at(41,308). The input remains on the original top row; the output moves to y450. The exact connector data are in the JSON, including every cell and head state.

All eight histories are checked: INIT0 or INIT1, or WRITE0 either before E or between E and W, each with or without a later output READ. The before/between choice is an explicit extra finite test, not a license for arbitrary unscheduled WRITE operations. The E trace is exactly identical in every history.

`delayed_copy_receipt.json` independently checks37,136 micro-prefix instances,48 stub replays, and nine physically concatenated two-tile E/W sweeps covering both input boxes' INIT0/INIT1/priorWRITE alternatives. The two sweeps remain separated activations; no turnaround is implicit. An optional intermediate INIT0 box at(100,250) has disjoint support and is never touched.

## Two-slot delayed pair instructions

These are the canonical fixed-width pair instruction interfaces:

| File | Function on old(p,q) | Selected source | Ignored source | Owned cells |
|---|---|---|---|---:|
| `pair_dup.json` | (p,p) | old slot0 | old slot1 | 10604 |
| `pair_move_right.json` | (0,p) | old slot0 | old slot1 | 10318 |
| `pair_move_left.json` | (q,0) | old slot1 | old slot0 | 10550 |

Every pair has both old boxes at `(100,50),(700,50)` and both new boxes at `(100,450),(700,450)`. A zero output is a literal complete INIT0 source box, not an absent output. An ignored old box is also a literal resource: it may be INIT0, direct INIT1, or have a prior WRITE0, but it is never READ or otherwise changed by either compute pass.

All pair interfaces:

- E `(0,75,E)` → `(1200,75,E)`,2408 departures
- W `(1200,305,W)` → `(0,305,W)`
- Old slot i WRITE `(102+600i,50,S)` → `(107+600i,49,N)`
- New slot i READ `(103+600i,459,N)`
- New slot i zero exit `(99+600i,456,W)`; one exit `(109+600i,456,E)`

For selected bit0 all W passes cost3404 departures. For selected bit1, DUP costs7488, MOVE_RIGHT7184, and MOVE_LEFT7416. Ignored input values do not affect those traces. Prior WRITEs cost18 each and precede E in this pair contract.

All3×3 old-box representations are checked. If both boxes have prior WRITEs, both possible WRITE orders are included, giving10 base cases. Each base case is replayed with all five ordered subsets of the two optional new-box READs. Thus each pair has50 complete histories. Every micro-prefix is covered by monotonic departure counters.

`pair_instruction_receipt.json` certifies all150 histories,1,293,526 micro-prefix instances, and90 simultaneous-stub replays. It explicitly checks that the ignored input is preserved, zero-output boxes are untouched until optional READ, selected READ occurs once, and all crossing projections are FIRST or FIRST→SECOND. Intermediate source boxes at(100,250) and(700,250) are support-disjoint.

## Neighbor seams, extensions, and resource aliasing

Ordinary normalized COPY support occupies `1≤x≤width`. Delayed support occupies `0≤x≤width`, but E and W have different boundary ownership: E owns its left entry and not its right exit; W owns its right entry and not its left exit. Boundary cells used by E and W have different y coordinates.

All16 ordered neighbors among delayed COPY, DUP, MOVE_RIGHT and MOVE_LEFT are checked literally. Translating the right module by the left module's width gives empty support intersection. E seam is `(left_width,75,E)` and W seam is `(left_width,305,W)`. No shared endpoint cell is processed twice merely because it is recorded as an upstream exit and downstream entry.

Every normalized ordinary/pair interface has simultaneously disjoint canonical extension stubs for any positive even length≤144. Exact finite maps are replayed at representative lengths and the maximum support check proves containment for intermediate even lengths. The delayed one-slot tile additionally has pairwise-disjoint unbounded outward half-strips, so arbitrary even extension lengths are valid there. Multi-output same-row lateral ports cannot all have disjoint unbounded rays, so no such stronger claim is made for them.

The canonical east-going length2m strip has white/color0 top cells and black/color1 bottom cells. For j=0,...,m−1 it processes `(2j,1,E),(2j,0,N),(2j+1,0,E),(2j+1,1,S)` and ends at `(2m,1,E)`, processing4m fresh cells. Rotation/translation gives the specified one-phase extensions for other headings. This is a statement about this canonical phase, not every possible arbitrary neighboring initialization.

When a new storage row becomes the next instruction's old row, its box is a single physical resource. The compiler must alias the same43 owned cells, require a compatible initialization, and combine WRITE-before-READ histories before counting visits. It must not place two independent owners on those cells or assume direct INIT1 is the complete board left after WRITE. The finite cases distinguish both possibilities precisely to support that later aliasing proof.

## Reproduction

Run from this directory, with ordinary Python (not `-O`):

1. `python build_normalized_copy_family.py`
2. `python build_delayed_copy.py`
3. `python build_pair_instructions.py`
4. `python verify_copy_family.py`
5. `python verify_delayed_copy.py`
6. `python verify_pair_instructions.py`

The source hashes, complete initial maps, ownership, phase traces and final board differences are in the JSON. Final changed-cell lists explicitly use the common INIT0 board as their basis. Receipts pin exact JSON hashes. The small preliminary examples can separately be regenerated with `build_copy.py` and `build_copy_family.py`.

## Complete local six-type compatibility audit

`atlas_compatibility_receipt.json` additionally uses the packet's normalized NOT and NAND as data. NOT_PAIR is NOT followed physically by a COPY at y200; NAND_PAIR is NAND followed by two COPYs at x0/600,y200. The intermediate storage aliases are exactly43 cells each, with identical initial colors.

The six audited full-round types are NOT_PAIR, NAND_PAIR, delayed COPY, DUP, MOVE_RIGHT, MOVE_LEFT. All36 ordered horizontal neighbors have disjoint support and exact E/W seams. All456 potentially relevant vertical ±400 shifts with horizontal offsets in600Z have exactly their aligned full-storage-box aliases, with no other overlap or initial-color disagreement. Every4/8-neighbor contact pair is enumerated, including separate counts/lists outside shared-box interiors. Adjacency is not treated as an ownership collision.

Canonical right and left turn templates from `strip/periodic_benchmark.json` independently replay to their exact endpoints and use each connector cell once. All42 edge-tile checks pass: six right-edge cases and36 current/next left-edge cases. Forty-six complete single-column or pair-column histories are also run physically through E→right-turn→W, not just as separately restarted E/W simulations. They include INIT0, INIT1, priorWRITE0 and both prior-WRITE orders where applicable, with later output READs and aggregate bound2.

The strip was regenerated after the COPY source update. The refreshed compatibility audit records current matching source pins and an empty stale-pin list. Source maps and all hashes are recorded explicitly.

## Skipped header-prefix columns: W-only NOT_PAIR

`marker_neighbors_receipt.json` includes six exact W-only NOT_PAIR histories. The upper E NOT is skipped entirely. Its old input may be INIT0, INIT1, or priorWRITE0, but W never processes that old box. Lower COPY starts at `(600,305,W)`, reads the untouched intermediate INIT0 box, exits at `(0,305,W)`, and leaves the final output0. An optional later READ0 is checked. W costs1376 departures, an optional prior old-input WRITE18, and final READ0 costs19.

This is a permanently skipped E activation in that row, not permission to run the upper E NOT later after its former output has already been read.

## Joint physical marker variants

Both marker constructions use width600 and retain the existing storage-row step200/full-round step400. No additional horizontal or vertical padding is needed. Their JSON includes full joint maps, exact shared-box aliases, all branch-dependent phases, ownership, and microtraces. Every branch continuation is exclusive.

### Right-stop NOT/COPY

`marker_right_stop.json` owns6269 cells. It combines footer NOT at y0 and external COPY at y200, sharing the marker box `(100,250)`. The input p is at `(100,50)`; marker m=NOT p is copied to `(100,450)`.

- p=0: E entry `(0,75,E)` writes m=1 and turns immediately into COPY, leaving at `(0,305,W)` after4736 departures; the later external W entry must not activate
- p=1, either representation: E leaves at `(600,75,E)` after1376 departures; a later W activation `(600,305,W)`→`(0,305,W)` takes1452 departures and copies m=0

A new UNION rotated270° at `(551,308)` combines the early write-return path at upper input `(554,300,S)` with the later external W path at lower input `(554,308,N)`. Its common output `(550,305,W)` enters COPY's FIRST crossing at `(190,305,W)`. The former NOT after-write route and COPY entry strip are replaced, not overlaid. Thus either branch primes COPY's required first crossing, and the new UNION is used exactly once.

### Left-start COPY/header-NOT

`marker_left_start.json` owns6193 cells. It combines external COPY at y200 and the next header NOT at y400, sharing `(100,450)`. COPY reads p from `(100,250)` and writes p to `(100,450)`; header NOT outputs NOT p at `(100,650)`.

- p=1, either representation: W entry `(600,305,W)` turns directly into this column's header NOT and leaves at `(600,475,E)` after4100 departures; the later ordinary header entry must not activate
- p=0: W continues to `(0,305,W)` after1376 departures; later ordinary header E `(0,475,E)`→`(600,475,E)` takes2208 departures

The p=1 diversion begins only after the COPY write-cross has completed SECOND, at `(140,388,S)`. A new UNION rotated90° at `(21,472)` combines this branch at `(18,472,S)` with the normal later header entry at `(18,480,N)`. Output `(22,475,E)` proceeds to the header-NOT FIRST crossing at `(50,475,E)`. No assumed or missing FIRST crossing is hidden in either history. The ordinary normal-entry header branch is required only for p=0.

`marker_variants_receipt.json` checks all12 complete input/read cases,44,558 micro-prefix instances and36 simultaneous-stub replays. It projects each trace onto every primitive resource: crosses are unused/FIRST/FIRST→SECOND, UNION is unused/LEFT/RIGHT, boxes have only the permitted WRITE-before-READ sequence, and every connector cell is processed at most once. Both marker maps admit pairwise-disjoint unbounded external half-strips, so arbitrary even canonical extensions are safe.

`marker_neighbors_receipt.json` checks all8 horizontal combinations with neighboring standard E-NOT/W-COPY columns. All12 vertical tests have exactly the allowed43-cell aliases, or no off-column overlap. Six extended physical histories additionally verify right-stop→next-headerNOT and left-start→next-headerW-COPY, including actual mutations of shared boxes. The left-start output at y650 is shared with COPY at y600; the right-stop output at y450 is shared with NOT at y400.

## Exact constant initial anchor

`left_start_anchor.json` exposes an exact prefix of the verified left-start INIT1 history:

- Virtual prefix entry `(600,305,W)`
- Source INIT1 setup changes only `(104,254),(105,254)` from1 to0
- Virtual prefix length2824
- Actual initial head `(50,475,E)`, immediately before the header-NOT FIRST crossing; that endpoint has not been processed by the prefix
- Remaining verified header suffix1276 departures, ending `(600,475,E)` and outputting0
- Net post-prefix initialization patch:2806 changed cells against the complete joint marker's common INIT0 background

The full post-prefix board, every prefix/suffix microstep, and exact net changed-cell list are recorded. The baseline comparison includes the original INIT1 source setup, not merely changes relative to an already-initialized source1 board. The two source state-cell flips are later undone by COPY READ, so they correctly do not appear as additional net changes. Adding them again would create the wrong initial board.

The independent checker reconstructs the prefix from the common INIT0 board plus the explicit INIT1 setup, requires exact equality with the patch and full post-prefix board, proves the endpoint is unprocessed, and replays the actual suffix plus optional output READ0. The suffix alone and the encompassing certified history satisfy bound2. This is an explicitly initialized suffix, not a claim that the skipped prefix physically ran.

`fixed_initial_anchor_patch.json` applies translation `(+288600,−400)`, giving fixed head `(288650,75,E)`. Each patch row includes both the expected literal-background color and new initial color. The complete background evaluator should require those expected colors to match before applying the2806 net changes. No ordinary headerINIT1 normal-entry behavior is assumed.

Additional reproduction commands:

1. `python audit_atlas_compatibility.py`
2. `python build_marker_variants.py`
3. `python build_initial_anchor.py`
4. `python verify_marker_variants.py`
5. `python verify_marker_neighbors.py`
6. `python translate_anchor.py`

## Global generator review and the missing-prior-COPY header mode

`GLOBAL_GENERATOR_REVIEW.md` and `global_generator_review.json` review the complete proposed color evaluator as a separate step. The finite evaluation checks263,525 cells and1,974 complete shared-box groups; the exact symbolic selection and margin arguments cover the unexpanded layout. The normal rising channel's entire long north strip is separated by interval bounds, not by sampling heights. Its total finite length is481238075996 departures.

The independent compressed-program analysis in `program_audit/` proves all601547591 decoded rows and their index bounds. Pair-left indices are0…919, highest touched column920, and exact live compiler peak915. It does not replace the color-geometry audit.

A further reachable initial/new-right-boundary case is certified in `header_entry_only_receipt.json`: LEFT_MARKER normal header E on current header input INIT0, without any preceding old COPY. All three possible unused old-source histories are preserved, and stopping, READ1, and nextCOPY→READ1 continuations give nine exact histories. Bare normal header INIT1 remains unnecessary and unclaimed.
