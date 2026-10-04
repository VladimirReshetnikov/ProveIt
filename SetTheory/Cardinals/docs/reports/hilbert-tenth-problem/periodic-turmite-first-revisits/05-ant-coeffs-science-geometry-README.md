# Finite motif ownership and coefficient profiles

All upstream Python files were read only. No upstream code, random-access decoder, ant evolution, or expanded schedule was executed. New scripts inspect finite JSON maps and perform finite coordinate-set unions, intersections, and shifts. Dependency packages were not changed.

## API and artifacts

- `profile_api.py`: `build_profiles()` returns `(H,B,F,Q)`. `H`, `B`, and `F` are length-576000 lists of 400-bit nonnegative column integers. `Q[kind][dx]` is `(positive_bits,negative_bits)`.
- `verify_profiles.py`: exact finite colored component lists and a streaming x-bin union audit, including color agreement and periodic x seams.
- `profile_audit.json`: raw and unique cell counts and overlap multiplicities; zero conflicts in every profile.
- `build_profiles.py --out NEW_DIRECTORY`: writes compact profile IDs and mask dictionaries to a previously absent directory.
- `profiles/MANIFEST.json`: exact counts, paths, SHA-256 hashes.
- `scan_motifs.py`, `motif_scan.json`: pair/DELAY and adjacent-round interface scans.
- `scan_boundaries.py`, `boundary_scan.json`: generic translated template comparisons. Some translations in this broad exploratory table do not occur in the actual atlas; conflicts in such hypothetical placements are not atlas conflicts. Actual profile audit is authoritative for boundary assembly.

## Geometry and ownership

Write `S=576000`, `R=601547591`, `V=400(R+2)`, `F=400(R+1)`. For one macro's vertically fundamental domain `[50,V+50)`, the disjoint ownership slabs are:

- Header H: `[50,450)`
- Program slabs B, r=1,...,R: `[400r+50,400r+450)`
- Footer F: `[F+50,F+450)=[V-350,V+50)`

Bit b in every profile is local y=50+b; for footer its global local coordinate is F+50+b. Use x modulo S. The alternate macro row is the x-translate by S/2=288000. Predecessor and successor half-shifts are the same modulo S. The full atlas is represented by these slabs and the per-operation signed corrections in the applicable program slab.

Each bulk slot uses DELAY clipped to `[50,450)`. Prior DELAY or pair-map tails at local y450..459 consist of the same 43 colored cells (23 black) per slot, wholly included in the next slot's initial interface. Thus they add no new cells. The preceding LEFT_TURN contributes its distinct tail shifted by -400: 163 colored cells, 82 black, y50..76. Current LEFT_TURN contributes 401 cells, 201 black, y305..449. Current RIGHT_TURN contributes 684 cells, 341 black. The up wire black column is x=right+175; the white column is x=right+174. All bulk components are support-disjoint. Bulk has exactly 5,386,966 colored cells and 2,695,878 black cells.

Header includes current header NOT/COPY, turns, top corner and wire, and predecessor footer tails translated by S/2 in x and -400 in y. All predecessor ordinary COPY and RIGHT_MARKER tails supply the common 23-black top interface. The predecessor LEFT_MARKER at slot1 lands at current slot481, precisely where current header NOT is omitted. Its tail occupies y50..259 and has 1620 blacks; relative to NOT it adds99/removes16. Its overlap with current COPY is43 cells/23black at y250..259. The two outer slots0,959 receive common tails without a current header tile. This is why header ownership cannot be obtained by naively adding raw template totals.

Footer includes NOT/COPY/markers, preceding program common interface and preceding LEFT_TURN tail, the final20 cells of the vertical black wire, the170-black bottom wire and10-black EN corner. Current footer has no turn maps of its own. LEFT_MARKER tail beyond footer y449 belongs to the next macro header.

Finite colored-union verification finds:

|Profile|Raw colored|Unique colored|Raw black|Unique black|Color conflicts|
|--|--:|--:|--:|--:|--:|
|H|5,941,771|5,859,426|2,979,510|2,935,465|0|
|B|5,386,966|5,386,966|2,695,878|2,695,878|0|
|F|5,944,375|5,862,030|2,980,815|2,936,770|0|

The profile dictionaries have respectively108,93,247 distinct masks including zero.

## Operation corrections

NAND is the exact union of nand_macro plus COPY shifted(0,200) and(600,200), as specified by generator.py. It has13,197 colored cells,6,614black. Its internal COPY overlaps remove46black from the naive sum.

Let D2 be the union of DELAY at x0 and x600. They are completely cell-disjoint and have5672black. For each pair operation T, define Q+=black(T)\black(D2) and Q-=black(D2)\black(T). Use these as signed additive masks, never raw OR of T with baseline.

|Kind|Plus|Minus|Net|Nonzero columns|
|--|--:|--:|--:|--:|
|DUP|1520|1884|-364|763|
|MOVE_LEFT|1424|1814|-390|678|
|MOVE_RIGHT|1495|2001|-506|772|
|NAND|3447|2505|942|1159|

All correction points have0<=x<1200 and56<=y<=449 (NAND57..297), so adjacent400-round corrections are disjoint even when selected slots change. Actual outside same-row neighbor DELAY slots at x-600 and x1200 are completely cell-disjoint from each operation map. Corrections cannot reach margin turns or wires. The shared incoming/outgoing23-black interfaces have zero correction. Thus after baseline ownership is resolved as above, correction sums are exactly additive and require no cross-round or cross-slot ownership subtraction.

## Sources

`/workspace/shared/report44-recovery-20261004/certificate/dependencies/recipe_assets/atlas/generator.py` (read only): geometry, map compositions, header and program maps, footer markers, and normal wire routes.

`.../ca/physical_program.py` (read only): operation kind meanings and selected-slot conventions. Its decoder/schedule was not used.

`.../ca/physical_program.json`: scalar geometry constants only.

Finite maps in `.../{copy,nand,not,strip,common}/*.json` supply all cells.
