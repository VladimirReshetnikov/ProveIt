# Literal periodic ant interface proof for review

## Status and model

This is the global proof proposed for the literal generator in `generator.py`. Its final gate status must be read with the independent global review and the final manifest. Boolean verification, physical template verification, and global assembly are separate claims; none is substituted for another.

Coordinates increase east and south. Headings N,E,S,W are 0,1,2,3. Color 0 turns right and color 1 turns left. A snapshot is before departure: the current cell is read, flipped, and the head moves one step in the resulting direction. The ant never halts. A seam terminal state is not processed by the upstream segment; it is the next segment's entry.

The fixed period is

    S =576000
    V =240619037200
    rectangular periods (S,2V) =(576000,481238074400).

The two-row vertical period accounts for a horizontal shift S/2 between successive CA layers. All bits outside the explicitly painted finite-template instances are 0. `generator.py` specifies every lattice cell by a terminating random-access algorithm; no dense bitmap or guessed hardware word is used.

## One exact fixed source machine and cellular rule

The only machine data are the pinned 30-entry U15 table, including J1=null. Primary cellular states are 0 and 1 for headless tape bits, and 2+2q+a for head state q in A,...,O and scanned bit a. There are exactly 32 states; J1 has code 21. The center cell of a nonhalting head writes its prescribed tape bit. An incoming neighboring head supplies its prescribed next state. A center 21 remains 21, giving a frozen simulated halt. A left-arriving head has priority on malformed double-arrival triples; this arbitrary total extension is never used by a valid one-head simulation.

`radius_one_32_table.bin` explicitly lists all 32768 local triples. `radius_half_11_table_le.bin` explicitly lists all 4194304 pairs of 11-bit states. Primary a is coded by a. Pair(a,b) is 0 when a=b=0 and 1024+32a+b otherwise. The radius-half rule sends primary neighbors(a,b) to Pair(a,b), and sends consistent neighbors Pair(a,b),Pair(b,c) to the radius-one result g(a,b,c). Invalid cases have the displayed total default 0. Zero is quiescent in both phases.

Consequently, on a valid primary tape, two radius-half steps give one machine step and a one-site shift: if sigma(X)_i=X_(i-1), then F²(X)=sigma(G(X)). Induction gives F^(2t)(X)=sigma^t(G^t(X)). Translation does not change whether state 21 occurs. Odd CA times contain pair codes or 0, so they cannot contain primary 21. The simulated machine halts exactly when a computed primary cell becomes 21; it then remains encoded forever.

The actual Boolean cell takes xL,s 0,s 1,xR, with 11 bits per state, and computes

    (s 1, f((1-s 1)xL,xR), f((1-s 1)xL,xR), s 0(1-s 1)).

There are 24 input and 24 output bits. A862-gate NAND DAG computes complemented outputs from complemented inputs, as required by the physical NOT header/footer. It also computes h=[f(...)=21]. A separate vector-bitplane evaluator compares the DAG with the complete independent CA tables on all 16777216 assignments to the 24 Boolean inputs. Its receipt is `ca/complete_table_verification.json`.

The fixed U15 transition table is fully implemented. A compiler from an arbitrary program to a U15 pair is not implemented here; its published universality remains a separate source dependency.

## A complete physical Boolean instruction basis

Every full instruction round has old storage boxes at y 50, new storage boxes at y 450, an eastward control sweep at y 75 and a westward sweep at y 305. Column pitch is 600. The physical two-column instructions are

    NAND(p,q) =(not(p and q),0)
    DUP(p,q) =(p,p)
    MOVE_LEFT(p,q) =(q,0)
    MOVE_RIGHT(p,q) =(0,p).

A delayed-COPY tile preserves every nonselected column. The ignored input in DUP/MOVE may contain either bit and may already have been written; no read is performed on it. All output boxes are fresh INIT0 resources before any conditional write.

Each literal tile includes all initial/input-write cases, crossing orders, exact headings, intermediate board states, and optional later output reads. Independent interpreters verify the histories. The finite atlas checks all horizontal types, all potentially meeting vertical translates, both neighbor halos, and both edge-turn continuations. Vertical intersections are exactly whole 43-cell input/output box aliases. A box has one physical owner and one merged optional-WRITE then READ history, even when named by two adjacent stages. No pair of separately counted macro maxima is added at an aliased box.

The NOT header requires one additional reachable mode: columns skipped on the initial partial eastward sweep execute only their lower COPY. Their intermediate boxes remain INIT0, so this W-only mode produces 0 without reading the old input box. The modified left-start header also needs normal E-only input 0 when the preceding outer COPY was never activated, including the initial CA row and each newly exposed right edge. These modes must be included in the final local receipt.

The fact that some READ1 and union paths revisit cells is retained. The bound is two aggregate departures over an entire legal resource history, not self-avoidance of every path.

## Exact compressed finite Boolean program

At the abstract word level, adjacent DUP and NAND implement XOR with 3 duplications and 4 NANDs. Three XORs with 3 further duplications implement adjacent SWAP. A SWAP expands to 12 DUP and 12 NAND word operations.

A word DUP at position i is implemented physically by moving the suffix one position right, from right to left, then using the DUP pair. A word NAND is implemented by the NAND pair followed by moving the suffix left, from left to right. Thus no dynamic column positions or geometric data-wire crossings are required. The fixed physical column array is preserved.

To append a circuit gate, duplicate its first referenced wire, move that extra copy to the right end by adjacent SWAPs, do the same for the second wire, then NAND the last two. Every existing wire value remains in its old logical word position. Induction over the 862 DAG rows proves the compiled computation. The loop bounds prove this for arbitrary word contents; finite tests are regression for those identities.

For r=word_width-source_index, copying a wire to the end costs exactly

    DUP:12r-11, NAND:12r-12,
    MOVE_RIGHT:6r²-6, MOVE_LEFT:6r²+3r-9,
    total 12r²+27r-38 rows.

The final program gathers 24 uniformly spaced inputs, computes the DAG, copies its 24 selected outputs and h, performs one dedicated DUP on h, gathers the outputs and scatters them to the same uniform positions. The exact totals are

    NAND1365370, DUP1366258,
    MOVE_LEFT299589177, MOVE_RIGHT299226786,
    total R=601547591 instruction rounds.

The program is a finite arithmetic grammar with 958 records, not an omitted unspecified circuit. `physical_program.py` returns the exact instruction and adjacent column pair at any row index by interval descent. The independent ledger checks its closed-form counts and all column bounds. Physical active width is K=958 columns; selected input/output bits occupy active indices 0,40,...,920. The compiler prefix requires at most 917 entries (the independently audited exact peak is 915), and all scattered destinations remain below K. The two surrounding 600-cell columns are routing margins.

## Literal fixed C block

A C block has one all-NOT/header-COPY round, R full instruction rounds, and one NOT-footer plus outer-COPY round, hence height V=400(R+2). Its active body begins at x 600 and ends at x 575400. Each internal round's exact right/left connectors come from the checked benchmark atlas. Only fresh rows are entered, except for their declared input-box aliases.

The footer's right marker is selected column index 920, absolute column 921. Its joint right-stop NOT/COPY gadget computes the marker before choosing a branch. Marker 0 continues the eastward footer and later admits the ordinary westward copying visit. Marker 1 performs the output write, joins its own outer COPY, and exits to the leftward copy sweep. It never requires a missing crossover FIRST.

The left marker is selected output index 0, absolute column 1. Its joint COPY/header-NOT gadget either copies 0 and continues west, or copies 1 and immediately joins the next CA layer's s 1 header NOT. The next block is horizontally shifted by minus S/2, so that output column 0 is exactly the next block's selected input s 1 column 12. Every C input and output bit location therefore aligns with the alternating staggered grid. With fixed physical block indices, even-to-odd transfers output slots0–11 to block i−1 and12–23 to i; odd-to-even transfers them to i andi+1. This is a phase-dependent spatial reindexing of the logical F evolution. State21 occurrence is invariant under that translation, so physical C indices are not silently identified with the indices in F²=sigma G. All dummy-column copies are explicit; they do not encode source state.

Normal C completion rises on a dedicated right-margin channel and enters the next C header. Put e=575400 and F=400(R+1). The literal pieces are:

1. Even east strip, length 170, from(e,F+75,E)
2. Source left corner, entering(e+170,F+75,E) and exiting(e+175,F+69,N)
3. Even north strip, length F-10, ending(e+175,79,N)
4. Rotated source right corner, exiting(e+180,75,E)
5. Even east strip, length 1020, ending(S+600,75,E)

Its total length is 2F+2396 departures. Internal right turns remain at x≤e+61, while the long north strip lies at x=e+174 or e+175. The long north segment has exactly80≤y≤F+69, whereas footer E is atF+75. Previous outer-COPY ordinary output footprints end at y59. The preceding LEFT_MARKER extension is confined to x in[288600,289200], far from this right-margin channel. The top horizontal strip traverses only the right and next-left margin at y 74/75. These inequalities separate it from every internal round, both exceptional markers, the preceding outer COPY, and the next block's left returns. Its end cell belongs to the next header and is excluded from its own footprint. The two finite corner seams are explicit source ports; the long portions are the proved arbitrary-even-width cable family.

## Growing sweep and freshness induction

Suppose a CA row has a finite active word of m+j states. Its sole left marker s 1=1 is at block L; its sole right marker s 0=1 is at block R, with R-L=m+j. All intermediate marker bits are 0.

The leftmost block is entered at its s 1 header, skipping only the xL,s 0 prefix. The Boolean cell ignores that prefix under s 1=1. Its header W-only columns are explicitly certified. Every later block is entered normally, and all internal instruction rounds are complete. The last block writes the right marker and diverts after its final meaningful output, rather than escaping into uncomputed hardware.

The outer westward sweep copies the complete computed output interval. All intermediate left-marker tests are 0. At the sole copied s 1=1 it joins the next layer's header. The next active word has one extra state, with left edge shifted left S/2 and right edge shifted right S/2. Newly exposed outside inputs are still quiescent INIT0. The modified normal header E-only 0 case covers an outer COPY that was never used. This proves the same invariant for the next CA layer.

For any finite number of layers the schedule uses finitely many finite operations, and every complete layer has a next layer. It continues after source halt because 21 is frozen only in the simulated CA, not in the ant controller.

Owned supports of distinct nonalias resources are disjoint by the finite template atlas, the bounds on exceptional columns, and the margin inequalities. The only temporal overlaps are input/output boxes whose chronological projections are optional WRITE followed by at most one READ. A crossing receives FIRST before any SECOND; a union uses one incoming alternative. Therefore the unique physical ant run is the concatenation of those certified histories. Every physical cell is processed at most twice over the entire infinite run. Every arrival is eventually followed by departure, so the same bound applies to visits, including the initial site. This is the global induction; bounded trajectory tests alone are not its proof.

## Literal finite loader and fixed start

Input consists of two finite binary words ell,r, both nearest-head-first. Form the primary CA word

    reverse(ell), head(A,0), r.

Its length is m=len(ell)+len(r)+1≥1. For each state a_i, its bit b is placed in block i at selected input slot 13+b and in block i+1 at selected input slot b. Selected slot k is the source box at x=iS+600+600·40k+100,y 50. A logical 1 changes its two state cells by setting(x+4,54),(x+5,54) to color 0. State 0 changes nothing.

Set the left marker in block 0, slot 12 and the right marker in block m, slot 11. This explicitly uses the word lengths even when every tape bit is 0; the endpoint marker is never omitted.

Initialization also applies the fixed 2806-cell anchor in `copy/fixed_initial_anchor_patch.json`. It is the exact net board change after a verified virtual COPY1-to-header prefix, translated by(288600,-400). That prefix did not physically run. The actual ant starts at its unprocessed endpoint

    (288650,75,E).

All expected anchor colors have been checked against the complete global generator. The actual startup is a suffix of the certified local history, so deleting the virtual prefix cannot increase any physical visit count. The two virtual source-INIT1 setup flips cancel during its read and are not applied a second time.

The anchor occupies x in[288617,289200], y in[-144,76]. Among raw input fields it meets only the left marker's two state cells, already set to the same new color 0. All state copies occupy distinct selected fields; the right marker is in block m≥1 and is disjoint. Therefore the total number of changed cells is exactly

    2806 +4·(popcount(ell)+popcount(r)+1)+2
    =2812+4·(popcount(ell)+popcount(r)).

The +1 is the A0 head's single set bit, producing four cell changes. The final +2 is the right marker. The left marker is already included in the 2806-cell anchor. Zero-only words still change the right marker position through m, with the same support cardinality. No uncounted anchor or free input-dependent tile is assumed.

## Fully literal accepting event

Use pre-departure snapshots. Accept if the incoming heading is S=2 and either

    x mod 576000 =546702,
    y mod 481238074400 =240606225650,

or

    x mod 576000 =258702,
    y mod 481238074400 =481225262850.

There is no color stencil. These are two residue/heading clauses, not a fixed-site return condition.

The dedicated instruction is program row 601515562, active column 910. Its input is exactly the uncomplemented h=[f=21], copied after the entire fixed Boolean DAG has been evaluated. This is DAG wire885, the output of zero-based gate861=NAND(884,884). The last COPY-to-end node has width910 and source885; its8137 physical rows put h into column910. A separate checker eagerly expands all8137 rows, matches them to the random-access decoder, proves no unused workspace bit is read, and verifies the transported value on all16777216 inputs. No footer NOT intervenes. See observer_polarity_receipt.json. The chosen cell is the first output box's WRITE entry in that row's DUP tile. Every local case visits this entry with heading S exactly once when h=1 and never when h=0. The eastward pass never reaches it. A later READ of that same box never visits its WRITE entry. The next instruction row therefore cannot create a second or false accepting event at the aliased cell.

The two clauses are exactly the two staggered CA-layer translations of this resource. Apart from the just-described next-row shared-box alias, all other body rows have different vertical phase. No initialization, header, footer, marker turn, or partial-layer route has that phase at that column. The only route traversing old instruction heights is the normal C rising channel, confined to the far-right margin; it misses the accepting column. Initial input changes are at y 54 and the bounded anchor is near y 0, and the actual start has y 75, so initialization itself cannot satisfy either clause. Partially entered C blocks still execute the complete fixed program; their skipped inputs are ignored by the s 1 branch. An incomplete earlier phase has no route into the observation row. Acceptance itself occurs before the observer DUP and the footer have finished; this is sound because h was already computed and copied exactly. Their future completion is not an assumption needed for acceptance soundness.

Thus a physical accepting event occurs if and only if some computed CA output is primary 21, which holds if and only if the supplied U15 configuration reaches J1. On valid primary-loaded runs, the even computation layer's clause is in fact never used, since odd CA outputs are pair states; retaining both clauses gives the uniform two-phase description without admitting false visits.

## Quantitative scope and the arithmetic boundary

The initialized support has the exact cardinality above; coordinate magnitudes grow linearly with m times the fixed S. For T computed CA rounds, the number of C evaluations is

    T(m+1)+T(T-1)/2.

Each C has a fixed finite number of control steps, bounded from the finite macro maxima and R, plus the explicit 2F+2396 margin route. An explicit bound is |x|≤S(m+T+2), with -144≤y≤V(T+1)+659. The initialized support lies in[288617,576000m+264705]×[-144,76]. A conservative per-C departure bound is 15274393040715416, obtained by taking 26394 departures for any finite resource history and adding the exact long margin route; atlas/quantitative_ledger.json gives the complete formula. These are deliberately loose upper bounds, not optimized costs. The generator itself stores a finite template family and 958 program records, rather than a board with S·2V entries.

To match the existing north-facing bounded-board convention, rotate counterclockwise and subtract the rotated fixed start:

    X=y-75, Y=288650-x, heading E→N.

The start is(0,0,N); its checkerboard parity is even. Accepting headings become E on odd-parity cells. The normalized periods are(481238074400,576000), with acceptance residues

    (240606225575,317948,E),
    (481225262775,29948,E).

Period-multiple translations preserve those residues and can place any finite prefix inside a sufficiently large odd-width/even-height board. This geometric alignment does not construct the arithmetic initial word for free. No 174-operation composition or additional operation budget is claimed in this packet; the raw input, phase/anchor, bounds and accepting endpoint constraints must still be fully paid.
