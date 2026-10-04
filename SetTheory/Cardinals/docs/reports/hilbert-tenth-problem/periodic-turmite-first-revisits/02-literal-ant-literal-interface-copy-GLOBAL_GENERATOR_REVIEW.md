# Independent global color-generator review

## Finding

PASS for the reviewed finite-template selection, literal-color compatibility, partial-header cases, staggered storage alignment, normal C-to-C rising channel, and exact fixed initialization anchor. No remaining route or index bug was found. `global_generator_review.json` pins the exact generator, program and supporting receipts reviewed.

This finding separates three arguments:

1. Actual-color evaluation over263,525 finite template/box/anchor cells checks both stagger parities, every960-column next-layer top-box row, each exceptional marker, header boundary classes, instruction-template classes, and finite margin pieces
2. A symbolic selector and interval argument covers all other translated rows/columns and every cell of the enormous north strip
3. `program_audit/` independently proves every decoded instruction index and arithmetic interval, rather than substituting random or representative tests for601,547,591 program rows

The observed1,974 multiply-painted groups are complete43-cell storage boxes with matching colors. No non-box ownership overlap or triple painter was found. The finite neighbor atlas and symbolic selector reduction extend the local compatibility result to all program placements.

## Exact program and selector coverage

There are958 compressed records and601,547,591 physical pair rounds. The independent grammar audit gives pair-left indices0…919, so the highest touched active column is920, within active columns0…957. The exact live compiler peak is915; the declared917 is a valid conservative bound. Gate, COPY, SWAP and WORD interval branches, plus gathering/scattering and the observer row, are independently checked arithmetically. The geometry review's real-row template witnesses are class tests only, not its claimed exhaustive index proof.

All macro resources lie within local Y=[50,V+259] and X=[0,S+599]. Hence the true painter lies in the generator's three neighboring CA-row and CA-column candidates. At a full-round cell, floor((Y−50)/400) differs from the true round by at most1. A width600 slot's boundary cells belong to k0 or k0−1. Pair instructions are added exactly once and replace both consumed delayed-COPY slots. These observations justify the selector loops, including negative global coordinates and exact seam cells.

The omitted header NOT is precisely column481. The preceding staggered LEFT_MARKER supplies its modified header operation. Every header COPY remains present. Two reachable partial modes have separate exact certificates:

- W-only NOT_PAIR after permanently skipped upper E: old input is untouched; the unmodified intermediate0 is copied to final0
- Normal LEFT_MARKER header-E-only0 with no prior old COPY: current header input0 is read normally and header output1 is written; no missing COPY FIRST is required

`header_entry_only_receipt.json` contains nine histories for the latter mode: unused old-source INIT0, INIT1 or priorWRITE0, followed by stopping, output READ1, or next header COPY plus READ1. Every aggregate bound is2.

## Staggered CA alignment

S=576000, V=240619037200, B=40 and S/2=12·B·600. A selected footer output slot t has x=600(1+40t) relative to its C origin. Relative to the next staggered row, its selected input slot is t+12 modulo24:

- output0 (s1) becomes input12 (s1)
- outputs1…11 become inputs13…23 (right state)
- outputs12…22 become inputs0…10 (left state)
- output23 becomes input11 (s0)

For even→odd physical block indices, slots0…11 go to next block i−1 and slots12…23 to i. For odd→even they go to i and i+1. Thus the comparison to a fixed-index one-sided radius-half CA includes the corresponding phase-dependent reindexing. This is harmless for existence of state21, which is translation invariant.

Vertically, F=400(R+1)=V−400. Ordinary outer COPY output F+450 equals next header input V+50. The LEFT_MARKER header output F+650 equals the next header COPY input V+250. These are whole literal source-box aliases, not merely centerline coincidences.

## Normal rising channel: proof for every long-wire cell

Put e=575400 and F=240619036800. The five owned-support bounding rectangles are:

| Resource | x interval | y interval |
|---|---|---|
| bottom east strip | e…e+169 | F+74…F+75 |
| source E→N corner | e+170…e+176 | F+70…F+75 |
| north strip | e+174…e+175 | 80…F+69 |
| source N→E corner | e+174…e+179 | 74…79 |
| top east strip | e+180…S+599 | 74…75 |

They are pairwise disjoint. Exact head states at the seams are

`(e,F+75,E) → (e+170,F+75,E) → (e+175,F+69,N) → (e+175,79,N) → (e+180,75,E) → (S+600,75,E)`.

The finite strips and corners are reconstructed and independently replayed. The north strip has even length F−10. For every integer Y in[80,F+69], its x=e+174 cell is color0 and x=e+175 cell is color1. Direct substitution in the generator's wire formula gives longitudinal coordinate a=F+69−Y in0…F−11 and lane b=x−(e+175)+1 in{0,1}. Thus the formula specifies every long-wire cell exactly; no sampled-height argument is used.

The following uniform inequalities rule out every other painter:

- Active body resources satisfy x≤e; internal right turns satisfy x≤e+59, both strictly left of the north strip
- The outer right-guard COPY begins at y=F+250, strictly below the strip's last owned row F+69
- The next CA row begins at y=V+50=F+450, also below the strip
- Previous ordinary outer-COPY and RIGHT_MARKER output footprints end at current y59
- The only previous-CA-row extension reaching current heights80…259 is LEFT_MARKER, whose horizontal interval modulo S is[288600,289200], strictly left of the north strip
- Previous same-row C painters can extend only to current x600; the next C starts at x=S. The north strip lies strictly between them
- The top east strip ends at S+599; the next C's first active header entry is exactly(S+600,75,E), excluded from the strip

The two corners use19 and17 cells. The even strips use twice their lengths. Total channel cells and departures are2F+2396=481238075996, each processed once. The schedule's one-use property remains a controller claim; the static geometry does not silently assume it.

## Anchor and proof review

All6193 cells of the translated left-start marker's baseline agree with the actual global evaluator. All2806 expected old colors in the fixed patch agree too. Starting at(288650,75,E), the sparse changed-color map plus global background reproduces the exact1276-step certified suffix, ending at the next header-column entry(289200,75,E), with maximum2 departures.

The corrected metadata distinguishes the unused ordinary slot entry(288600,75,E) from the actual fixed head(288650,75,E). The old mismatch was metadata only and is no longer present in the reviewed source hash.

The loader cardinality2812+4(popcount(ell)+popcount(r)) follows because each tape/head1 bit changes two distinct two-cell source fields; the A0 head has one set bit; the right marker adds2; and the left marker's two changes already belong to the2806-cell anchor. The anchor bounds and its sole overlap with raw-input marker fields are checked exactly. No virtual INIT1 setup flips are added again after taking the net patch.

The accepting-write proof correctly singles out the observer DUP's first output WRITE entry. Its false branch, E pass, subsequent READ and following-row input alias cannot produce that state. The normal rising channel crosses old observation heights only in a different far-right x interval. Header/footer/marker phases differ from the observation phase. This geometry review is conditional on the separately checked CA truth-table/DAG and h-transport/polarity certificates, rather than claiming to replace them.

The reviewed global proof's earlier wording has been corrected to call917 a bound with exact peak915, state the north strip's true y interval, and exclude the already-handled next-row alias from the phrase “all other rows have different vertical phase.” No further geometry/controller-stitching overclaim was found. Logical-machine universality remains the proof's explicit published-source dependency; arithmetic composition and its cost accounting remain outside this review.

## Reproduction

Run `python review_global_generator.py` and `python verify_header_entry_only.py` from this directory. The compressed program's independent verifier is `python program_audit/verify_program_index_bounds.py`. The current finite atlas compatibility receipt has been regenerated after the strip update and has no stale source pins.
