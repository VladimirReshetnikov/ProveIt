# Independent audit of the structured coefficient prefix

## Verdict

**PASS for the exact constant-prefix construction, with the scope limits below.**

The inspected new compiler constructs all 1,152,598 fixed coefficient labels used by the authenticated Report44 stream from literal `1` and literal `3`, using only addition, subtraction and multiplication. Its exact cost is

- 13,182,377 multiplications
- 15,898,997 additions or subtractions
- **29,081,374 total operations**

The independent validating sink traversed every emitted gate, verified every operand was a permitted literal or earlier gate, and reproduced the canonical stream SHA-256:

`6a01d7c1d8ee6b268d49c921b3263b578c152e49c62810d5aa877a4103cb9759`

No mathematical defect was found in occurrence compression, finite ownership, signs, coordinate orientation, period cutting, geometric sums, power charging or shared-node accounting. This conclusion is supported by exact mathematical identities and exhaustive finite JSON-map checks. The all-label modular check is supplementary, not a probabilistic substitute for those identities.

The independently counted prefix plus the unchanged Report44 variable source gives 31,388,831 operations for two raw inputs and 31,388,841 for one raw input. At the time of this audit these two sums are a formally justified splice ledger; actual full joined-stream validation is being conducted separately. This audit does not claim a materialized complete joined stream, ant simulation, fresh proof of the inherited ant theorem, novelty, optimality, or a new upstream execution.

## 1. Execution and source boundary

The frozen atlas generator, physical-program specification and Report42/44 initialization sources were first inspected as text. Their upstream Python, color recipe, physical ant and Boolean-tape routines, and saved schedules were never imported or executed.

Executed work consists of new audit scripts, the inspected newly authored symbolic prefix compiler, and its new finite JSON-map union helpers. The occurrence analysis reads the finite compressed JSON description as data and performs algebraic/count analysis. It neither obtains nor applies an expanded physical row schedule. The independent count checker does not use `prefix_rows`.

`check_emitted_source.py` imports only the new prefix compiler and its new helpers, replacing its arithmetic sink with independently authored validation/count/hash/modular-evaluation code. This is actual traversal of the new arithmetic source, not execution of a saved arithmetic schedule. It does not expand the enormous fixed integers.

## 2. Exact occurrence identity and count

For a monotone run starting at time n and slot s, direction d in {-1,1}, length L, place events +Z^n at s and -Z^(n+L) at s+dL. A sweep in direction d with value(s)=Z value(s-d)+event(s) gives Z^(n+k) at s+dk for 0<=k<L, and zero thereafter. This follows directly by induction; addition gives the result for any collection of runs. A terminal event outside the owned slot interval has no effect inside it. The synthetic checker verifies 2,912 exact coefficient-dictionary instances, including both directions and edge sentinels; the induction proves the unrestricted identity.

The candidate's finite 24-word interchange was parsed as a literal and compared with the independently composed XOR/interchange specification. Its WORD, COPY, GATE, RANGE and ROW lowering matches the inspected fixed grammar: a DUP word is the reverse MOVE_RIGHT run followed by its DUP; a NAND word is its NAND followed by the forward MOVE_LEFT run; copies concatenate interchanges in the prescribed order. The compiler advances its time wire exactly once per nonempty run. Thus each fixed row contributes exactly once to one kind/slot occurrence polynomial.

The independent count uses distance histograms, not row enumeration. A copy at distance d has length 12d^2+27d-38. It contributes one DUP word at d and one interchange at each distance d,d-1,...,2. Aggregating these histograms gives exactly:

- 5,456,442 runs, comprising 2,724,814 directional and 2,731,628 singleton runs
- 2,730,765 words, 113,709 interchanges and 1,749 copies
- 601,547,591 rows and 845 cached lengths including 0 and 1

With K=957 and lambda(n) the binary-chain cost, the exact occurrence ledger is

M = lambda(400) + runs + 4K + sum_cached_L>=2 lambda(L)

A = 1 + singleton + 2 directional + 6K

The cached-power sum is 9,705; the result is 5,469,985 M + 8,186,999 A = 13,656,984 gates. Top-level boundary hash and every metric match the reported compiler receipt.

## 3. Finite ownership and no duplicated digits

All source board lists were checked for distinct coordinates and binary colors. NAND was independently formed as the color-compatible union of the raw NAND map and the two shifted COPY maps.

The independent black-set subtraction gives these pair-minus-two-DELAY corrections:

- DUP: 1,520 additions, 1,884 removals
- MOVE_LEFT: 1,424 additions, 1,814 removals
- MOVE_RIGHT: 1,495 additions, 2,001 removals
- NAND: 3,447 additions, 2,505 removals

Every coordinate in every published signed correction mask was independently compared with these differences. Every match is exact. Corrections lie in y=56..449 (NAND y=57..297), do not intersect the external neighboring DELAY tiles, and therefore cannot cross the canonical 400-row boundary. Signed differences are applied to the baseline, rather than incorrectly unioning an operation's black support with the baseline.

Across 175 relative vertical motif comparisons, all 65 nonempty overlaps have agreeing colors and the same 43-cell/23-black per-slot seam. The seam is owned by the following canonical band. Since operation-minus-baseline vanishes on it, adjacent rounds cannot duplicate or erase it.

The H/B/F data were then independently reconstructed by projecting generic finite macro placements onto owned 400-height windows. This reconstruction does not reuse the candidate's hand-selected boundary component lists: it retains all intersecting motif placements, checks both white and black occupancy, then unions. Synthetic R=2 suffices because it includes a first bulk band, a last bulk band, header, footer and both neighboring macro phases; the finite motifs have bounded height, and the wire intersection is linear in the window. Every true R>=2 has exactly these local configurations and translated copies of the same bulk band.

Every one of the 576,000 columns of H, first B, last B and F agrees with the candidate data. There are zero color conflicts. Unique black counts are H=2,935,465, B=2,695,878 and F=2,936,770. This comparison includes the crucial predecessor LEFT_MARKER tail at slot 481, the omitted current NOT, and the modulo-horizontal seam. F uses 246 distinct nonzero masks; its dictionary also reserves a zero mask, so its dictionary size is 247.

Consequently the baseline has exactly one owned Boolean coefficient per physical cell. At each program round exactly one operation correction replaces the two selected baseline tiles. The corrected coefficient remains the literal target color 0 or 1, so the argument does not assume that a redundant signed expansion is already carry-free. It proves equality of each coefficient before radix substitution.

## 4. Coordinate and cut identity

Let physical horizontal coordinate be a and physical vertical coordinate b. Report42/44 uses normalized coordinates X=b-75 and Y=288650-a. Accordingly `tile:j` must encode the physical column a=288650-j modulo S, with exponent b-75. This is the candidate's exact index map. `first:j` is the same column at b=75, which is bit 25 of H.

With V=400(R+2), u=2V, canonical H begins at physical b=50 and F begins at b=V-350. The full first macro relative to b=50 has length V. Cutting its first 25 rows leaves length V-25. The second macro, shifted horizontally by S/2, then occupies exponents V-25 through 2V-26. The wrapped first 25 H rows occupy exponents 2V-25 through 2V-1. These intervals are disjoint and partition all u exponents.

For bulk U=B(1+Z+...+Z^(R-1))+C, this yields exactly

Full = H + Z U + 3^(V-400) F

Cut = Hhigh + 3^375 U + 3^(V-425) F

Tile[a] = Cut[a] + 3^(V-25) Full[a-S/2] + 3^(u-25) Hlow[a]

Hence every `tile:j` equals the prescribed alpha_j. The Hlow/Hhigh split is made from fixed digits, never by division of a runtime value. The backward half-shift equals the forward half-shift modulo S, so the orientation of the staggered macro is correct.

## 5. Every old label and every paid constant

The checked label set is exactly:

- 576,000 `tile:j` labels
- 576,000 `first:j` labels
- 584 `anchor:j` labels
- Cu, Cx, Cbase, C198, EndpointK and EndpointD
- literals 0, 1, 2, 3, 4, 6, 8 and 9

It has no missing or additional label. The anchor JSON has 2,806 distinct changed cells, 1,401 positive and 1,405 negative changes. The coefficient contribution is `(new-old) 3^(b+144)` at row `289200-a`, with exponents in the exact bounds 0..220 and 0..583. All 584 signed 221-digit Horner rows are retained and paid.

Zero is 1-1, minus one is zero-1, and two is 1+1. Four, six and eight use paid additions; nine is a paid multiplication. Cu=3^u, Cbase=3^(u-219), C198=3^198 and EndpointK=3^481225262775 use paid binary chains; Cx=Cu-1 and EndpointD=Cx-1 use paid subtractions. Minus one is used for signed digit construction, though it is not a separate old output label.

The independent sink evaluated every gate modulo 1,000,003 and checked all 1,152,598 labels against a separately assembled formula/data evaluation. All pass, and the output-alias hash agrees exactly. This modular result is supplementary evidence, with its limitation stated explicitly.

## 6. Complete ledger and limits

Independent closed counts and actual source traversal agree in every stage:

- Occurrences: 13,656,984
- Small profiles/basic literals: 648,926
- Geometric sum/fixed shifts: 328
- Operation corrections: 6,454,008
- Bulk/boundary/period join: 8,064,000
- Anchor rows: 256,960
- Remaining named constants: 168

The profile cache has 736 nonzero signed/unsigned 400-digit entries, 21 25-digit entries and 81 375-digit entries, for 838 shared entries. Their Horner costs are 324,462 M and A each; the two additional basic-literal additions are charged. There is no inferred sharing beyond the explicit cache. Operation corrections have exactly 957*(763+1159+678+772)=3,227,004 M and the same A. The final per-column assembly has seven M and seven A for each of 576,000 columns.

The geometric-sum algorithm uses only the exact identities P(2n)=P(n)^2, G(2n)=G(n)+P(n)G(n), followed for an odd extension by G(2n+1)=G(2n)+P(2n) and P(2n+1)=P(2n)Z. Its output power is paid even when the caller discards it. All fixed shifts are charged binary chains.

Every added wire is a fixed constant expression, so the substitution introduces no witness or equation and cannot change variable degree. The inherited degree remains 2,304,000 under the existing Report44 proof. Inherited ant dynamics, history correctness and recoder assumptions remain inherited: this audit proves the replacement coefficient construction, not those external theorems.

## Artifacts

- `check_independent.py`, `receipt.json`: exact event checks, compressed-data count, motif/seam/sign and all-Q checks
- `check_profiles.py`, `profiles-receipt.json`: separate finite projection and every-column comparison
- `check_emitted_source.py`, `emitted-source-receipt.json`: independent literal/reference/opcode sink, full hash/count and all-label modular comparison
- `closed-count-receipt.json`: independently recomputed complete stage ledger
- `MANIFEST.json`: audit artifact hashes

The checker paths currently target the inspected prototype inputs. This is an audit bundle, not a claim that its checker installation is independently relocatable. The construction's separately packaged release has its own source closure and replay checks.
