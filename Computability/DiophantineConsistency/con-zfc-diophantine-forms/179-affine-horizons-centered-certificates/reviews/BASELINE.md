# Round 22 immutable comparison and calibration audit

**Pin:** `5274bc751a1566879ddc028a2d2a2af3c031654a`, compared with the bounded round21 late pin `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb`. No upstream source edit or remote write. `audit_baseline.py` independently recollects **91 complete residual-square expansions**, authenticates the incoming archive identities, and reconstructs the entire maintained coefficient tuple and finite Pcs arithmetic.

## Findings that change the comparison

1. **The strongest inspected direct quartic dimension is now 216 unrestricted integers**, from incoming *Pooled Projection*, not our delivered217. Its exact tuple is **216 variables /153 rows /15,158 terms /334,952 height**. It trades lower dimension/row count against our217 endpoints' much lower heights and the sparse217 endpoint's lower support. The new215-variable source168 point has **degree10**, not4.
2. Incoming *Quotient Carriers* adds genuine low-height direct tradeoffs, especially **220/157/8,847/2,336** and **220/157/8,018/3,597**. Its217/154/19,112/5,184 and217/154/18,148/5,888 points lie between our two217 support/height endpoints. Do not claim a global coefficient minimum from the old3,840–4,576 comparators.
3. Our round21 *Pooled Powers and Separated Radicals* archive is now in the incoming queue, **byte-identical** to the delivered7,871,808-byte ZIP, SHA256 `6c5563cb14fe31413a41ff7d34ba8ff66b0720b697440f3193989740ea9a6a88`. This is arrival, not placement or adoption. Sources166–168 are separately placed new work.
4. The maintained display is **Start-marker4177**, with **15 strictly positive variables /66 integer-leaf binary operations /degree157 /98,219 raw coefficient bytes**. Its physical zero-weight marker is at1048;1048 is not a separate smaller tuple. Full new-K Pcs is discharged. All four ports changed coherently from6007; the free-port66 DAG did not.

## New mathematics behind the new artifacts

The following are source-level changes, not README-only titles. They are ordinary proof constructions relative to retained calibration, not newly replayed formal kernels.

- **166, Fixed-base modular:** `proofs/FIXED_BASE_PROOF.md` changes the arithmetic front to `R=16^t`, `B=binom(R+t,t)` and Horn weights `1+jB`. `proofs/MODULAR_PROOF.md` then retains six exact power requests and replaces eleven numerator powers by signed modular Pell evaluations at a common freely chosen center, with complete frame and signed-bootstrap changes. Its final229/230-variable quartics are not new dimension records but the230-variable point is sparse (4,482terms,height7,968).
- **167, Integral projection:** exact integral common-quadratic-direction and affine restorations of the pooled225 system give218/155/14,410/5,023,040 and220/157/7,793/45,161. New *Pooled Projection* combines157's factorial-free source with158's strict ranges/pools before applying the projection method; its literal `algebra/equation216.json` and `equation218.json` are distinct from167 and must not be missed by an `equation.json`-only scan.
- **168, Reciprocal pooling:** `proofs/RECIPROCAL_POOLING.md` replaces two consecutive-base pooled congruences by one reciprocal sum whose denominators have the same sign. The common-denominator bound makes the rational sum an integer of absolute value below1, forcing every squared error to vanish. Three coordinates/rows disappear at the cost of a degree-five residual and degree-ten final polynomial. This is zero-existence equivalence with integral restoration on solutions, not a global polynomial coordinate bijection.
- **Incoming Quotient Carriers:** the direct branch composes inherited radical projection, exact affine elimination and reversible residual-basis optimization; credit for the inherited radical method is explicit in `direct/RADICAL_PROOF.md`. Its compact branch removes the index quotient by a new auxiliary Pell residue, on the retained **radix67** tuple. `compact/FIXED_CARRIER_PROOF.md` has13-positive70/206,71/162,72/154 and12-positive74/438 points. These are not13 or12 unrestricted-integer points and not current4177 specializations.

## Literal direct comparison points

All rows below have exact degree4 unless marked otherwise. Tuples are **(variables, residuals, collected terms, coefficient height)**. Every listed new equation's full expansion, including all coefficients and coordinate liveness, was independently recollected; hashes are in `BASELINE.json`.

| Domain and artifact | Tuple | Role |
|---|---:|---|
| Z, incoming Pooled Projection `algebra/equation216.json` |216,153,15158,334952|Smallest inspected quartic dimension|
| Z, our incoming `integer/integer217` |217,154,25949,4576|Low-height217 endpoint|
| Z, our incoming `integer/integer217_sparse` |217,154,14615,16866|Sparse217 endpoint|
| Z, Quotient `direct/pooled217_height5184` |217,154,19112,5184|New intermediate height/support|
| Z, Quotient `direct/pooled217_height6144` |217,154,18148,5888|Actual height5888, not filename6144|
| Z, Pooled Projection `algebra/equation218.json` |218,155,7726,45161|Sparse218 alternative|
| Z, Quotient `direct/pooled218_height4576` |218,155,16706,4544|Actual height4544|
| Z, Quotient `direct/pooled219_height4576` |219,156,10508,4544|Support tradeoff|
| Z, Quotient `direct/pooled220_height2736` |220,157,8847,2336|Strong new low-height comparator|
| Z, Quotient `direct/pooled220_height4408` |220,157,8018,3597|Sparse/lower-height comparator|
| Z, Quotient `direct/pooled220_height7968` |220,157,7858,6272|Further support tradeoff|
| Z,166 `equations/balanced` |230,176,4482,7968|Very sparse new source|
| Z,168 `equations/decic215` (**degree10**) |215,152,99914,113304|Not a quartic comparator|
| N, our incoming `natural/natural202` |202,154,9818,239204765|Strongest inspected natural dimension|
| N, our incoming `natural/natural202_lowheight` |202,154,12706,31145294|Same dimension, lower-height alternative|

The91-artifact Pareto flags in JSON concern that bounded set only; duplicate equations and intermediate controls are included. Earlier sparse/low-height points remain relevant. No global optimum is asserted.

## Small-variable comparisons and domains

The live operation model is binary `+,-,*`, including squares and scalar multiplications, with fixed **integer** leaves free. This is not bit complexity or a model permitting free rational constants.

- **Ten positive:** our85operations/232degree and77/348 remain retained matched endpoints. Existing trace75/402,76/352,79/290,80/258 are genuine tradeoffs. Incoming Quotient's12/13-positive results do not dominate these on variable count. Whole coefficient tuples are part of each source claim.
- **Thirteen unrestricted integers:**152degree/119operations remains a strong matched point;156/117 is another degree/cost tradeoff.
- **Fourteen unrestricted integers:**82/113,86/112 and88/110 remain relevant, as in the round21 audit.
- **Twelve unrestricted integers:** our512/132 is a fixed-count tradeoff versus500/139 and1084/123, but already dominated across counts by eleven-integer398/121 and328/130. Incoming12-positive438/74 does not change this unrestricted-domain assessment.
- **Eleven unrestricted integers:** source135 `scalar/weak_cofactor11_none.json`398/121 and `free_cofactor11_sharp.json`328/130 remain required comparators; source153298/150 is the lower-degree/higher-cost point.

The four new Quotient compact circuits were replayed successfully using their dedicated checker in normal and optimized Python, including full homogeneous leaders, all actual fixed numeral bindings and negative controls (`QUOTIENT_COMPACT_{NORMAL,OPTIMIZED}.json`). The simple independent DAG recount authenticates their live operations but intentionally reports its naive degree overestimate: the main Pell norm has a leading cancellation. This is not a degree failure; use the dedicated full-leading-form receipt rather than pretending tropical degree arithmetic suffices.

## Exact maintained tuple and its boundary

The following complete big-endian ports all match their raw hashes, compressed hashes, bit lengths and declared byte counts:

| Port | Bits | Raw bytes |
|---|---:|---:|
|K0|196790|24599|
|MC|196319|24540|
|MF (shifted source mask)|196320|24540|
|beta|196319|24540|
|**Total**||**98219**|

The audit independently reconstructs K,MC,beta and `MF_source=MF_native+beta` from the published full coefficient array and closed formulas. It also checks all current manifests/top-level display hashes, identical free-port source graph to6007, and exact preservation of the previous current record.

**Physical support is not coefficient support.** Es has980 positions but only977 nonzero weights. Dummies990/991 and marker1048 have zero weight. `Psi(rho,1)` retains the marker; `Psi(rho,2)` erases only its weight. Removing1048 because its Phi coefficient is zero destroys the masks, upper-predecessor identity, phase argument and complementary populations. Current finite negative controls explicitly catch this omission.

For exact currentK, the independently rechecked controller is `L=4177`, `d=196319`, `lambda=224113`, with orders23/87, spacing2001 and `Hs=1+BK+B²` residues **9,2620,158694** modulo47,4177,224113. The finite certifier passes normal and `-O`, with exact certificate hash `b3e1368f3918e8a3371e11aed9746c2369e8770c9aaa2496b4cf797f3b85b8f8`. The ordinary proof hash is `1db36f130e31087e751b2c83f9988ba4dda34e4f7525d5c9514766238858386e`.

This verifies finite source/port/controller coherence and replays the supplied finite checker. It does not re-prove every inherited unbounded native/Pell/refutation contract. A new compact4177 specialization must preserve the complete ordinary proof interface and all four ports, not transfer one oldK controller certificate or identify distinct specialized polynomials.

### Reproducibility caveat: gzip header portability

The unmodified current `build.py` read-only replay fails its compressed-byte comparison in this Python environment: regenerated gzip files use OS header byte03 where the stored files useff. Raw integers and payloads are unchanged. `CURRENT_BUILD_PORTABILITY.json` records all four byte comparisons and an explicitly labeled in-memory compatibility replay with that header normalized to255; no frozen file is rewritten. The original-script failure must not be called a pass or a mathematical contradiction. Finite certification, raw tuple reconstruction, and stored-manifest authentication pass independently.

The maintained display remains separate from every research comparison. No silent port replacement, adoption or formal-kernel claim is made.
