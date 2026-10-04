# Independent audit: horizon-free binary target-firing certificate

Date: 4 October 2026. Verdict: **PASS for the stated eleven-field raw physical-code relation, conditional on the explicitly pinned constructive Pell theorem dependency inherited from the accepted arithmetic macros.** No mathematical or emitted-source defect was found.

This approval is for existence of a finite **legal binary prefix** firing the supplied target. It is not an ordinary unrestricted target-firing theorem, a stabilization theorem, a universal-loader identification, a raw-program compiler theorem, a finite-fold representation, or a real-witness equivalence.

The submitted packet is `/workspace/shared/sandpile-target-firing-20261004`. All submitted files were treated as read-only data. Neither the submitted builder nor any submitted checker, upstream script, historical schedule, or Lean program was run or imported. The JSON DAG was normalized as inert formal polynomial syntax, not numerically evaluated on witness assignments. All numerical experiments ran newly written code in this audit directory. A second independent semantic review and its own fresh tests are preserved in `SEMANTICS.md`, `semantics_check.py`, and `semantics-receipt.json`.

## 1. Exact accepted theorem

Let `InputPlus` be a positive integer. Decode `InputPlus-1` using ten right-associated Cantor pairings into the natural fields

`(p-1,q-1,r-1,T,d-1,e-1,f-1,D,zeta_x,zeta_y,zeta_z)`.

The six dimensions are positive. The base-32 tile code `T` has exactly its declared `p*q*r` slots and digits 0 through 5; the finite patch code `D` has its declared `d*e*f` slots and digits 0 through 15. Leading zero slots are permitted; nonzero digits outside the declared arrays are not. The tile defines a periodic configuration on Z^3. The nonnegative patch is added at physical coordinates `[0,d) x [0,e) x [0,f)`.

For each axis the natural coordinate code `zeta=2h+s`, `s in {0,1}`, represents the signed integer `h-2sh-s`. Thus codes `0,1,2,3,...` represent `0,-1,1,-2,...` uniquely.

For the literal emitted integer polynomial `P`, the accepted equivalence is:

> There exist 3,308 strictly positive integer witnesses with `P(InputPlus,w)=0` if and only if the decoded physical instance is valid and admits a finite legal toppling sequence containing the decoded target, with every lattice site toppled at most once.

The polynomial has **exact total degree 18**. Its emitted implementation contains **14,778 binary arithmetic gates** under the declared convention that fixed integer literals are free. There are **1,923 squared residuals**, with **118 POWER, 30 Sub, five AND, and four SPREAD** calls fully expanded into those polynomial gates. Arity and literal source shape are independent of physical dimensions, box size, time horizon, and target coordinate.

Unlike the earlier supersolution certificate, a successful source witness's stream `V` is exactly the odometer of a genuine legal finite binary sequence. It need not be a globally stabilizing odometer, nor the odometer of a maximal evolution. The theorem requires only that the target occur in the finite legal sequence.

## 2. Exact independent source reconstruction

`independent_check.py` implements sparse formal polynomials over Z and separately specifies every intended equation. It checks the entire submitted source, including all positive adapters, macro internals, outer constraints, named ports, and the complete sum-of-squares assembly. The comparison is exact symbolic equality, not probabilistic agreement modulo several primes.

Verified results:

- All 1,923 named residual polynomials match the independent specification
- All 157 macro interfaces match, including all 118 POWER uses
- All 36 exposed port expressions match
- The exact set of 3,308 positive witness leaves matches, without duplicates or unaccounted leaves
- Every reference is defined before use; every binary gate is addition, subtraction, or multiplication
- Every witness, gate, and the free input is reachable from the final output
- The final output is precisely the sum of the squares of the 1,923 listed residuals, without extra or missing clauses
- The literal DAG hash equals the supplied frozen pin

Because the witness domain is positive integers, the sum of real nonnegative squares is zero exactly when every residual is zero. The natural adapters are always a positive witness minus one; `a,beta>=2` in POWER and the padding multipliers at least two are always a positive witness plus one. No implicit signed or zero-capable quantified integer is omitted from the count.

### Independent ledger

| Part | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|
| Body | 3,887 | 3,156 | 1,967 | 9,010 |
| Sum of squares | 1,923 | 1,922 | 1,923 | 5,768 |
| Complete polynomial | 5,810 | 5,078 | 3,890 | 14,778 |

The witness decomposition is

`118*26 + 30*5 + 5*3 + 4*4 + 5 + 3 + 5 + 3 + 8 + 12 + 11 + 9 + 3 = 3308`.

The terms are POWER outputs plus internals; Sub outer witnesses; AND common/partition values; SPREAD outer witnesses; five geometric values; three tile bitplanes; five legality bitplanes; three interior-mask factors; eight time quantities (`K,R,pre,new,final,nx,ny,nz`); twelve target decoding/bounding witnesses; eleven input descriptors/target codes; nine internal Cantor codes; and three padding multipliers.

The equation decomposition is

`118*15 + 30*3 + 5*2 + 4*4 + 5 + 1 + 10 + 3 + 1 + 1 + 3 + 1 + 12 = 1923`.

These terms are POWER; Sub; AND partitions; SPREAD outer equations; geometric equations; tile reconstruction; Cantor equations; interior-mask equations; time repetition; time recurrence; exact neighbor divisions; selected legality; and signed-target clauses.

The power count can also be checked by role: 90 inside 30 Sub calls, 12 direct SPREAD powers, five geometric powers, five physical row/plane/z radices, one patch shift, three box radices, one time-end shift, and one target point, totaling 118.

### Exact total degree

Exact sparse normalization gives maximum residual degree nine. Exactly three residuals reach it: `patch.shift.eq8`, `patch.shift.eq9`, and `patch.shift.eq11`. Each has highest homogeneous part

`-4 p q r d e f tx0 ty0 tz0`,

where `tx0,ty0,tz0` are the positive padding witnesses before adding one. Every other residual has degree at most eight. Hence the full sum of squares has highest homogeneous part

`48 (p q r d e f tx0 ty0 tz0)^2`.

This is nonzero, so the exact degree is 18, independently of the author's specialization checker. The count and degree are properties of this literal source, not minimality claims.

## 3. Arithmetic and physical dependencies

The previously accepted audit at `/workspace/shared/sandpile-fixed-arity-independent-audit-20261004/AUDIT.md` proves the relevant POWER, Sub, three-Sub AND, SPREAD, physical decoder, and padded-prism lemmas. This extension's complete macro equations were independently reconstructed and checked against the emitted source. They are the same mathematical macros, with fresh names and source syntax.

The only external number-theoretic dependency remains mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`. The prior independent audit fetched and pinned the source as SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`, Git blob `6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e`. This audit inherits that explicit dependency; it did not rerun Lean or claim a new formalization.

The fifteen POWER equations specialize the positive-index constructive Pell characterization with `k=e+1`, `m=b*out`. Positivity and the auxiliary Pell equation imply the required nonnegative subtraction `a-b`. The strict modulus slack and paired nonnegative congruence quotients are present. Its theorem is precisely `out=b^e` for `b>=2,e>=0`, in both directions. Each call contributes 26 positive witness leaves and fifteen equations.

Sub retains both strict extraction bounds and uses the carry-free binomial digit in radix `2^(M+1)`. Its parity is exactly binary bit containment. AND retains all three Sub tests, including disjointness of the residual supports. SPREAD retains its strict input range and `stride>=length+1` gap, so the copy exponents cannot collide and the full-bit mask selects exactly the intended diagonal. These are expanded polynomial constraints, not primitive bitwise or array operations.

The paid box has even dimensions `A=2p d tx`, `B=2q e ty`, `C=2r f tz` with each padding multiplier at least two, and lower corner `(-p d tx,-q e ty,-r f tz)`. Its corner is period-aligned. The two tile reshapes and two patch reshapes put coefficients at exactly `x+A y+AB z`. The three tile repetition factors cover every box cell once, and the patch shift places the finite additions at physical origin. The background digits are at most five, patch digits at most fifteen, and their sum `eta_hat` has digits at most twenty. The patch lies strictly inside the box. These statements were also tested afresh for every combination of six dimensions in `{1,2}`.

No least-action or stabilizing-supersolution theorem is used for the extension. The old exterior-stability reasoning is unnecessary here.

## 4. Tableau soundness, including all boundaries

Write `b=32`, `X=b^A`, `Y=b^(AB)`, `Q=b^(ABC)`, and `N=ABC`. The three geometric equations uniquely identify

`I = b X Y Jx Jy Jz`

as the low-bit mask of strict interior sites. All denominators are positive. The allowed mask is a true one-bit-per-spatial-slot stream, zero on all six faces.

For existential `K>=1`, POWER gives `W=Q^K`, and the time geometric equation uniquely gives `R=sum_{t<K} Q^t`. Therefore `IR` is precisely the union of the K interior-frame masks, without coefficient collisions. Sub makes `Apre,E` binary within those K frames and `V` binary in one frame.

### Initial, internal, and terminal time frames

The recurrence is

`Q(Apre+E) = Apre + Q^K V`.

The left side has base-32 digits at most two. On the right the first K frames and terminal frame have disjoint supports and digits at most one. There is no carry on either side. Its frame equations are exactly:

- Initial frame: `Apre_0=0`
- Internal frames: `Apre_(t+1)=Apre_t+E_t` for `0<=t<K-1`
- Terminal frame: `V=Apre_(K-1)+E_(K-1)`

Nothing survives above frame K. Induction identifies `Apre_t` with all earlier firings, and binary next states force every event layer to be disjoint from that history. The binary final mask supplies the same restriction for the last event layer. Thus `V` is exactly the total fired set. `K=1`, empty initial or intermediate layers, and an event in the last frame are all covered. There is no cyclic-time solution or self-starting history.

### Exact six physical neighbor streams

The equations `b nx=Apre`, `X ny=Apre`, and `Y nz=Apre` enforce unique exact natural quotients. Every occupied spatial slot has index at least `1+A+AB`, so all three divisions are integral, even in frame zero.

For an interior source, shifts by `+/-1,+/-A,+/-AB` lead to its physical neighbors in the same spatial frame. The lower and upper x-face zeros prevent row wrap, the y-face zeros prevent plane wrap, and the z-face zeros prevent wrap between temporal frames. In particular, a positive shift from the last temporal frame cannot enter frame K. All six shifted streams are supported within the original K frames, including the shell but never outside the prism. Explicit omitted-face counterexamples in the fresh tests demonstrate that these conditions are substantive.

The height stream repeated over frames is `eta_hat R`, with a unique frame decomposition. Adding the six shifted binary streams gives

`Cval = eta_hat R + b Apre + X Apre + Y Apre + nx + ny + nz`.

Every digit is between zero and 26. Thus all sums are carry-free, and each slot gives the initial height plus the number of previously fired neighbors. No outside firing is required or presumed.

### Selected-site legality and no overfiring

Because `E` has a low bit at each newly firing slot, `31E` fills exactly the five bits of precisely those slots. The expanded AND extracts `Cval` only there.

Each `Sub(E,Li)` makes `Li` a low-bit subset of `E`. The additional `Sub(E,L3+L4)` excludes overlap of the 8 and 16 planes: their overlap produces digit two, not an allowed low bit. Hence `L=L0+2L1+4L2+8L3+16L4` has exactly the possible digits 0 through 23 on the selected slots and zero elsewhere. The equation `selected=6E+L` has digits at most 29 on its right, and at most 26 on its left. It therefore forces a coordinatewise height at least six at every newly firing slot, with actual slack at most twenty.

There is correctly no `-6 Apre_t(v)` term at a selected site, because the recurrence already forces `Apre_t(v)=0` whenever `E_t(v)=1`. An activation cannot benefit from its own prior toppling or from any current/future event layer.

Each layer consists of finitely many unstable sites at the beginning of that layer. Serialize them in any order. Before an as-yet-unfired member is processed, other firings in the layer can only add chips to it, so it remains unstable. Induction over layers gives a finite legal sequence whose odometer is exactly `V`. Two adjacent height-five sites cannot ignite by mutual support: the earliest nonempty layer has no previously fired sites to supply chips.

This reasoning remains valid if the endpoint is unstable or subsequent evolution continues forever. No global stabilization, stable exterior, exhaustive schedule, or maximality assumption is present or needed.

## 5. Exact target, input uniqueness, and POWER domains

All eleven decoded fields are natural adapters or positive dimensions minus one. Each Cantor equation is the standard bijection of a pair of naturals to one natural. Ten right-associated equations uniquely decode the supplied free input, including `InputPlus=1`. That lowest input is a valid zero-data encoding, not an assertion that its target can fire.

For each axis, natural `s` and `s(s-1)=0` force `s` to be exactly zero or one, and `zeta=2h+s` fixes both parity and quotient uniquely. The translation equation forces

`ell=half_extent+h-2sh-s`.

Natural `ell` gives the lower bound, and positive `g` in `ell+g=full_extent` gives the strict upper bound. Therefore the exponent `ell_x+A ell_y+AB ell_z` is the unique mixed-radix index of the supplied physical target. Without the local upper bounds, radix aliases would be possible; the submitted source includes all three bounds.

POWER produces the single low-bit point `b^index`. `Sub(V,point)` forces exactly this target to occur in the actual fired set. Since `V` is already a subset of the interior mask, a target on the shell cannot pass. Enlarging a genuine witness box puts the fixed physical target strictly inside and removes any completeness issue.

All 118 POWER instances meet their mathematical domains:

1. The six dimensions and padding multipliers are positive, so all direct tile, patch, plane, z, shift, and box exponents are nonnegative; the constant base is 32 or a previously established radix at least two
2. All five geometric bases are at least two and their lengths are positive
3. Every SPREAD has positive length and its explicit gap gives `stride>=length+1`; consequently its copy-base exponent is nonnegative and the resulting copy base is at least two
4. Every Sub mask and value is a natural adapter or a nonnegative expression; expressions involving `base-1` have already established `base>=2`
5. Each Sub radix call has base two and exponent `mask+1>=1`; its two further bases are that radix and that radix plus one, with nonnegative exponents `value` and `mask`
6. The time-end power has base `Q>=2` and exponent `K>=1`
7. The signed target point uses nonnegative local coordinates, never a signed physical coordinate, in its exponent
8. All AND operands and difference witnesses, selected-legality planes, and final target-mask values are nonnegative at their Sub interfaces

These domains follow in a well-founded order from the complete conjunction. They need not hold for arbitrary assignments that fail the constraints. There is no circular appeal to a POWER theorem outside its proved domain, nor a hidden negative exponent.

## 6. Completeness and precise scope separators

Given a finite legal binary prefix containing the target, stop when the target first fires. Its positive finite length can be the existential `K`, with one singleton event layer per toppling. Enlarge the three independent box multipliers until the finite support and patch lie strictly inside, the target is off the shell, and all four SPREAD margins hold simultaneously. The permitted period-aligned boxes are arbitrarily large in each direction.

Use the sets of earlier topplings as `Apre_t`, the singleton events as `E_t`, and the total fired set as `V`. Their packed streams satisfy every mask, recurrence, and exact-neighbor constraint. Each newly firing site has legal height at least six and at most `20+6=26`, because each neighbor topples at most once. Its slack belongs to 0 through 20 and therefore has the required five planes. The exact input and target witnesses have their intended values, and the proved complete arithmetic macros supply the remaining positive witnesses. This proves completeness without a supplied horizon or global termination hypothesis.

### Ordinary target firing is strictly broader

Use a zero tile of shape `1 x 1 x 1`, a patch of shape `2 x 1 x 1`, and patch digits `[12,4]`, so `D=140`. Set the target to physical coordinate `(1,0,0)`, encoded by `(zeta_x,zeta_y,zeta_z)=(2,0,0)`.

The origin is initially the only unstable site. Its first toppling leaves the origin at six, the target at five, and all other affected sites at one. Thus every still-unfired site is stable and no binary prefix can reach the target. Ordinary legal evolution can topple the origin again, raising the target to six, and then topple the target. The exact legal sequence is `origin, origin, target`.

This is an admitted physical-code example separating ordinary unrestricted target firing from the theorem. An appropriately proved all-site-one-shot property of a particular loader can bridge that distinction on that loader's image; the present source does not establish that property or identify such an image.

### No finite stabilization is required

Take the uniform height-five periodic background and add one chip at the target. The target can legally fire in a one-step binary prefix, even though its six neighbors are then unstable. This instance cannot have a finite global stabilization: any finite nonzero toppling support has a maximal-x support site; its immediate positive-x neighbor is outside the support, begins with at least five chips, receives at least one, and never topples. It is therefore unstable at the proposed endpoint. The finite target certificate does not impose an unwanted global-stabilization condition.

## 7. Fresh finite coverage

The main audit's independent checker completed successfully:

- 1,880 exact binomial-digit/parity extractions and 297 explicit valid Sub outer-witness constructions, including zero and out-of-range indices
- 32,768 candidate AND triples, including false outputs
- 2,502 full-radix SPREAD cases plus a demonstrable failure outside its certified stride contract
- 50,408 arbitrary binary candidate tableaux for several frame widths and `K=1,2,3`; exactly 65 satisfy the recurrence, all with the intended cumulative/disjoint meaning
- 4,096 two-slot slack-plane candidates and 2,916 selected-legality threshold cases
- All 64 combinations of six physical dimensions in `{1,2}`, comparing the decoded tensors to direct physical coordinates at 53,056 sites
- 256 space-time boxes with each spatial side in `{2,3,4,5}` and `K=1,2,3,4`, checking exact six-neighbor streams and no-carry values at 27,440 temporal sites; side-two empty interiors are included even though the full source uses sides at least four
- Six explicit omitted-face spatial/time-wrap counterexamples, rejected by the actual mask
- All 2,744 height triples in `{0,...,13}^3` on a three-site path, comparing 175,616 packed three-layer assignments against direct legal binary reachability, with 8,232 target-existence comparisons
- The mutual-height-five rejection, the admitted heights-12/4 repeated-firing separator, and a binary legal prefix in the nonstabilizing uniform-five background
- 160 unique signed-code decodes, 2,400 strict coordinate-bound cases, 8,000 unique mixed-radix positions, and 257 eleven-field Cantor round trips including zero shifted fields

The additional semantic checker independently passed 4,368 recurrence candidates, 372 exact 3D shift fixtures over 100,480 coefficients, 1,728 legality-plane assignments, and 2,624 signed-target bound cases. Its separate report gives the details.

Finite experiments test the formulas and implementation; they do not replace the all-integer proof. Neither checker materializes the potentially enormous complete Pell witness for a whole physical instance. Existence of those witnesses follows from the explicitly inherited constructive macro theorem and its verified domains.

## 8. Reproduction, pins, and approval limits

Run the main fresh checker with ordinary Python 3, without `-O`:

`python /workspace/shared/sandpile-target-independent-audit-20261004/independent_check.py`

It reads the submitted JSON DAG as inert syntax, builds an independent formal specification, checks exact clause/interface equality, and runs only its own finite probes. `audit-receipt.json` and `audit-run.log` record the successful run. An isolated `python -I` replay of the main checker reproduced the receipt byte-for-byte; the separately inspected semantic checker also passed in isolated mode. Every submitted and audit-file pin was rechecked after replay. `audit-manifest.json` records the audited source pins, inherited dependency pins, independent deliverable hashes, and replay result.

Authoritative submitted pins:

- DAG: `352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504`
- Builder, inspected only: `6a9ced103676ce7ba0b052e00779177fb522101fc5479866273e3908d299c975`
- Final architecture: `dabbe1685bb050eca578c29472a00426c940df6002c383fe5c3a558797bf93c9`
- Source notes: `ab6e86e29f71815b839687f2eef46b264fc9b0c3f1a4226ef2507c9be6c88c88`

The architecture's proof was reviewed initially and again after the author updated only its evidence/status section. The authoritative builder and emitted DAG were unchanged throughout this audit. No submitted file was modified by the audit.

The accepted output is a closed fixed-shape positive-integer certificate for the raw physical binary-prefix relation, conditional on the pinned Pell theorem. Universal-machine loader identification, any all-site-one-shot theorem, and a raw program-to-physical-code compiler remain separate inherited obligations. No finite-fold or real-domain claim follows. Successful witnesses permit enlargement of the box, insertion of empty layers, and shifts of paired congruence quotients, so uniqueness or finite witness fibers must not be inferred.

Recommended concise statement: “An explicit horizon-free positive-integer polynomial of exact degree 18, with 3,308 positive witnesses and a 14,778-gate implementation, recognizes valid base-32 periodic 3D sandpile inputs admitting a finite legal binary prefix that fires an exactly supplied signed target. Its time tableau produces a genuine legal fired set. The constructive Pell power theorem is inherited from pinned mathlib; unrestricted repeated firing and universal-loader/compiler identification are outside this theorem.”
