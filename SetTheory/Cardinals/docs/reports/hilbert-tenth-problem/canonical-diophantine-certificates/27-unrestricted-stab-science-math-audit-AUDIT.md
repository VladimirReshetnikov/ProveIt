# Independent mathematical audit: unrestricted finite global stabilization

Audit date: 4 October 2026. This is a proof-audit record, not an article.

## Verdict and scope

**PASS for the proposed mathematical architecture.** No counterexample or gap was found in the enlarged-radix cap, carry-free balance, finite-support least-action argument, input conversion, or exterior treatment. The resulting existential predicate is exactly existence of a **finite legal sequence that globally stabilizes the supplied periodic-plus-finite configuration**, with no binary restriction on its true odometer.

This audit does not certify a newly emitted polynomial's literal source, witness count, gate count, or degree. It relies on the same explicit constructive Pell power theorem identified in the inherited materials; it does not newly prove that theorem. The new source must still be checked to ensure that every required clause below is actually emitted. No inherited executable, article-generation process, upstream program, schedule, or Lean process was run.

The two read-only inputs were:

- `sandpile-fixed-arity-20261004/PROOF.md`, SHA256 `40297f9767965fa5c47e310eadcd9bc89dcc3963ee090c93727712cf185a075a`
- `sandpile-repeated-target-20261004/ARCHITECTURE.md`, SHA256 `ccb59eac23edab6db8500814123c0e0e9486253d577f52be1e177c959efe5e9f`

They were read as inert text. This report audits the stabilization proposal rather than inheriting the repeated-target tableau theorem.

## 1. Unambiguous notation and exact input

Use lowercase `b` for the new radix, reserving `A,B,C` for the box side lengths. This avoids the inherited proof's overloaded uppercase `B`.

The physical input is unchanged: positive dimensions `p,q,r,d,e,f`, the ordinary base-32 tile code `T`, and ordinary base-32 patch code `D`. The tile contains exactly its declared `pqr` slots, each in `0,...,5`; the patch contains exactly its declared `def` slots, each in `0,...,15`. Leading declared zero slots are permitted, but nonzero digits past the declared lengths are forbidden. On the physical lattice,

`eta(v) = tile(v mod (p,q,r)) + patch(v)`.

The patch is zero outside `[0,d) x [0,e) x [0,f)`. The initial heights are natural and at most 20. No restriction is added to the eventual number of legal topplings at a site.

Raw validation remains at radix 32. In particular, retaining the old four tile Sub conditions and the raw patch mask pays validity of the original codes. It is incorrect to reinterpret `T` or `D` directly in the existential new radix without the two conversion clauses.

## 2. Radix choice, conversion, and the count cap

Choose a positive integer `L`. Pay `b = 32^L` using the explicit power macro. The two paid conversions are

`T_b = SPREAD(T; 32,pqr,L)` and `D_b = SPREAD(D; 32,def,L)`.

Their stride-gap clauses impose `L >= pqr+1` and `L >= def+1`. Since both products are positive, valid witnesses actually satisfy `L>=2` and `b>=1024`. The weaker bound `b>=32` is sufficient for every carry estimate below.

If the raw digit lists are `t_i` and `d_i`, the proven SPREAD graph gives exactly

`T_b = sum t_i b^i`, `D_b = sum d_i b^i`.

Thus the physical data are preserved, not replaced by free recoded data. There is no upper bound on `L`.

Introduce positive `h` and impose `16h=b`. The power theorem has already established `b=2^(5L)`, so the equality forces

`h = 2^(5L-4) >= 2`.

Set `m=h-1=b/16-1`. This is a nonnegative integer whose binary expansion is a contiguous block of `5L-4` one-bits. No additional root or exponent theorem is required for `h`: its precise value follows from the exact linear equation and the previously established value of `b`.

Let `I` be the one-low-bit-per-interior-slot mask. Since slots are spaced `5L` binary positions apart, the product `mI` contains disjoint blocks of `5L-4` one-bits. Therefore

`Sub(mI,U)`

is exactly the following statement: `U=sum u_j b^j`, every strict-interior digit is an arbitrary integer in `0,...,m`, and all other digits are zero. In particular, there are no digits outside the finite box. This conclusion comes solely from the mask, before use of the balance equation. There is no circular assumption about carries or legality.

## 3. Geometry remains valid at this variable radix

Choose `tx,ty,tz>=2`, and set

`hx=pd tx`, `hy=qe ty`, `hz=rf tz`,

`A=2hx`, `B=2hy`, `C=2hz`, `N=ABC`.

The physical box consists of vertices with coordinates in

`[-hx,hx) x [-hy,hy) x [-hz,hz)`.

Its lower corner is period-aligned. Local coordinates are packed in order `x+Ay+ABz`. All three side lengths are at least four. The existing four spatial SPREAD gap clauses remain necessary, with radix powers changed consistently from 32 to `b`:

- tile rows: base `b^p`, length `qr`, stride `2d tx`
- tile planes: base `b^(Aq)`, length `r`, stride `2e ty`
- patch rows: base `b^d`, length `ef`, stride `2p tx`
- patch planes: base `b^(Ae)`, length `f`, stride `2q ty`

The three background repetition factors and the patch's shift by `b^(hx+Ahy+ABhz)` are unchanged in form. Their mixed-radix coordinate proof only needs a power-of-two radix, not its fixed numerical value. Unique coordinate decompositions prevent overlapping tile contributions. The resulting background digits are at most 5, patch digits at most 15, and their sum at most 20, below `b`.

The patch is strictly inside the box: `hx>=2d`, `hy>=2e`, `hz>=2f`. For example, its x coordinates in local indexing run from `hx` to `hx+d-1`, all between 1 and `A-2`. The y and z claims are identical.

The strict range required for the second spatial spread is not an extra semantic oracle. After the row spread, every x coordinate is less than `A`, so all `qr` rows fit below exponent `Aqr`. The patch version uses `Aef`. Thus those range inequalities follow from the first spread and geometry; their paid slack equations still need to be present in literal source.

There is no circular dependence between choosing a large enough radix and choosing a large enough box. The two raw conversion gaps depend only on raw input lengths. Box padding is independently unbounded in each axis.

## 4. Interior mask and all six neighbor shifts

Let `X=b^A`, `Y=X^B=b^(AB)`, `Q=Y^C=b^N`. The natural solutions of

`b^2 ((b-1)Jx+1)=X`,

`X^2 ((X-1)Jy+1)=Y`,

`Y^2 ((Y-1)Jz+1)=Q`

are respectively `G(b,A-2)`, `G(X,B-2)`, `G(Y,C-2)`. The equations are linear in their natural unknowns, and the usual geometric-series values satisfy them. Consequently

`I=b X Y Jx Jy Jz`

has one low bit at each local `(x,y,z)` with `1<=x<=A-2`, `1<=y<=B-2`, `1<=z<=C-2`, and nowhere else. Products have unique mixed-radix exponents.

Because every nonzero source count is strictly interior, each of the six integer index shifts `+/-1`, `+/-A`, `+/-AB` is exactly its intended lattice-neighbor shift, stays within the box, and cannot wrap a row or plane. Multiplicity of a source count does not change this argument. The natural quotient equations

`b Ux=U`, `X Uy=U`, `Y Uz=U`

are complete because every nonzero source exponent is at least `1+A+AB`, and hence all three divisions are exact. The six streams are precisely `bU,XU,YU,Ux,Uy,Uz`.

The **whole six-face shell** is needed. It is not enough to remove just the first and last packed slots or only the z faces. For example, in a `4x4x4` box, multiplying the slot for `(3,1,1)` by `b` sends it to `(0,2,1)`, which is not a lattice neighbor. The proposed full mask excludes that source and all analogous wrap artifacts.

## 5. Exterior treatment, stated precisely

Extend `u` by zero to every lattice vertex outside the box. Every exterior vertex adjacent to an interior-box vertex is adjacent to a vertex on the box's boundary shell. The shell count is zero. Thus, for every exterior vertex `v`,

`u(v)=0` and `sum_(w~v) u(w)=0`.

The patch is strictly inside the box, so `eta(v)` outside is exactly the stable periodic background. Therefore the global endpoint expression is stable outside automatically:

`eta(v)-6u(v)+sum_(w~v)u(w) = eta(v) <=5`.

Shell vertices can receive chips from strict-interior topplings. They must not be dropped from the packed balance or endpoint-stability masks. They are included in all `N` slots of the endpoint stream. This is how the certificate tests that such received chips do not force further topplings beyond the selected support.

This is a finite-support global argument on the original lattice. It does not introduce a sink, discard boundary chips, or replace the infinite physical sandpile by a finite graph.

## 6. Stable endpoint and carry-free equivalence

Let `J=G(b,N)`. The unchanged endpoint bitplanes

`F=Z0+2Z1+4Z2`,

`Sub(J,Z0)`, `Sub(J,Z1)`, `Sub(J,Z2)`, `Sub(J,Z1+Z2)`

give exactly digits `f_j in {0,...,5}` on all box slots, with no outside digits. The last Sub condition forbids simultaneous 2- and 4-bits; at a slot the unweighted sum of those bitplanes is at most 2, so there is no hidden base-`b` carry in that condition.

Impose the single equality

`H+Delta+bU+XU+YU+Ux+Uy+Uz = 6U+F`.

Before using this equality, the mask, geometry, and endpoint clauses independently prove that its uncarried per-slot coefficients satisfy

`0 <= left_j <= 20+6m = 3b/8+14 < b`,

`0 <= right_j <= 6m+5 = 3b/8-1 < b`.

The first strict inequality holds already at `b=32`, where the maximum is 26; equivalently `14<5b/8`. All summands have support within the `N` slots by the shell argument. Thus neither side has an inter-slot carry or an above-last-slot contribution. Uniqueness of finite radix-`b` representations makes the equality equivalent to every individual conservation equation

`f(v) = eta(v)-6u(v)+sum_(w~v)u(w)`

inside the box. Combined with the exterior argument, the decoded natural finite-support `u` is a globally stabilizing supersolution with nonnegative stable endpoint.

No assertion that `u` is itself legally executable has occurred here or is needed below.

## 7. Least action for arbitrary finite natural counts

The binary restriction in the inherited least-action lemma is inessential. Let `u:Z^3 -> N` have finite support, and suppose

`F(v)=eta(v)-6u(v)+sum_(w~v)u(w) <=5`

for every vertex. Nonnegativity of `F` is not needed for the lemma, although the certificate imposes it.

Take any finite legal toppling sequence. If its count first exceeds `u` at a toppling of `v`, then immediately before that toppling its count `a(v)` is exactly `u(v)`, and all neighbor counts satisfy `a(w)<=u(w)`. The current height at `v` is therefore at most

`eta(v)-6u(v)+sum_(w~v)u(w)=F(v)<=5`,

contrary to legality. Hence every finite legal prefix has count bounded pointwise by `u`.

Put `M=sum_v u(v)`, a finite natural integer. Starting from the input configuration, repeatedly choose any unstable site whenever one exists. Each finite prefix is bounded by `u`; therefore no such process can execute `M+1` steps. It must stop after at most `M` steps, and it can stop only when every site is stable. This gives a finite legal global stabilization. There is no fairness assumption, compactness argument, or limit of infinite sequences. If desired, use a fixed enumeration of `Z^3` to make each choice determinate.

The actual legal odometer `u*` satisfies `u*<=u`. The supplied supersolution need not equal `u*`. For a concrete counterexample to the stronger claim, place height 5 at two adjacent sites and 0 elsewhere. The true odometer is identically zero. Giving both sites supplied count 1 produces endpoint zero at those two sites and height 1 at each of their other neighbors, which is also stable. The mask and balance should accept this witness. It certifies the right existential language despite being an overfiring witness.

## 8. Completeness with an arbitrarily large true odometer

Suppose a finite legal sequence globally stabilizes the given valid physical input. Let its natural odometer be `u*`; its support is finite, and let `Umax=max_v u*(v)`, taking zero when the sequence is empty.

Choose `L` sufficiently large that all of the following hold simultaneously:

- `L>=1`
- `L>=pqr+1`
- `L>=def+1`
- `32^L >= 16(Umax+1)`

There is no upper bound on this witness, so such a choice always exists. The final condition gives `u*(v)<=b/16-1=m` at every vertex. It is a choice made in the completeness proof, not a new constraint requiring the polynomial to know `Umax` or the true odometer in advance.

Then choose each padding multiplier sufficiently large that the finite support of `u*` lies strictly inside its corresponding interval and all four paid spatial spread-gap inequalities hold. For an axis whose physical firing coordinates range from `vmin` to `vmax`, it is enough that the half-extent exceed both `-vmin` and `vmax+1`. Each half-extent ranges over unbounded positive multiples of the required period-and-patch product. The input patch is already guaranteed interior.

Pack `u*` in this box. It satisfies the cap mask and exact quotient clauses. Pack the true stable endpoint on the entire box and split its digits into the three permitted bitplanes. Exact toppling conservation supplies the balance equation. Input conversion and spatial geometry supply their outputs and positive range slacks. Completeness of the explicit arithmetic macros supplies the remaining witnesses.

This argument includes arbitrarily repeated topplings, the empty stabilizing sequence, arbitrarily large coordinates of the firing support, and declared input arrays containing only zero digits. Increasing `L` or padding changes values of a fixed witness list, not the number of witnesses or equations.

## 9. Domain order and fixed arity

The necessary domain reasoning is acyclic:

1. Positive physical dimensions give positive raw lengths; base-32 validation establishes finite input ranges.
2. Positive `L` and the paid power give `b=32^L>=32`.
3. The exact sixteenth equation gives positive integral `h`, specifically a power of two; hence `m=h-1>=0` before it is passed to Sub.
4. Conversion stride gaps give legitimate SPREAD exponents and strict-range slacks.
5. Positive padding and the four spatial gaps make every subsequent radix at least 2 and every geometric/spread exponent nonnegative.
6. The mask equations identify natural `I,J`; `mI`, the count `U`, every shift quotient, and the endpoint bitplanes are natural.
7. Only then are digit bounds and balance interpreted.

For a literal implementation, each mathematical natural still uses a strictly positive quantified leaf minus one; `tx,ty,tz>=2` use positive leaves plus one. Any adapter introduced for a product mask must be equated to that mask. In particular, do not silently treat `h-1` as natural before using `16h=b` and the power clause.

Relative to the old binary stabilization architecture, the conceptual additions are a radix POWER, two fixed-size raw conversion SPREADs, the sixteenth equation, and replacement of the binary count mask by the cap mask. The spatial macro inventory remains fixed. A candidate proof must not simply substitute `b` for every occurrence of 32: raw physical-code validation and the conversion input radix remain exactly 32. All spatial and endpoint stream radices, including shell equations that previously used the literal 1024, must instead change consistently to `b` and `b^2`.

Fixed arity follows at the architectural level from a fixed number of expanded macros and scalar equations. Exact numerical counts, live-gate accounting, polynomial degree, and source correspondence require the separate literal-source audit.

## 10. Separators, scope limits, and finite checks

### Genuine repeated finite stabilization

Take the zero periodic tile and a patch of shape `2x1x1` with digits `[12,4]`, whose raw base-32 code is `D=140`. A legal sequence is origin, origin, its positive-x neighbor. Its counts are `[2,1]`; its endpoint is stable. Any binary globally stabilizing supersolution is impossible because the origin's endpoint after at most one own toppling would be at least `12-6=6`. Thus the new construction is strictly more general than the binary global-stabilization predicate on the unchanged physical code.

### Finite global stabilization remains different from target firing

A periodic background of height 5 everywhere plus one added chip has a legal first toppling, but no finite-support stabilizing supersolution and hence no finite global stabilization. Indeed, for finite-support `u`, the endpoint differs from the height-five background at finitely many sites. The sum of that difference is exactly 1, since finite toppling Laplacians sum to zero. A stable endpoint would make every such difference nonpositive, a contradiction. The new theorem must not be stated as unrestricted target firing or as every notion of infinite-volume stabilizability.

### Fresh finite checks

The locally authored and inspected `check_math.py` imports no inherited implementation. It passed:

- 256 exhaustive binary count patterns on the eight strict-interior sites of a `4x4x4` prism at abstract radix 32
- 600 further packing cases at radices 32, 1024, and 32768, on a `5x5x5` prism, including configurations attaining all six neighbor caps simultaneously
- 450 direct raw-code conversions at multiple lengths and admissible strides
- the complete packed balance for the repeated `[12,4]` stabilization with `L=3`
- an explicit accepted stable-input overfiring supersolution
- an explicit row-wrap counterexample when the full shell is omitted
- acceptance of the exact count cap and rejection of the first over-cap digit

The fresh checker's safety bound is only a guard on its tiny illustrative legal simulation; it is not an assumption of the theorem. Finite tests are evidence for the inspected identities, not a proof of the all-integer equivalence or a test of giant Pell witnesses.

The receipt is `finite-check-receipt.json`. The checker SHA256 is `dd1d1ed8fe5d52f24b5810dd344778181c156bab87cdb2873087fd4b7fc1a059`; receipt SHA256 is `8b15b0321d32eb7446f26dfda227588f28db15e4ea9110d4b95bd7f074661405`.

## Required wording and implementation checks

No mathematical repair is required. Preserve these points in the final claim and source:

1. Say **finite legal global stabilization**, with unrestricted natural true counts; do not broaden this to all infinite-volume notions of stabilizability.
2. Say the supplied witness is a **finite-support stabilizing supersolution**, not necessarily the actual or legally executable odometer.
3. Include both paid raw base-32 conversions and retain raw base-32 validity checks.
4. Include the exact positive-sixteenth relation and the natural cap mask.
5. Retain the entire spatial zero shell, all shell endpoint slots, and the stable exterior argument.
6. State the explicit completeness choice `32^L>=16(max u*+1)`.
7. Keep source-size, degree, and Pell-dependency claims separate from this mathematical audit.

## Final proof consistency addendum

The complete new `PROOF.md` was read on 4 October 2026 after this audit was written. Its exact input language, two conversions, cap mask, geometry, least action, completeness choice, and distinction between finite global stabilization and target firing agree with this audit. No source executable was rerun for this pass.

The expanded POWER equations match the stated inherited dependency. Sub's positive slacks correctly extract an odd exact radix digit, including zero arguments and rejection above the binomial range. The AND proof is sound: if A and C share a bit, their least shared bit has no incoming carry and is lost from A+C, contradicting `Sub(A+C,A)`; conversely disjoint supports add without carries. The SPREAD equations correctly make their second geometric base `bC=b^s`, with top power `EP=(bC)^n`.

No structural mathematical correction is needed. Two small wording clarifications were communicated and then verified in the updated file: section 4 now names the sum `T1+T2` explicitly when bounding it by two; section 7 now explicitly extends the global endpoint by `F(v)=eta(v)` outside the box, while u is zero-extended. These do not alter the equations or theorem. Literal source counts and degree remain under the separate exact-source review.

**Final manuscript consistency verdict: PASS.** The reviewed final `PROOF.md` SHA256 is `1d426f591b2f9cdbf552fcc151515a7c402bb7c4b06a127bae8ab35de88e4579`. No mathematical corrections remain pending.
