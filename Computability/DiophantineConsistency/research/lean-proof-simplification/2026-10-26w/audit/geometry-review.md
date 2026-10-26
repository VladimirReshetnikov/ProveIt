# Independent mathematical review: helical coordinates and edge fields

Review date: 26 October 2026 (user time zone).
Production snapshot: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
No candidate or production source was modified for this review.

## Outcome

The geometric statements in the reviewed `HelicalCoordinates.lean` are mathematically correct, including the exact signed address, negative spatial positions, arbitrary band offset, absence of a coprimality premise, and the newly added finite-band bijection for positive width and height. The three original theorem statements also remain valid at H=0. The finite equivalence correctly excludes H=0.

The edge-field construction is also correct and matches the production west/north/east/south field order. Its normal form is a genuinely different proof organization from earlier static color-fiber classifiers. Its source-saving effect remains an integration question: replacing a matching proof by rfl is useful only if the exact literal-row bridge does not assume the old matching theorem and does not cost more repeated case analysis than it removes.

## Inspected artifact identities

- `lean/HelicalCoordinates.lean`: SHA-256 `73f9bf79e866f77159a7d0950c04964f98a77899880069d0d52ceacae4f8fc61`.
- `lean/EdgeFields.lean`: SHA-256 `81957d2ad382244c1d177c7e1ec96f7bf10683b7effc48e96b1bb1739f161d36`.
- `evidence/helical-coordinates.log`: SHA-256 `d721b00592571fe29038323430c18990adc41dced8e5ea52d2d8f79f0c15e2e2`.

The log at this review point records axiom outputs for `address_eq_iff`, `normalize_address` and `address_eq_zero_iff`, each within the standard set `{propext, Classical.choice, Quot.sound}`. The source already includes `bandAddress_injective`, `bandAddress_surjective`, and `bandEquiv`, but the inspected log still predates their axiom output. Thus this review accepts their mathematics; a fresh full-file compile receipt is required before labeling the extended file kernel checked. This review is not a second Lean compilation.

## 1. Exact signed address and helical orientation

The candidate address is

    address(w,H,x,t) = -x - w*t   in ZMod(w*H).

This is exactly the convention in production `WangTiles942Periodic.address`, used by `WangTiles942HelicalQuotient.quotientWord_binding`. The two relevant periods preserve it:

    address(x+w,t-1) = -x-w-w*t+w = address(x,t),
    address(x,t+H)   = address(x,t)-w*H = address(x,t).

Consequently the shear coordinate is `x+w*t`, not `x-w*t`. At time zero, a quotient position z is represented by spatial coordinate `-z.val`; the sign in the new surjectivity proof is therefore essential and correct. The production `address_row_zero` uses the same sign.

For arbitrary integer x and offset L, write

    q = (x+L)/w,
    r = (x+L)%w-L.

Integer Euclidean division gives x=r+w*q. Hence

    -r-w*(t+q) = -x-w*t.

The candidate `normalize_address` uses the correct time correction `t+q`. This is exactly the twisted extension's convention: crossing the right edge advances the band-row time by one. It remains correct for negative x because integer emod/ediv, not natural subtraction or truncating integer division, is used.

A separate presentation caveat: `normalize_address` has no positivity premise and proves only an algebraic address equality. It is true even for w=0 under Lean's division conventions, but in that case the representative is not a point of the empty band `[-L,-L)`. Statements describing it as a *canonical band representative* must attach w>0 or explain that in-band membership is supplied separately. The finite equivalence and `bandAddress_surjective` already impose w>0.

## 2. Injectivity on one canonical band

The band is the half-open integer interval

    -L <= x < w-L.

For x and y in this interval, `-w < x-y < w`. If addresses agree, their difference is an integer multiple of wH. Rearranging gives

    x-y = w*(H*k-t+u)

for an integer k, with the sign determined by the library divisibility convention. Since w>0, the factor on the right is an integer strictly between -1 and 1; therefore it is zero. Thus x=y, and the remaining equality is exactly equality of time classes in ZMod H. The reverse implication follows by multiplying the time divisibility witness by w.

This argument is stronger than a Chinese remainder argument. It never inverts w modulo H and never needs gcd(w,H)=1. The x coordinate is selected from one consecutive block of w integers; after it is recovered by the strict interval bound, w is cancelled in an integer equality. The time coordinate is then recovered modulo H.

For example, w=H=2 and L=0 still gives a bijection: the four pairs (0,0),(1,0),(0,1),(1,1) map respectively to 0,3,2,1 modulo 4. The common factor two creates no ambiguity.

The exact half-open bounds matter. Replacing x<w-L by x<=w-L admits both endpoints separated by w. Their addresses agree after a unit time adjustment, destroying spatial uniqueness. Likewise using ordinary natural coordinates would omit legitimate negative sites when L>0.

## 3. The H=0 case

The candidate `address_eq_iff` and `address_eq_zero_iff` intentionally do not require H>0. This is valid because Lean's `ZMod 0` is the integer ring. In the injectivity theorem, address equality is then an exact integer equality and the result says x=y and t=u. The same interval/cancellation proof establishes it.

The result is not a finite quotient in this case. The finite-band domain `Band w L × ZMod H` is infinite at H=0, and `bandAddress` uses `.val`, whose reconstruction property is guarded by a nonzero-modulus instance. Accordingly:

- `bandAddress_injective` requires `[NeZero H]`;
- `bandAddress_surjective` requires `0<H`;
- `bandEquiv` requires `0<w` and `0<H`.

These guards are correct. Do not claim that the `.val`-based map supplies the same equivalence when H=0 merely because the earlier integer-address theorem permits it.

## 4. Surjectivity and the complete finite equivalence

The added proof explicitly supplies a preimage, so the final claim is now an equivalence rather than only injectivity plus normalization.

For z in ZMod(wH), set x=-z.val, normalize x to r in the width-w band, and take the time class of q=(x+L)/w in ZMod H. The first address theorem allows replacement of that time class's natural representative by q itself. Normalization then gives

    address(r,q) = address(x,0) = z.

The proof of r's bounds uses the standard nonnegative remainder bound under w>0. The final cast back to z uses wH>0; this is supplied by positive w and H. No extra origin condition on L is needed for bijectivity: any consecutive width-w band works.

`Equiv.ofBijective` packages the proved map as an equivalence. Its noncomputable inverse is acceptable for a proof interface; it does not claim a newly executable decoder. If an explicit inverse expression is later useful, the constructive preimage in the surjectivity proof already identifies its formula, but turning that formula into an executable API is separate work.

## 5. Marker specialization

The zero-address specialization adds

    0 <= L < w.

These are exactly the conditions placing spatial origin 0 inside the chosen band. The theorem then identifies

    address(x,t)=0  iff  x=0 and t=0 in ZMod H.

It neither assumes uniqueness of a tile marker nor proves that an arbitrary band tiling has exactly one marker. The production `WangTiles942HelicalMarker.quotientWord_marker_iff` also requires a semantic marker classification on the band, `C x t = start iff x=0 and t % H=0`. That hypothesis remains necessary. The geometric theorem discharges the coordinate part of the argument once that actual marker classification is established.

The positive H case connects `t : ZMod H = 0` with `t % H=0`. A production adapter must make that conversion explicitly and retain the tile-to-word binding. It must not replace tile equality by equality of arbitrary chosen tile indices without using the existing table injectivity theorem when needed.

## 6. Shared edge fields match the literal tile orientation

The production `WangTiles942Core.Tile` fields are ordered west, north, east, south. Therefore

    tile(x) = <E(x), N(x), E(x+1), S(x)>

makes `(tile(x+1)).west = (tile(x)).east` definitionally true. The candidate's `matchingRowEquiv` establishes an actual equivalence between three edge fields and horizontally matching rows; it does not lose any such row. For a pre-existing compatible row, recover E from west, N from north and S from south; the old matching equation recovers the east coordinate.

For a time successor `next`, the two-field grid

    tile(k,x) = <E(k,x), V(k,x), E(k,x+1), V(next(k),x)>

makes both horizontal and temporal matching definitional. This is valid for an arbitrary successor function, including the finite cyclic `nextIndex`. No injectivity or surjectivity of that function is used by these two matching laws.

The supplied initializer example copies all four production tuples exactly, including Start `<2,435,3,1>` and the actual initializer-head south color 4. Its E field has values 2 at x<=0, 3 at x=1, and 4 at x>=2, so the color changes occur on the actual adjacent edges. The proof of literal equality is a real all-integer argument, not a finite list of spot checks. However it currently concerns a standalone copied `Tile Nat` definition. Connecting it to the production `initialTile` remains an adapter obligation.

## 7. The transition signal support is correct

Let h be the old head, d the actual action's direction, and r=rail(d,target) its actual direction-specific rail color. The correct west-edge signal is

    E(x) = if x = h+1 then r else 0    for a right move,
    E(x) = if x = h   then r else 0    for a left move.

This gives:

| Direction/site | West | East | Intended literal role |
|---|---:|---:|---|
| right, old head h | 0 | r | transition tile |
| right, new head h+1 | r | 0 | receiving tile |
| left, old head h | r | 0 | transition tile |
| left, new head h-1 | 0 | r | receiving tile |
| every other site | 0 | 0 | passing tile |

These values match production `stepTile_west`, `stepTile_east` and `nextHead_eq`. The rail must remain the actual `rail d (action sourceIndex).target`, not an arbitrary nonzero signal. Allowedness and decoding use the actual target-set membership. Rail injectivity is only proved on the direction-specific target set; it must not be silently generalized to every natural target.

There is one important API-generalization trap. Production `stepTile_allowed`, `stepTile_west`, `stepTile_east` and `stepTile_horizontal` hold for arbitrary cfg and q, without `cfg.state=some q`. Only the semantic north/south statements require that live-state identification. If the replacement defines N=`color cfg` and S=`color (machine.step cfg)`, then its exact-equality bridge requires that premise. Such a bridge cannot replace the unrestricted old theorems unchanged.

Two sound migration options are: retain the original unrestricted interfaces and use the normal form only under the actual live-state premise in `runTile`; or define q-specific input/output color functions (equivalently use cfg with state overwritten by `some q`) and prove an unrestricted literal bridge, then specialize the colors under the live-state hypothesis. Charge this adapter work in any claimed source reduction.

## 8. Avoid moving the same proof burden behind a definition

`grid_eq_of_matching` assumes both original matching properties. It is a useful equivalence/transport lemma, but invoking it cannot itself justify deleting the old matching proofs: that would be circular. To obtain a substantive simplification, independently define E and V from machine states and phase boundaries, then prove literal equality to the existing tile construction without invoking the matching theorem being replaced.

The exact bridge still needs transition/receiving/passing membership and the correct local colors. Whole-cycle allowedness still needs halt persistence at H-2, the height condition T+2<=H, and H>=3 to distinguish initializer/finish/reset. A definitionally matching edge grid can otherwise describe disallowed tiles just as easily as allowed ones. These obligations are not incidental proof bookkeeping.

The initializer prototype demonstrates that helper-inclusive source can grow even when matching becomes rfl: it introduces three edge functions and an exact equality proof. Its present value is the invariant and possible reuse across step, pass, finish, reset and cycle constructors, not a measured production LOC saving. Any final report should separate checked generic theorem/initializer proof from unintegrated machine-row adapters and source reduction estimates.

## 9. Novelty relative to the earlier color-fiber proposals

I01 and I02 classify the north/south colors of individual already-allowed tiles and specialize exact-color corollaries. They preserve the original row representation. This proposal instead constructs an entire matching row/grid from shared edge data and proves a representation equivalence. The two mechanisms can coexist: a color-fiber classifier can help prove allowedness of a tile emitted by the edge grid, while matching follows from shared data.

A structure merely bundling the four already proved run-row facts would be a much smaller presentational change; it should not be marketed as a breakthrough. The stronger edge-data normal form removes one independent copy of each horizontal/vertical edge value. Its contribution remains distinct after the earlier classifiers are assumed applied, provided actual independent construction and exact literal binding are delivered or clearly left as integration work.

## Acceptance recommendation

Accept the coordinate mathematics, including the full finite equivalence once the refreshed compile log succeeds. Retain the edge-field prototype as a checked structural proposal with a concrete initializer demonstration. Keep production migration, net source savings, runtime effects and whole-project equivalence explicitly unclaimed until their exact adapters are compiled. No false statement, coprimality omission or sign reversal was found in the reviewed coordinate statements.


## Addendum: unrestricted literal step-row bridge

The extended `EdgeFields.lean` was independently inspected after the preceding review. Reviewed SHA-256: `00bbf4f01b855786a9c014d31388b8dcdb0a8d6b75aaed5a4f303d69bc3f6116`.

`literalStep_eq_edges` resolves the unrestricted-interface concern at the generic level. It quantifies arbitrary source and written colors, an arbitrary direction-indexed rail function, an arbitrary tape-bit function, and an arbitrary target-color function. Its proof uses only the two direction cases and the three actual positions (old head, moved head, elsewhere), plus integer arithmetic showing the two heads are distinct. It invokes neither a previous horizontal-matching theorem nor a machine-state or halting premise. Therefore the new exact equality is not circular.

The production substitution is exact:

| Generic argument | Production expression |
|---|---|
| h | cfg.head |
| d | `(WangTiles942.action (sourceIndex cfg q)).2.1` |
| rail(d') | `WangTiles942.rail d' (action (sourceIndex cfg q)).2.2` |
| source | `headColor ((sourceIndex cfg q).val/2) ((sourceIndex cfg q).val%2)` |
| written | `(action (sourceIndex cfg q)).1.toNat` |
| target(b) | `headColor (action (sourceIndex cfg q)).2.2 b` |
| bit(x) | `(Tape.read cfg.tape x).toNat` |

The moved-head identification is the existing `nextHead_eq`. The transition branch uses exactly `<(1-d.toNat)*rail false, source, d.toNat*rail true, written>`; the receiving branch uses exactly `<d.toNat*rail d, bit x, (1-d.toNat)*rail d, target(bit x)>`; the pass branch preserves the old bit. These are the literal production `transitionRow`, `receiveTile` and remaining `stepTile` branch, after the displayed substitutions. No identification of source/target with `color cfg` or `color (step cfg)` is needed to obtain the row equality or horizontal matching. Those semantic interpretations can remain separate and keep their original live-state premise.

Consequently `literalStep_horizontal` is a valid new consequence: rewrite by the independently proved literal equality and apply the definitionally matching constructor. This is stronger evidence than the earlier completeness-only `grid_eq_of_matching` theorem. The remaining integration work is small but real: adapt the standalone Tile type to the production Tile, prove the displayed parameter/literal bridge using `nextHead_eq`, and compile the original public wrappers and their consumers. Allowedness of the actual 942-tile table is still not a consequence of arbitrary generic colors; retain the existing allowedness proofs or migrate them with their actual target/bit restrictions.

This addendum accepts the mathematics and exact source mapping of the new prototype. Its compilation was still in progress when this source inspection was requested, so a new compiler-success claim must be based on the final receipt. No candidate file was changed by this review.
