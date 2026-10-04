# Fixed-arity ordinary target firing with repeated topplings

Research certificate, 4 October 2026. This is a source-and-proof packet, not an article. The approved binary-prefix source and its audit are preserved unchanged. This construction removes the binary-prefix restriction while preserving exactly the same raw physical input and signed target interface.

## 1. Exact theorem and dependency

For one positive integer `InputPlus`, decode `InputPlus−1` through ten right-associated Cantor pairings into the eleven natural fields

`(p−1,q−1,r−1,T,d−1,e−1,f−1,D,ζx,ζy,ζz)`.

The six dimensions are positive. `T` is a base-32 stream with `pqr` declared digits, all in 0–5. `D` is a base-32 stream with `def` declared digits, all in 0–15. Declared leading zero slots are permitted; nonzero digits outside either declared array are forbidden. The tile defines a periodic background on Z³, and the patch is added at `[0,d)×[0,e)×[0,f)`. For `ζ=2h+s`, with `h≥0` and `s∈{0,1}`, the signed coordinate is `h−2sh−s`. Thus the codes `0,1,2,3,…` mean `0,−1,1,−2,…`.

The emitted integer polynomial `P` satisfies:

> There exist 3,865 strictly positive integer witnesses with `P(InputPlus,w)=0` if and only if the decoded physical input is valid and has a finite legal ordinary toppling sequence containing its exactly decoded target. Sites may topple repeatedly.

The source contains 2,251 squared residuals and 17,275 binary arithmetic gates. Its degree is exactly 18, independently verified by exact sparse normalization of all residuals. Every POWER, Sub, AND and SPREAD is expanded. The fixed source shape is independent of input sizes, coordinates, box size and sequence duration.

The number-theoretic dependency is unchanged from the independently accepted binary certificate: the constructive Pell power theorem at mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`; pinned file SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. This packet does not run Lean or import any upstream program. It inherits that explicit arithmetic theorem and gives the remaining finite-tableau argument below. No arbitrary MRDP representation is invoked.

## 2. The fixed physical input is not silently recoded

The ordinary tile and patch are first validated in radix 32 by the accepted explicit Sub/bitplane equations. Choose positive witnesses `K,L` and let POWER give

`b=32^L`.

Introduce positive `h_b` and natural `g_b`, enforcing

`2h_b=b`,
`b=64(K+1)+g_b`.

Two additional, fully expanded calls are

`T_b=SPREAD(T;32,pqr,L)`,
`D_b=SPREAD(D;32,def,L)`.

Each SPREAD enforces its own strict range and stride gap, so `L≥pqr+1` and `L≥def+1`. If the original digits are `t_i,d_i`, these outputs are exactly `Σ t_i b^i` and `Σ d_i b^i`. No new free input code or uncharged digitwise conversion has replaced the original physical code. The radix is a power of two and satisfies `b≥64(K+1)>K`.

This choice is complete: after a finite legal prefix fixes `K`, take `L` large enough to satisfy both conversion gaps and the radix inequality. There is no upper bound on `L`, and increasing it changes only existential witness values, never the polynomial's arity or source shape.

## 3. Paid geometry at the enlarged radix

Choose independent padding multipliers `tx,ty,tz≥2`, and set

`hx=p d tx`, `hy=q e ty`, `hz=r f tz`,
`A=2hx`, `B=2hy`, `C=2hz`, `N=ABC`.

The box lower corner is `(−hx,−hy,−hz)`, period-aligned in each axis. The two tile reshapes and two patch reshapes from the accepted geometry are repeated at radix `b`, with these exact strides:

- Tile rows: base `b^p`, length `qr`, stride `2d tx`
- Tile planes: base `b^(Aq)`, length `r`, stride `2e ty`
- Patch rows: base `b^d`, length `ef`, stride `2p tx`
- Patch planes: base `b^(Ae)`, length `f`, stride `2q ty`

The tile's three repetition factors have bases `b^p,b^(Aq),b^(ABr)` and lengths `2d tx,2e ty,2f tz`. The patch is shifted by the paid power `b^(hx+Ahy+ABhz)`. All intermediate radix powers, strict input-range gaps and spread gaps are included in the source.

Expanding these products puts exactly the physical initial height at each slot `x+Ay+ABz`, with no overlapping tile copies. The background digit is 0–5, the patch digit 0–15, and their sum `η̂` has digits 0–20. The patch lies strictly inside the box. The same finite tensor proof works for every power-of-two radix; it does not depend on the value 32. Only the external-code validation and the two conversions remain at radix 32.

Put `X=b^A`, `Y=X^B=b^(AB)`, `Q=Y^C=b^N`. Natural `Jx,Jy,Jz` obey

`b²((b−1)Jx+1)=X`,
`X²((X−1)Jy+1)=Y`,
`Y²((Y−1)Jz+1)=Q`.

They uniquely identify the finite geometric sums of lengths `A−2,B−2,C−2`. Therefore

`I=bXY Jx Jy Jz`

is exactly the one-bit-per-slot strict-interior mask, zero on all six spatial faces. All three box dimensions are at least four.

## 4. Tableau masks and the one recurrence

POWER gives `W=Q^K`; a natural repetition value obeys `(Q−1)R+1=W`, so `R=Σ_(t<K)Q^t`. Introduce natural `Apre,E,V`, and impose

`Sub((b−1)IR,Apre)`,
`Sub(IR,E)`,
`Sub((b−1)I,V)`,
`Q(Apre+E)=Apre+WV`.

Because `b` is a power of two, the masks are disjoint binary blocks. Thus `E` has a 0/1 digit at each allowed interior space-time slot. `Apre` and `V` initially have arbitrary digits in 0–`b−1` at their allowed slots. In particular `Apre,E<Q^K` and `V<Q`. We do **not** initially infer that `Apre+E` has no carries.

### Whole-frame induction, with no circular carry assumption

Write the canonical radix-`Q` frames as `Apre=Σ_(t<K)a_tQ^t` and `E=Σ_(t<K)e_tQ^t`, with `0≤a_t,e_t<Q`. The right side `Apre+Q^K V` has those frames followed by `V`, with no overlap. Reducing the recurrence modulo `Q` first forces `a_0=0`.

Suppose `a_t` has already been proved to be the cumulative earlier events, with each radix-`b` digit at most `t`. Each digit of `e_t` is at most one, so each digit of `a_t+e_t` is at most `t+1≤K<b`. It is therefore a valid single radix-`Q` frame and produces no carry into the next frame. At `t=0` there is no lower incoming carry; at subsequent steps all lower-frame additions have already been established carry-free by induction. Whole-frame Euclidean division of the recurrence consequently forces

`a_(t+1)=a_t+e_t` for `t<K−1`,

and at the final frame forces

`V=a_(K−1)+e_(K−1)`.

This proves `a_t(j)=Σ_(s<t)E_s(j)≤t` and `V(j)=Σ_(s<K)E_s(j)≤K`. Only now is it legitimate to describe the whole recurrence as carry-free. Initial, internal, last and above-last frames are all accounted for. Empty layers and `K=1` are included.

### Independent uniqueness proof

There is also an algebraic safeguard against malicious carries. Construct canonical cumulative streams `A*` and `V*` directly from the binary event digits. Since `K<b`, their digits fit and `A*<Q^K`. They satisfy the recurrence. Subtracting the two recurrences gives

`(Q−1)(Apre−A*)=Q^K(V−V*)`.

Since `gcd(Q−1,Q^K)=1`, `Q^K` divides `Apre−A*`. Both streams lie in `[0,Q^K)`, so the difference is zero. Hence `Apre=A*` and `V=V*`. This proof never supposes that the candidate `Apre` already consists of small counts.

## 5. Exact neighbors, with all spatial and temporal boundaries

Natural `nx,ny,nz` obey

`b nx=Apre`, `X ny=Apre`, `Y nz=Apre`.

Each allowed source index is at least `1+A+AB` within its frame, so these exact divisions are integral. The six streams `bApre,XApre,YApre,nx,ny,nz` put each previous count at exactly its physical neighbors.

Both x faces remove row wrap; both y faces remove plane wrap; both z faces remove wrap between time frames. In particular the last frame cannot emit a shifted count into frame `K`, and the first frame cannot draw from negative time. Shifted destinations may lie on the shell, which is correct; shifted sources never do. Multiplicity does not change this positional argument.

Define the available-before-own-depletion stream

`Cval=η̂R+bApre+XApre+YApre+nx+ny+nz`.

At time `t`, its exact coefficient is

`c_(t,v)=η(v)+Σ_(w~v)a_(t,w)`.

Since previous counts are at most `t`,

`0≤c_(t,v)≤20+6t≤6K+14<b`.

Consequently these sums are genuinely carry-free. The repeated initial stream `η̂R` has disjoint frames, so it introduces no coefficient collisions. No outside topplings are assumed.

## 6. Selected-site legality with repeated own firings

The full-digit mask `(b−1)E` has all the bits precisely at event slots. Expanded AND calls give

`Csel=AND(Cval,(b−1)E)`,
`Asel=AND(Apre,(b−1)E)`.

A natural slack `S` obeys

`Sub((h_b−1)E,S)`,
`Csel=6Asel+6E+S`.

Because `h_b=b/2` is a power of two, the slack mask fills exactly the lower half-radix bit positions at selected slots. Its coefficients are independently in `0,…,b/2−1` there, and zero elsewhere.

Before any carrying on the right, a selected coefficient is at most

`6(K−1)+6+(b/2−1)=6K+b/2−1<b`.

The last strict inequality follows from `b≥64(K+1)`. Nonselected coefficients are zero. Both sides are therefore digitwise equal. At an event this is exactly

`η(v)+Σ_(w~v)a_(t,w)−6a_(t,v)=6+S_(t,v)≥6`.

Prior own firings are fully charged; same-layer and future events are absent. Conversely every legal selected firing has slack

`0≤η(v)+Σ_(w~v)a_(t,w)−6a_(t,v)−6≤6K+8≤b/2−1`,

so every legal slack fits the explicit mask. No digitwise multiplication, variable-length conjunction, array oracle or unexpanded inequality is used.

## 7. Exactly the supplied signed target, including even final counts

For each axis introduce natural `h,s,ell` and a positive upper slack `g`, and enforce

`ζ=2h+s`, `s(s−1)=0`,
`ell+2sh+s=half_extent+h`,
`ell+g=full_extent`.

These uniquely give the signed physical coordinate and its local coordinate `0≤ell<full_extent`. POWER produces

`point=b^(ell_x+Aell_y+ABell_z)`.

Introduce a natural event time `τ`; a separate POWER produces `timepoint=Q^τ`. Impose

`Sub(E,point·timepoint)`.

The spatial coordinate bounds give a unique exponent `j∈[0,N)`. Since `E<Q^K`, containment of the positive bit `b^(j+Nτ)` implies `j+Nτ<NK`, hence `τ<K`. No additional upper-bound clause is necessary. The interior mask forces the target off the shell.

It would be incorrect to retain the binary theorem's `Sub(V,point)`: an even positive final count has no low bit. Selecting a genuine event removes that parity defect. The separate two powers also retain the degree bound without placing the product `Nτ` in one exponent.

## 8. Soundness as an ordinary legal sequence

The recurrence determines all prior and final counts from the finite event sets. The selected legality equations prove every member of a layer unstable at the beginning of that layer. Serialize the finitely many members in any order. Before an unprocessed member fires, other members' firings only add chips to it; they do not decrease its height. It remains unstable. Induction through all `K` layers gives a finite ordinary legal sequence with odometer exactly `V`, including the marked target event.

A site can occur again in a later layer. The resulting object is neither an overfiring supersolution nor a hypothetical globally stabilizing odometer. Endpoint stability, maximality and eventual global termination are not required.

## 9. Completeness for every finite repeated prefix

Given an ordinary finite legal sequence containing the target, stop when the target first fires and take its positive length as `K`. Put one event in each layer. Choose `L` large enough for both fixed-input conversions and `32^L≥64(K+1)`. Enlarge `tx,ty,tz` until the finite firing support and target lie strictly inside the centered box, and the four spatial SPREAD margins hold. These three independent period-aligned extents are unbounded; the physical patch is automatically interior.

Pack the actual prior counts, event bits and total counts. They satisfy the masks and recurrence. Their exact neighbor counts and legal selected slacks satisfy the legality clauses and all carry bounds above. Choose `τ` to be the target's event layer. All target and physical decoding witnesses have their prescribed values. Completeness of the explicitly expanded arithmetic macros supplies their remaining positive witnesses.

This proves the exact unrestricted target-firing equivalence. No one-shot property of a loader is required to pass from this theorem to ordinary firing on the same physical-code inputs.

## 10. Macro semantics, domains and accounting

All arithmetic macros are written in full in `build_repeated_certificate.py` and emitted in `evidence/polynomial-dag.json`. The source notes list their complete equations. Each POWER uses the inherited constructive Pell characterization with positive-index shift `k=e+1`, and contributes 26 positive leaves and fifteen equations. Each Sub contributes three such POWERs and five further positive leaves. Each AND contributes three Sub calls and three additional natural adapters. Each SPREAD contributes three direct POWERs, one AND and four further leaves.

The domain proof is well-founded: positive dimensions first validate the base-32 inputs; positive `L` makes `b=32^L≥32`; the exact-half clause gives `h_b≥16`; the growth clause gives the stronger bound. Conversion gap equations make both conversion exponents nonnegative. Positive spatial dimensions and spread gaps then make all row/plane/copy radices powers of two at least two and all exponents nonnegative. The box mask, repetition and streams are natural. In particular `(b−1)` and `(h_b−1)` are nonnegative before their Sub interfaces are interpreted. The signed target exponent uses only bounded nonnegative local coordinates, and `τ` is a natural adapter. All Sub extraction powers have natural mask and value arguments. No POWER theorem is used at a negative exponent or a base below two.

The counts are fixed syntactic facts, not claims of minimality. No witness is allowed to be zero: every mathematical natural is represented by a strictly positive leaf minus one. Padding multipliers and Pell `a,β≥2` use strictly positive leaves plus one. The final output is the sum of all residual squares, so over positive integers it vanishes exactly when every clause holds.

## 11. Separators and remaining scope

The previously excluded valid physical input is now accepted: zero tile, patch shape `2×1×1` with digits `[12,4]` (`D=140`), target `(1,0,0)` with codes `(2,0,0)`. The legal sequence is `origin,origin,target`, with counts `[2,1]`. A binary prefix cannot reach the target, but this certificate has the three singleton event layers and the correct own-depletion term. Taking the origin as target also explicitly tests an even final count.

Two adjacent height-five sites still cannot manufacture a first firing: the forced zero initial frame gives no previous-neighbor support. A height-five periodic background plus one added chip still permits the one-step target certificate, although it has no finite global stabilization. Thus the extension does not accidentally impose stabilization.

There is no identified mathematical gap in the recurrence, conversion, geometry, selected legality or target clauses. The separate review directories state precisely what was independently checked. The inherited constructive Pell dependency remains explicit. Universal-machine loader identification and a raw machine-program-to-physical-code compiler remain separate tasks; this theorem concerns the ordinary physical input itself. No finite-fold representation, uniqueness of witnesses, or real-witness equivalence is claimed. No article or publication has been produced.
