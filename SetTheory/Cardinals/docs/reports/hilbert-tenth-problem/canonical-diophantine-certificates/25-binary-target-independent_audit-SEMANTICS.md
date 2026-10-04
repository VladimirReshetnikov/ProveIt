# Independent semantic review of the binary target tableau

Date: 4 October 2026. **PASS for the stated relation: existence of a finite legal prefix containing the supplied target in which every site topples at most once.** This is conditional on the already audited physical decoder and arithmetic macros, including their pinned constructive Pell dependency. No mathematical gap was found in the new tableau. This review does not certify the emitted DAG, arithmetic ledger, exact polynomial degree, a particular universal loader, or ordinary unrestricted target firing.

The submitted architecture and builder were read only as text. No submitted builder, submitted checker, or arithmetic schedule was executed or imported. The separate fresh script `semantics_check.py` implements finite probes from scratch.

## 1. Recurrence and every time boundary

Write `Apre = sum(a_t Q^t)` and `E = sum(e_t Q^t)` for `0 <= t < K`, with both frame coefficients subsets of the strict-interior low-bit mask `I`. The three Sub clauses give these support bounds as well as one low bit per base-32 spatial slot. They similarly put `V` inside a single frame.

In `Q(Apre+E) = Apre+Q^K V`, the left side has base-32 digits at most two. The right side has digits at most one, since the supports of `Apre` and `Q^K V` are in disjoint frames. Thus neither side carries. The low frame gives `a_0=0`; frames 1 through `K-1` give `a_t=a_(t-1)+e_(t-1)`; the highest frame gives `V=a_(K-1)+e_(K-1)`. There is no hidden condition above frame K, since all terms already have bounded support.

Induction shows that `a_t` is exactly the union of all earlier layers. The binary condition on each next `a_t`, and finally on `V`, forces every layer to be disjoint from every earlier layer. The final mask is essential for this conclusion at the last transition. There is no cyclic-time loophole. `K=1` is covered: the equation directly forces `Apre=0` and `E=V`. Empty layers cause no difficulty. `K` is a positive existential witness, not a fixed or supplied finite bound.

## 2. Spatial shifts and frame separation

For a source site `(x,y,z)` in the strict interior, each index shift by `+/-1`, `+/-A`, or `+/-AB` is the corresponding physical neighbor in the same frame. The source x-face zeros exclude row wrap, the y-face zeros exclude plane wrap, and the z-face zeros exclude frame wrap. Both lower and upper faces matter. In particular, a source in the last time frame cannot overflow into frame K under any positive neighbor shift.

The natural quotient equations `32 nx=Apre`, `X ny=Apre`, and `Y nz=Apre` are exact, not truncated divisions. All occupied exponents are at least `1+A+AB` in frame zero, and the higher-frame terms have still larger exponents, so the required divisions are possible. The upper-face bounds prove that all six resulting streams remain below `Q^K`.

The inherited physical decoder gives `0 <= eta_hat < Q` with base-32 digits at most 20. Multiplication by `R=sum(Q^t)` places exactly one copy into each time frame. This gives no overlap among frames. Adding the six neighbor streams gives digits at most `20+6=26`, so no arithmetic carries obscure the height at any slot. The field includes shell sites too, which is harmless because firing is restricted to the strict interior.

## 3. Selected legality, slack, and absence of self-support

Since `E` has one low bit at each selected slot, `31E` fills exactly that slot's five binary bits. The audited AND therefore selects the entire value of `Cval` exactly at the newly firing sites.

Each `Sub(E,Li)` makes `Li` a low-bit subset of the firing mask. The extra `Sub(E,L3+L4)` prohibits those two planes from overlapping: an overlap would make base-32 digit two, whose bit is absent from `E`. The permitted slack digits are exactly 0 through 23. Consequently `6E+L` has digits at most 29, and has zero digits outside the selected slots. The other side has digits at most 26. Thus the final equality is coordinatewise, and forces selected heights to be at least six, with actual slack at most 20.

The absence of a `-6 Apre` term in `Cval` is correct specifically at selected sites: recurrence already gives `Apre_t(v)=0` when `E_t(v)=1`. A newly firing site's actual height is therefore its initial height plus one chip from each previously fired neighbor. It cannot use its own earlier firing or any current/future layer's support.

Every member of a layer is unstable at the layer's beginning. Serializing a finite layer in any order preserves legality of its not-yet-fired members, since other topplings only add chips to them. Inducting on layers produces a genuine legal finite sequence with binary odometer exactly `V`, including the target. This is stronger witness identification than the earlier stabilizing-supersolution certificate. Two adjacent initially height-five sites cannot start a nonempty layer and cannot support each other through the equation.

## 4. Exact target and signed input

All target decoding variables are natural adapters. `s(s-1)=0` therefore gives precisely `s=0` or `s=1`; `zeta=2h+s` is the unique parity decomposition. The translation equation gives `ell=half_extent+h-2sh-s`, so even codes represent `h` and odd codes represent `-h-1`. The positive upper gap gives the exact strict bound `ell<full_extent`, while the natural adapter gives the lower bound.

The three local bounds make `ell_x+A ell_y+AB ell_z` the unique mixed-radix index of the supplied physical target. `POWER(32,index)` is a single low-bit point mask. `Sub(V,point)` places that exact point in the actual fired set. Because `V` is already a subset of `I`, a target on the shell cannot be falsely accepted; this is not a completeness obstruction because a valid finite prefix permits enlargement of all box dimensions.

The builder visibly implements ten right-associated Cantor equations over the eleven intended natural fields, in the same convention as the accepted earlier decoder. All sign and position clauses in the architecture occur in the builder.

## 5. Every new POWER domain

The following are mathematical consequences of the whole conjunction, which is sufficient; they need not hold for arbitrary unsatisfying witness assignments.

- The inherited positive dimensions and box multipliers at least two give `A,B,C>=4`, `X=32^A>=2`, `Y=X^B>=2`, and `Q=Y^C>=2`
- `time.endshift` has base `Q>=2` and positive exponent `K`
- The repetition variable is natural, and its equation uniquely gives `R=(Q^K-1)/(Q-1)`; thus `IR`, `I`, `pre`, `new`, and `final` are nonnegative masks/values
- The new neighbor quotients are natural. `available` is a sum of nonnegative expressions, and the other AND operand `31*new` is nonnegative
- AND's three subset calls use natural common/difference witnesses and the nonnegative sum of the two difference witnesses, as in the inherited proof
- All legality subset masks are `new>=0`; each `Li` and `L3+L4` is nonnegative
- `target.point` has base 32 and nonnegative exponent `ell_x+A ell_y+AB ell_z`. Exponent zero is allowed by the inherited POWER theorem, even though its point is subsequently excluded by the interior condition
- The target subset uses `final>=0` and the positive target point
- Every such Sub call internally has base 2 and exponent `mask+1>=1` for its radix, then bases `radix>=2` and `radix+1>=3`, and exponents `value>=0` and `mask>=0`. The zero-mask/zero-value branches require no extra disjunction

No new POWER call needs a negative exponent, a base zero or one, or an unproved nonnegative expression. All inherited SPREAD/physical geometry domains remain as in the previous audit; enlarging the three independent box multipliers meets all four strict spread margins simultaneously.

## 6. Completeness and the exact limitation

Given a finite legal prefix with at most one firing per site that includes the target, stop at its first target firing and choose one singleton layer per toppling. Take `K` equal to that finite positive length. Choose a sufficiently large centered prism of the paid form so that the finite fired support and patch lie strictly inside and all four spread bounds hold. The historical sets, singleton layers, and total fired set satisfy the recurrence and every support constraint. Each selected site's height lies between six and 26, so its slack lies in 0 through 20 and has permitted planes. The signed target clauses have their intended values. The complete inherited arithmetic macros then provide their positive witnesses.

No endpoint stability, later termination, least-action argument, or stable exterior inequality is needed. The finite sequence itself is the soundness witness. A valid certificate allows continuing infinite evolution after the target firing.

**Ordinary target firing is strictly broader.** Take zero periodic background; patch shape `2 x 1 x 1`; patch heights 12 at `(0,0,0)` and 4 at target `(1,0,0)`; all other heights zero. These are valid patch digits. The origin is initially the only unstable site. Its first firing leaves the origin at six, the target at five, and every other affected site at one. Hence no as-yet-unfired site can fire, so no binary prefix reaches the target. Ordinary legal evolution can instead fire the origin again, raising the target to six, and then fire the target. The sequence is `origin, origin, target`.

For the literal eleven-field physical interface this example has `(p,q,r)=(1,1,1)`, tile `T=0`, `(d,e,f)=(2,1,1)`, patch `D=12+4*32=140`, and `(zeta_x,zeta_y,zeta_z)=(2,0,0)`. This explicitly separates the audited relation from ordinary target firing within the admitted input class.

The conditional all-site-one-shot-loader sentence is reasonable, but remains genuinely conditional: identifying a particular loader, showing the necessary one-shot property, and paying a raw-program-to-physical-code compiler are not consequences of this tableau. The source does not overclaim these obligations as proved.

## 7. Fresh finite probes and source pins

`python semantics_check.py` passed:

- 4,368 candidate packed recurrence assignments on two independently encoded sites with K=1,2,3, including empty and overlapping layers; exactly 29 valid assignments
- 372 full 3D neighbor-stream fixtures across three boxes and K=1,2,3, checking exact six shifts, frame separation, and 100,480 coefficient bounds
- 1,728 selected-legality/bitplane assignments, including all values 0 through 26 and all five-plane combinations
- 2,624 signed target and strict-bound cases, plus mixed-radix point uniqueness checks
- Both the repeated-firing separator and the adjacent-height-five mutual-support rejection

These finite tests do not establish the general theorem; the preceding argument does so subject to the stated inherited dependencies. See `semantics-receipt.json` for the checker hash and counts.

Read-only reviewed pins:

- `ARCHITECTURE.md`: `dabbe1685bb050eca578c29472a00426c940df6002c383fe5c3a558797bf93c9`
- `build_target_certificate.py`: `6a9ced103676ce7ba0b052e00779177fb522101fc5479866273e3908d299c975`

The frozen architecture was reread at 04:39 UTC. Its only changes from the initially reviewed hash `7c211a76d947abbe20e1045662edad2a24abacc3765774e96a730e90bd165745` are the two obligation-status items in section 8, reporting the completed author-side emission and pending independent review. Replacing those two items in memory with their previous text reproduces the exact old SHA256; thus the mathematical proof is byte-identical. The builder hash is unchanged. The semantic verdict is unaffected, and no upstream files were modified.

Reviewing these two text sources is not an independent emitted-source reconstruction. Agreement with the emitted DAG and its fixed-shape ledger and degree is covered by the parent audit's separate reconstruction, not by this semantic report.
