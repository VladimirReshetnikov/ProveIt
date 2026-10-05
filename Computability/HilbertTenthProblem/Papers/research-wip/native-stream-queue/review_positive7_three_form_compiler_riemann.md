# Independent complete-source review of the positive7 three-form compiler

The complete three-form compiler passes independent mathematical and literal-source review, with the single editorial correction retained in Review remark 1 below. For `r>=1`, its certificate is `(277+50r+lambda)M+(550+62r)A`, and its complete single polynomial is `(300+50r+lambda)M+(595+62r)A = 895+112r+lambda` operations, where `lambda=floor(log2(62+8r))+popcount(62+8r)-1`. It uses 23 comparisons and `96+8r` positive witnesses. The changed relation preserves the accepted-word/ordinary-input projection. It is not the same polynomial or the same supplied-witness relation as the preceding four-selection source.

All 3,496 saved rows for `r=1,2,4` were independently checked as inert records. Every row matched an explicit required operation record or a pinned predecessor/local record, and every row and supplied port is syntactically live and topologically closed. The full primary proof and 249-line emitter were read as text; the local three-form proof and Aristotle's independent proof/ledger companion were read in full, including their final qualifications. No supplied or frozen helper was executed or imported, no source/coefficient array was arithmetically evaluated, and no degree was propagated. A fresh reviewer program ran once solely for literal matching, metadata, operation-label counts, bindings, topology and liveness; its first receipt is frozen with this review.

## 1. Fixed coefficient recipe and exact changed ports

The inherited matrix `S(P)` fixes the right vector `w0=(2q,p-t,-2s)` when `pt-qs=1`: direct hand multiplication gives `2q(pt-qs)`, `(p-t)(pt-qs)`, and `-2s(pt-qs)`. The inverse relator has the negative corresponding invariant, so its difference matrix has the same row kernel. If this vector vanishes, the integral determinant condition forces `P=I` or `P=-I`; the specified zero `E` matrices handle these cases without dividing by zero.

For nonzero primitive `w`, permute coordinates so `w1!=0`, set `g=gcd(w1,w2)>0`, and choose `a*w1+b*w2=g`. Since `gcd(g,w3)=1`, a row `(x,y,z)` orthogonal to `w` has `g|z` and equals

    (b*x-a*y)*(w2/g,-w1/g,0) + (z/g)*(-w3*a,-w3*b,g).

This proves the integral row-lattice basis, including signs and zero secondary coordinates. Undoing the same permutation gives the two original-coordinate rows and integer matrices `E_plus,E_minus` with `S(P^sign)-I=E_sign*[u;v]`. Composing the two rows with the fixed decoder `C` gives the signed input forms. All gcd, Bezout and division steps prepare fixed integer numerals and add no runtime witness or division.

The prescribed offsets make every coefficient of `A_j=L_j+lambda_j*S4` a positive integer. Consequently `0<A_j<=M*S4<=M*S` for arbitrary positive history words, before any digit argument. The `5+22r` fixed roles are precisely `alpha,gamma,K,kappa_minus_one,form_bound`, eight positive form coefficients, two positive offsets and twelve signed `E` coefficients per relator. They are correlated by one actual-relator/full-alphabet recipe; allowing arbitrary independent role values would not establish this compiler theorem. Zero/unit coefficients remain charged in the uniform source. No numerical universal relator list is materialized here.

The saved sources retain the eight paired letters' exact 52 raw-coordinate fields. Each of the `2r` relator signs has only fields `0,1,2`, meaning selected `S4,A1,A2`. The two input forms are computed once per relator and used by both signs; the two signs share their offset roles but use their respective six `E` roles. The static audit verified these precise consumers and their order, not merely matching field totals. Each offset role has exactly two runtime consumers; every other fixed role has one. All selected hats are explicitly un-hatted and enter the selected-output total.

## 2. Positive pretyping and simultaneous projection proof

There are seven positive history words, six positive terminal coordinates with terminal 7 aliased to `F_1`, `8+2r` positive selector hats, `52+6r` positive selected-output hats, two positive slacks and exactly 21 inherited native auxiliaries. Thus there are `96+8r` witnesses. The ordinary input is `x>0`; its program slice and initial vector remain the inherited ones. The first six rows compute the input and its mass exactly as in the predecessor.

The changed guard is `M*S+Ztot+g=P`, with a paid multiplication by `M`. All raw selector and selected-output values are nonnegative from their positive hats. `D=S0+height_slack`, `B=K*D`, `J=sum selectors`, and `P=(B-1)J+1` are computed. The fixed dyadic `K` exceeds `Cmass`, the alphabet size and `3M+1`. At a zero, the guard forces `P>1`, `J>=1`, `B<=P` and `M*S<P`. Thus every original history, formed input and selected output is below `P`. The inherited elementary inequalities also bound `D`, `J`, all selectors and masks below `P`. This typing is established before deriving any no-carry property of a form. Off the guard locus the native packs are still nonnegative, so their computed input hats have the required positive domain.

The native lane partition is exactly `8+2r` Boolean selector lanes, `52+6r` selection lanes, one aggregate range lane and one dyadic-height lane, giving `ell=62+8r`. The prescribed native interface first yields dyadic `P`; its last lane makes `D` dyadic, hence `B` is dyadic. The repunit identity then gives `P=B^n` and the length-`n` repunit `J`, with `n>=1`. Since the alphabet size is below `B`, the Boolean checksum is carry-free and forces exactly one selected letter per cell. At this stage the form lanes certify selection of canonical digits of the whole form words, without yet asserting that those digits equal forms of the individual history digits.

The simultaneous induction closes that gap. Reducing the seven recurrences modulo `B` fixes the lowest history digits as the initial state because `S0<D<B`. There is no incoming carry. Its subset mass is below `D`, and each positive form value is at most `M*S0<MD<B`; these are therefore the actual lowest formed digits, with no outgoing form carry. Uncentering the selected forms and applying `E` gives the genuine relator difference. Together with the unchanged paired action and common positive baseline this yields the genuine positive update, whose total is below `Cmass*D<B`.

For the inductive step, remove known lower recurrence coefficients. The preceding genuine update has total below `B`, so the next canonical history digits are recovered without coordinate wrap. Earlier state masses were below `D`; hence there is no incoming carry in their aggregate. The recovered current mass is already below `B`, and the aggregate AND lane forces it below `D`. Only after this recovery are the current form digits interpreted: their earlier coefficients had no carries and their new values are at most `M*(D-1)<B`. Selection, uncentering and the fixed factorization then recover the actual action at this cell. Higher, still unrecovered action coefficients may be signed; they cannot affect the lower modular recovery. The top recurrence coefficient fixes the genuine positive terminal. `F7=F1` imposes the intended acceptance equality; initial coordinates 3 and 1 differ, so excluding duration zero loses no accepted input.

For positive completion, choose dyadic `D` above all state masses of an accepted finite word. All actual history and formed coefficients are then below `B`, and their selected outputs can be supplied with positive hats. A paired-letter cell contributes at most its mass to `Ztot`; a relator cell contributes `S4+A1+A2<=(2M+1)` times its mass. Therefore `Ztot<=(2M+1)S` and `S<=(D-1)J`, so

    g=P-M*S-Ztot >= [(K-3M-1)D+3M]J+1 > 0.

The native converse supplies fresh positive auxiliaries at the new packs and scale, and the recurrences telescope. This establishes both directions of the ordinary-input projection. The new fields, fixed `K`, global slack and native scale may change the witness assignment. No all-ring identity or witness-by-witness equivalence with the predecessor is used.

## 3. Complete literal source and fanout audit

The frozen JSON saves complete graphs only for `r=1,2,4`. All their source records were checked, including the exact six-row input prefix; all selector/selection unhat and checksum rows; the six-addition shared `S4,S` tree; the weighted guard; each form coefficient product and three-addition form sum; all three complete Horner packs; the binary-chain shape for the changed fixed exponent; the complete native block; every action append; and the complete final suffix.

The 64-row native certificate has the new header `q=16*P^ell`, `16*A_pack+12`, `16*M_pack+10`, `16*Z_pack+8`, followed by the exact 57 prefixed parent records. Its 15 comparison endpoints and 21 auxiliary names/domains are unchanged. Thus the native component is complete, including input-padding comparisons, and no old exponent remains bound to the new packs. Binary-chain verification matched row names, operations and operands against the fixed binary digits of `ell`; it did not evaluate saved powers or propagate degrees.

All 198 paired-action rows match the independently reviewed pinned local cut literally, with all 52 raw paired ports retained. For every signed relator slot, the audit checks two offset products and subtractions followed by all six `E` products and all six accumulator additions into the correct three coordinates. The final six increment names are bound to the parent suffix exactly. The 121 suffix rows match the predecessor under those increment-name substitutions: 33 fused-action rows, 20 recurrence-right-side rows and 68 finalizer rows. The six terminal products still serve seven recurrences through the shared `F_1` product. All 23 comparisons match the parent list, and every residual subtraction, square and final sum is present.

The audit covers the complete supplied/fixed/computed-name separation, operand types, topological order, final-output reachability, full boundary consumer lists and role consumers. In particular each changed raw field enters both its pack and total; subset field 0 additionally feeds both offsets; each shared input form feeds both signed-slot lanes. `S4` also feeds the total `S`. These consumer lists are stored in the companion metadata, so an unused or privately changed input cannot be hidden by a count match.

## 4. Independently derived uniform ledger

Writing `m=8+2r` and `N=52+6r`, the geometry alone costs `(m+4)M+(2m+2N+10)A`; the unchanged input/mass prefix adds `2M4A`. The six shared mass additions have exactly the old seven-history sum cost. Each pair of positive forms costs `8M6A`; each sign's offset-and-action append costs `8M8A`. The packs cost `3ell-4` of each operation, because only the top literal zero in the output pack is omitted. These disjoint counts give:

| Stage | M | A |
|---|---:|---:|
| Input, mass, geometry, masks and weighted guard | 14+2r | 134+16r |
| Shared positive forms | 8r | 6r |
| Three native packs | 182+24r | 182+24r |
| Prescribed native power | lambda(ell) | 0 |
| Native certificate | 33 | 31 |
| Exact paired cut | 30 | 168 |
| Formed relator appends | 16r | 16r |
| Fused positive lift | 12 | 21 |
| Seven recurrence right sides | 6 | 14 |
| Certificate | 277+50r+lambda(ell) | 550+62r |
| Residuals, squares and sum | 23 | 45 |

The actual saved-source counts independently match:

| r | ell | lambda | Certificate M/A | Polynomial M/A | Polynomial rows | Positive witnesses |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 70 | 8 | 335 / 612 | 358 / 657 | 1015 | 104 |
| 2 | 78 | 9 | 386 / 674 | 409 / 719 | 1128 | 112 |
| 4 | 94 | 10 | 487 / 798 | 510 / 843 | 1353 | 128 |

The `r=3,8` receipt entries are formula/shape censuses, not saved graphs. The all-`r` theorem follows from the explicit grammar and projection proof, not extrapolation from three examples. The exact saving against the plane source is `10r-1+lambda(62+10r)-lambda(62+8r)`; no monotonicity or free reuse of the changed exponent is presumed. The `r=0` branch's exact compact source digest and 903-row/96-witness count match the pinned predecessor.

## 5. Retained correction, counterexamples and boundaries

**Review remark 1 (correction to the frozen primary's liveness rationale).** Its Review remark 4 says: "Neither formula is asserted for r=0, where a new S4 producer would be unused; that branch retains the existing 903-operation source." The shared schedule itself is a counterexample to that rationale: `S=history_first_three+S4` consumes `S4` even at `r=0`, so the shared producer remains live. Only an additional separate producer without that consumer would be unused. The preceding 903-operation branch is an intentional unchanged-source choice, not a consequence of dead shared `S4`. Root accepted this correction; the frozen primary is preserved. No source, count, adopted branch or projection changes.

**Review remark 2 (unconditional selection linearity remains false).** At `B=8`, the positive four-tuple `(5,1,1,1)` has sum 8. Selecting its lowest cell gives `8 AND 7=0`, whereas summing the four separately selected values gives 8. This is a valid local counterexample and is not asserted to be a full compiler zero. The simultaneous no-carry induction is essential.

**Review remark 3 (the earlier sparse mass bound does not transfer).** At a relator cell on seven ones, `S=7` but `S4=4` and each positive form is at least 4, giving retained total at least 12. Thus `Ztot<=S` is false for the changed interface. The source uses the paid weighted guard and its proved `(2M+1)S` selected-mass bound. This local obstruction is preserved without mislabeling it as an accepted trajectory.

**Review remark 4 (scope of the two-form obstruction).** For noncentral `P`, the cited minors `2q^2` and `2s^2` prove rank two; if both `q,s` vanish, integrality and determinant one force a central matrix. The right invariant proves rank at most two. The decoder has full row rank and annihilates `(1,1,2,1)`, so the rank-two difference map on four histories has a strictly positive kernel vector. A homogeneous linear form nonnegative on every positive integer four-vector has nonnegative coefficients. A fixed linear reconstruction from two such forms would force their row space to equal the difference map's row space and both forms to annihilate the positive kernel vector, making both zero. This verifies precisely the stated unconditional two-form linear obstruction. It is not an arithmetic lower bound against affine, nonlinear, guarded or restricted-state constructions.

**Open question 5 (unclaimed extensions).** Pascal's proposed affine `D*J` centering needs an independent pretyping, carry, completion and full paid-source proof. Actual numerical universal relator data, a numerical universal gate count, source degree and arithmetic optimality remain unproved here. The earlier conservative separate-`S4` count was valid but three additions larger; the present shared schedule supplies that reduction explicitly. Inherited group-universality/native foundations retain their previous scope and are not newly re-audited as external theorems. Earlier frozen corrections and open questions remain preserved in the predecessor reports and reviews.

## 6. Frozen bindings

The primary proof is SHA256 `d1d794b3d1534b60094741ca3edc57cf0a48d099c701a0685a868abfc00bb3c2`; its emitter is `7d615b6ab34cf186a8858bd22c2c36c6816a7b72a21c2deee701d342789707b1`; its complete receipt is `8c056b9fc7b75c79677332e5dafac8de7130a2530cc79ae2fc300c862efed195`. The companion JSON pins the final local proof and independent proof/ledger review, the exact predecessor/cut evidence, inclusive text-read spans, all saved-source coverage, the fresh one-run metadata checker and its first output. All new review files are in `/tmp`; repository files, Git and all earlier frozen scientific evidence are unchanged by this lane.
