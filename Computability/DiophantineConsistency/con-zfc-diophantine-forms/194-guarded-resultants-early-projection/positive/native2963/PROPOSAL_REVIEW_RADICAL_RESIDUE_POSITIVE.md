# Four-root radical/residue reduction: ten positive unknowns

The arriving ten-positive equation is supported by its ordinary proof and finite replay: **131 live binary operations, exact degree 1152**. Its literal nonnegative-domain translation uses **141 operations** at the same degree. This is a useful variable-count tradeoff beside the nine-positive equations, not a smaller operation-count replacement for them.

The reviewed archive is `con-zfc-radical-residue-2026-10-23.zip`, arrival `440dd03ab8`, SHA256 `7d10ee7e2186b82d660d218137added7a14e3463390845fc37e1228eddbd9394`. The original 108-file extraction and all 107 manifest entries were authenticated before/after scratch checks. [Detailed receipts](data/radical-positive-review.json) cover only the positive component; the integer forms are reviewed separately. No Lean work was performed.

## Why this four-root construction works

The ten positive inputs are `j,F,alpha,i,T,X,s,n,eta,zeta`, with `Y=q³s`. It uses the complete compact44 tuple `beta,K0,MC,MF`, `beta=2^590069-1`, with MF already shifted. The four rational squared roots before scaling are the first Pell radicand, normalized strong radicand, adjacent-coefficient auxiliary radicand, and the main Pell radicand divided by `H²`. All polynomial denominator-clearing scales are strictly positive.

A rational sum of four square roots does not generally force their rationality, even if its full signed sum is nonzero. Here the proof supplies the stronger condition required by square-class independence: **every nonempty signed subset sum is nonzero**. If `cT-R=0`, the ordered positive roots are `d/H,y,t,f`; otherwise they are `d/H,t,f,y`. Each successive root exceeds the sum of its predecessors. Distinct square-class character averaging then forces every root rational at a rational norm zero. The three integer radicands give integral roots; adjacent-coefficient Pell descent makes the auxiliary ordinate integral.

The initial proof-only transport/main coordinates may be rational. A uniform root majorant makes the transport coordinate positive without assuming its integrality. This first proves `Bt>0`, then `C>0`, then the native bound `3q<R<q⁴-2`. First/main Pell classification supplies `c>8q⁹>2R` and `c>2p`; the signed strong/auxiliary index theorem therefore yields `p=R` using the absolute main root. This occurs before forcing the main-root sign or either missing transport residue.

The merged equality initially yields only `q⁵ | H(q-1)(q⁴X-v)`. The valid cancellation is against the **q-power**: `H=3 mod q`, `q=2 mod 3`, and `gcd(q,q-1)=1`. First-Pell recurrence and the strict index interval then give `2m=R+1`, so `q⁵|v` and `q|X`. The remaining weaker conclusion is exactly `H|(q-1)(d*-X-ac)`. The proof deliberately retains the possibly shared factor of H and `q-1`.

The new Archimedean argument then separates it. With `r0=(R-1)/2>=24`, elementary Pell growth gives `c/k>X^r0/2`, while `c/k<Y+1`. Thus `Y>q*2^R` before identifying X with the power. Main Pell polynomial congruences imply that a negative main root would make `(q-1)(1+2^R X)/H` a positive integer less than one. For the positive sign, `(q-1)(2^R-X)/H` is an integer of absolute value less than one. These contradictions force the sign and `X=2^R`, yielding the unmultiplied main residue. Integrality of the proof coordinates now gives the exact transport residue too. No false coprimality of H and `q-1` is used.

Canonical completeness imposes no new divisibility on Y: existing `Y=q³s` supplies the tenth input. The transport weight is chosen after the strong/auxiliary pair. Its canonical carrier gives `r>2L`, while `|gamma|<L`, so the final n remains positive even if this temporary gamma is negative. The authentic old transport coordinate is restored as `z_old=z_new+1`, and the authentic auxiliary coordinate as `T_old=f*T`. These shifts were checked explicitly.

No mathematical defect was found in the new reduction. Its final native compiler/refutation calibration is an inherited ordinary theorem, not discharged by finite checks or a new internal Lean derivation.

## Finite evidence

All four positive-component programs (`build.py`, `independent_check.py`, `rebuild_coefficients.py`, `local_checks.py`) passed normally and under `-O`, with the optimization flag inherited by any children. Both positive/natural literal circuits rebuild byte for byte.

The independent checker multiplies the actual sixteen conjugate factors exactly, obtaining the 495-term cleared norm, and verifies all 62 named polynomial cuts. All 131 gates and inputs are live: 77 multiplications, 37 additions, 17 subtractions. The unique degree-leading norm monomial is `delta⁸ Z¹⁶`. The coefficient of `j^672 i^48 eta^112 X^96 s^192 T^16 alpha^16` is `12^16(3 beta)^672>0`, so degree 1152 survives actual coefficient specialization.

All four compact44 numeral payloads reconstruct exactly. Supplementary controls include the genuine noncoprime kernel example `gcd(H,q-1)=31`, a four-radical cancelling subset, and rejection of a changed final norm coefficient. These diagnostics supplement the universal proof; they are not a consistency test.
