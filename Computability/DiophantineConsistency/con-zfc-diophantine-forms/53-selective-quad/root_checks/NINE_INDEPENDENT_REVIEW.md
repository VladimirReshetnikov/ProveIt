# Independent review of the parity-calibrated nine-variable construction

Reviewed 23 October 2026: `nine/PROOF.md`, `nine/build_nine.py`, the calibrated natural/positive primary and degree-certificate DAGs, and the exact signatures and register definitions in the supplied `nine/upstream/NineRatio.lean`. The construction worker reported the proof and mathematical circuits frozen before this review concluded.

## Verdict

No mathematical gap found in the new source contract, parity calibration, ratio-interface substitution, or near-square finalizer. The primary claimed point is **nine positive integers, 738 operations, exact degree 7,344,328**; the bijective natural-coordinate circuit uses 744 operations and has the same degree. This verdict is an internal independent mathematical review, not external peer review or a new kernel-checked theorem.

## Checks that determine soundness and completeness

1. **Unconditional ratio hypotheses.** With b=epsilon+2>=2, B=2^2134940 b^2, and the isolated leading source coefficient 2, Dcode(B)>0 before imposing any equation or bounding g. Consequently Scode>0 and Tcode>=0. The rearrangement R=L^2+(L-1)Scode+L Tcode+L-1 establishes R>=8 and R>=b even for arbitrarily large g. N=2^16012040 B^2966 gives N>=8 and N>=b. The natural shifts give h,s,w,i,j>0 and phi>=0. Gcap=32bB^183 is positive.

2. **Exact inherited interface.** The actual theorem `Jones1982.Nine.ratio_sound` assumes R,N>=8, b>0, b<=R,N, Gcap>0, h,s,w,i,j>0, and the four displayed conditions. It concludes N^2 divides the central binomial coefficient, b is a power of two, and 8g<Gcap. The actual `ratio_complete` instead assumes 32g<Gcap, the divisibility, and b a power of two, and supplies natural witnesses with the required five strict positivities. No equation L=N, no particular radix, and no restricted-base cofinality occurs in these theorem signatures. Every local register in Section 5 matches the supplied definitions. The margin mu is exactly the fourth ratio condition; scaling DFI by 64 preserves its square predicate.

3. **Prebinary range.** On the soundness range g<4bB^183, integrality supplies 1+g<=4bB^183. With coefficient majorant M=2^2134927 and base scale 8192M, the main term is <Z/128, where Z=B^5557. The sparse target sum is also <Z/128. Thus 0<Jcode<Z, while (B-2)Targets<Z and g,Mcode<N0. Integrality gives Scode,Tcode<N0Z=B^5741, hence Scode+Tcode<2B^5741<L=2bB^5741. None of these estimates supposes that an arbitrary b is a power of two.

4. **Sparse signed-digit normalization.** After the ratio theorem recovers binary b, the low mask uniquely decodes g into 31 digits less than b. The coefficient bound |h_s|<B/8 is stronger than the sufficient B/4 bound. Starting from zero carry, every normalized carry is -1 or 0. At a selected cell the expression 2h_s+1+carry has an allowed digit 0 or 1 precisely when h_s=0, irrespective of the incoming borrow. Thus the sparse +1 target padding tests exactly the 22 residuals, without an illicit assertion that all signed coefficients are nonnegative.

5. **Parity calibration.** For b=2^k and B=2^v, v=kappa+2k, the mask population is 206v-31k-22. The new block length has u=1+k+5741v. Therefore u+pop(Tcode)+1=5947kappa+11864k-20. Meanwhile log_2(N)=15kappa/2-10+2966v, whose double is precisely the same integer. Legendre's identity and the already proved S+T<L imply that N^2 divisibility is equivalent to absence of a binary carry. The linear parameter b=epsilon+2 permits every sufficiently large power of two. A nonzero source tuple has positive g<bB^183, so 32g<Gcap and ratio completeness applies. The nonzero assertion follows from residual 5 having constant 1.

6. **Near-square majorant.** The formulas E=t0 DC and D-1=(A^2-1)C^2 give the exact identity DF=t0^2D^3(D-1)+D. Squaring t0(8D^2-4D-1) and subtracting 64DF leaves t0^2(8D+1)-64D, at least 8D+9 because t0^2>=9. Since I<=G^2H^2 and all quantities are positive, this yields sqrt(64DFI)<V1. The other root bound follows from V0^2-a0=K^2-1>0. The quotient bound 0<v/u<=Q+H-C uses only J,F>=1 and positive Q,H-C.

7. **Finalizer.** Omega=u(2mu-1) cannot vanish. In a vanishing four-factor norm, the rational number Theta/Omega equals r0+V0r1. It is nonzero because a1 is a positive integer and |r0|<V0. The elementary identity 2(Theta/Omega)r0=(Theta/Omega)^2+a0-V0^2a1 forces both roots rational, hence integral. No square-class independence is assumed. Their integer strict bounds give Z0=Mdiv+V0V1+r0+V0r1>=Mdiv+1. The selected factor becomes n+v/u=(2mu-1)Z0. Positivity forces mu>0, integrality forces u|v, and the converse produces an integer n>=1. This is exactly the required four-condition equivalence, with no additional witness or sign branch.

8. **Domains and alternatives.** Positive translation is coordinatewise natural variable = positive variable - 1; it is a genuine bijection and does not purport to cover unrestricted integers. The separately labeled square-restricted comparison admits b=2^(2r+1), an explicitly unbounded family, so its completeness claim is also justified. The main construction needs no such restriction. The three-block comparison is not substituted into the primary metrics.

## Independent degree and gate certificate

`check_nine_degree_independent.py` reads the delivered DAGs and actual fixed coefficient payloads without importing any construction code. The calibrated certificate DAG has syntactic total-degree bound 7,344,328, attained after diagonal specialization modulo three independently tested primes:

- Modulo 101: leading coefficient 9.
- Modulo 1009: leading coefficient 360.
- Modulo 1,000,003: leading coefficient 524654.

All three equal the residues of the stated positive exact leader 2^598 a^3671828 c^448. The primary DAGs have 738 positive or 744 natural operations, verified directly from their nodes. The script records exact circuit hashes in `check_nine_degree_independent.json`.

The primary/certificate equality uses the displayed universal identities deltaV=V1^2-a1 and Theta=E0-Omega V0V1, followed by ordinary square expansion. Direct substitution proves both identities, including the correction term 64DF(H^2-1). Thus the attained certificate degree applies to the same primary polynomial; it is not an unsupported raw degree walk through a cancelling expression.

## Limits

This review imports the authenticated parent/compiler calibration and the Jones ratio theorem as stated; it does not reprove the entire K215 semantic endpoint or rebuild the upstream Lean dependency closure. The fresh script certifies finite arithmetic-circuit degree/count properties, not the unbounded Diophantine equivalence by testing. The reviewed proof supplies that equivalence relative to the identified mathematical dependencies. No global simplest-equation or unrestricted-integer nine-variable claim is supported or needed.
