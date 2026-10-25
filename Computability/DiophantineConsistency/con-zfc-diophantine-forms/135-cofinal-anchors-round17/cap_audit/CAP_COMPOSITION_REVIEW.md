# Independent cap and composition audit, round 17

## Final signed selection after the strict-budget extension

The final signed construction additionally aligns K=x, merges the old K and x-index Pell pairs, and tightens exactly the u/vq beta quotient ranges. The frozen ordinary delta is `direct/STRICT_BUDGET_PROOF.md`, read together with `ORIENTATION_FIRST_PROOF.md` and `PROOF_315.md`. This final extension is approved on the same inherited arithmetic/calibration boundary.

Final primary endpoints are:

- strict_dimension_centered: 282 integer variables, 192 quadratic rows, degree 4, 5,491 monomials, height 128,446.
- strict_grouped_centered: 287 integer variables, 197 rows, degree 4, 4,313 monomials, height 128,446.
- strict_sparse_centered: 309 integer variables, 219 rows, degree 4, 3,922 monomials, height 128,446.

The additional measured diagnostic strict_separate_centered has 283 variables, 193 rows, degree 4, 4,890 monomials and the same height. Earlier 285/286/290 and 315 results below document intermediate audits, not the final signed selection.

The independent signed checker now binds the complete input-raw metadata delta, the two tightened range indices, all three power requests at the merged x index, every exact coordinate alias, deletion of only the duplicate principal norm and its A*Y wire, absence of live old-pair references, and the new count of fourteen independent pairs and eighteen power requests. It supports combined, separated, grouped and individual coordinate residue rows. Four additional mutations target the strict alias, duplicate deletion, range index and merged-request ledger. All four strict signed endpoints now pass normally and under Python -O with byte-identical result files; each rejects all eleven controls and has every quartic coefficient independently collected.

The ordinary strict proof has no circular sign dependence: q^x first excludes x<0, then the first endpoint gives x>=F+1>=2 before interpreting B^x or the self-radix power. Thus q>=B^2>V0 still precedes the factorial interpretation. After factorial, R<2x and x>2^32 prove the same local-source bound R^E<2^x. All lower indices are at most K=x, and the k! valuation loss remains at most k-1<K. Canonical beta quotients are at most x/2<x, proving completeness for the two strict ranges. The final document-only CRT correction is included: ordinary positive representatives may equal 2N^2, and the dominant a is selected from a0+2N^2 or a0+3N^2 for 0<=a0<N^2, yielding 2N^2<=a<4N^2 with either desired parity. The explicit estimate F=t!>=t and B^2>F^2+t proves the fixed factorial index bound. The selected signed source uses its square-shell constructor, whose literal even codes give h>=2a^2 and h=1+a+b modulo 2; the parity-controlled representative choice and private odd-auxiliary completeness remain valid. Individual residue rows work because their signed small errors have absolute value at most 2 or below 2W, both below |A-1|.

## Current verdict

The strict natural semantic-anchor construction is mathematically sound, conditional on the explicitly inherited arithmetic/Horn/calculus interpretation. Its new cap theorem, the exact frame, all requested indices, consecutive-coordinate orientation, raw-sign and factorial bootstrap, aligned amplification K=x, stricter beta quotient ranges, cofinal root choice, and CRT-lift completeness have been independently reviewed. No new end-to-end proof-assistant derivation is claimed.

The conservative unrestricted-integer 315-variable semantic-anchor construction is also mathematically sound on the same inherited boundary. Its squared cap, signed center, odd private parameters, semantic-anchor reuse and parity-controlled CRT completeness have been reviewed. The frozen orientation-first extension in `direct/ORIENTATION_FIRST_PROOF.md` has now passed the ordinary semantic review as well. This proof covers the combined, separate and grouped residue variants (285, 286 and 290 variables).

## Independently checked natural endpoints

- strict_natural229: 229 natural variables; 179 quadratic rows; degree 4; 9,184 collected monomials; height 83,954,634.
- strict_natural230: 230 natural variables; 180 rows; degree 4; 6,858 monomials; height 83,954,472.
- strict_natural228: 228 natural variables; 178 rows; degree 4; 9,866 monomials; height 2,445,412,949,744. This is a variable-saving/high-height tradeoff, not a Pareto improvement in every measure.

Each uses the identical 334-variable, 284-row natural raw graph, with 13 independent consecutive Pell seeds, one already-needed ordinary-coordinate semantic anchor, and 23 actual semantic frame atoms. The frame offset is exactly 15. The three projections have respectively 105, 104 and 106 certified natural eliminations. Each includes two non-coefficientwise-positive restorations whose exact rational square certificates were checked.

`check_natural.py` was independently written for this audit and imports no producer or inherited compiler. It verifies the literal semantic frame and complete requested-index coverage; the actual constructor subgraph establishing the anchor lower bound; all seed and private anchor norms; all private anchor progressions and positive multipliers; the positive lower-scale norm; all six exact power residue rows and their moduli; all eleven modular digit rows, their remainders and exact output bound; the common-root equation; strict K=x and the two tightened ranges; raw requested-index positivity; every affine normalization; each exact monic natural restoration and rational sum-of-squares certificate; every target row and every coefficient of every collected quartic.

Nine mutations are rejected separately for each endpoint: merged-cap sign, missing frame atom, wrong anchor index, wrong seed norm, raw row, inverse restoration, negative square weight, target row and final coefficient. All required checks use explicit exceptions, not removable assertions. Normal and Python -O results are compared.

## One-row cap theorem

For W>=3, 2<=H<W, A-1>W^3, r<=W-2 and 1<=k_i<W, the row

    V = H + sum (y_i-k_i)^2 + (A-1)Q, Q>=0

provides the omitted H<=V premise of the complete indexed-Pell certificate. Hence V=Y_H(A)>=2A>2W. If an actual Pell index j_i>=H, then y_i>=V and (y_i-k_i)^2>V, contradicting the row. Consequently every j_i<H<W. Reduction modulo A-1 gives a nonnegative error sum smaller than W^3, hence zero. This does not assume the requested k_i are below H in the soundness direction.

For completeness H>=2 max k_i is enough: Y_(2s)=2X_sY_s>2(A-1)Y_s^2, while each ordinate error square is at most Y_s^2. The leftover exceeds H and is divisible by A-1. No even H or doubled frame is required. The source's literal J constructor has J>=2a^2. A CRT-preserving lift a -> a+N^2 makes J>2N^4>4N^2>=2 max k_i. The private scale and full anchor are chosen only after the semantic data; no private witness is included in the semantic frame.

## Strict amplification and binomial composition

After the independently ordered positive-power/factorial bootstrap, x>=2+(t+1)y, y>=F+1, F=t! and t>=12 imply R=2+t+x+y+F<2x and x>2^32. At E=2^23, the base inequality (2*2^32)^E<2^(2^32), followed by (1+1/x)^E<2, proves R^E<2^x. Thus K=x is sufficient.

Only the beta quotient columns u and v use lower range index x rather than x+1. In canonical finite-refutation witnesses they are (x-S)/(1+(i+1)y) and (x-Sp)/(1+(i+2)y). Nonnegative numerators bounded by x, denominators at least 2 and x>0 give u,v<x. Soundness is strengthened, not weakened. Equality k=K in the CRT precision argument is harmless since the factorial-valuation loss is at most k-1<=K-1.

The self-sized radix uses actual representatives, so their completeness lift does not invalidate any digit bound. The exact common-root modulus N*q^x is divisible by every required denominator modulus. Its linear congruence for the free center A is soluble by gcd(q+1,M)=1 and the parity of (q+1)^2+1 when M is even.

## Signed squared anchor and negative centers

A negative A cannot be inserted into the natural merged cap: the factor A-1 would reverse its nonnegative-remainder inequality. The signed construction instead retains separate cap and residue rows. Its squared cap is

    C^2 = h^2 + 1 + sum(other y_i^2) + nonnegative ternary form.

This proves |C|>|h| and bounds the other absolute ordinates. The full signed comparison certificate proves |C|=Y_|h|(|A|), excluding h=0. Keeping the anchor's own residue summand is essential: for A<0 and even h, its correct ordinate is negative.

The recurrence identities X_j(-a)=(-1)^j X_j(a), Y_j(-a)=(-1)^(j-1)Y_j(a) give the correct signed residue calculation modulo A-1. A wrong abscissa at a positive exponent produces m*n^k congruent to -1 modulo T; the exact product identity and the strict |T| bound exclude that orientation. Private Pell quotients need not be natural, and the proof correctly reconstructs old positive-center private witnesses afresh instead of asserting otherwise.

## Odd auxiliary completeness: identified issue and repair

The semantic h is not universally even. The literal Cantor constructor gives h congruent to 1+a+b modulo 2. Odd auxiliary quotient J/C^2 alone would not guarantee an odd auxiliary abscissa if A were even and h odd; an odd comparison D would then conflict with D=A modulo the even abscissa.

The final 315 proof repairs this by choosing opposite parities for actual CRT representatives a and b. Since N is odd, adding N^2 preserves all residue classes and changes parity. The a representative can simultaneously be made large enough for anchor dominance. Then h and C are even, U is odd. With auxiliary index l=hC,

    J=C*Y_C(U),  Y_C(U)=C U^(C-1) modulo C^2,

so J/C^2 is odd. The auxiliary abscissa is odd and coprime to J; CRT supplies the required odd comparison center. This supplies every previously guarded private witness and is an existence argument, not an unsupported raw sign assumption.

## Independent signed finite checks

`check_signed.py` is a separate audit implementation importing only this audit's own sparse-polynomial primitives. On orientation_first/integer285 it checks all fifteen principal Pell norms and their A*y gates; the exact requested-index ledger; actual squared frame; full pooled both-coordinate residue; odd auxiliary and comparison constraints; every ternary guard and its freshness; every initial sign-inference identity; all 216 monic integral inverses; the integral translation; and all coefficients of the degree-four endpoint (285 variables, 194 rows, 6,594 monomials, height 128,446).

The same independent audit also passes `orientation_separate/integer286` (286 variables, 195 rows, 5,770 monomials, height 128,446) and `orientation_groups5/integer290` (290 variables, 199 rows, 4,949 monomials, height 128,446). Each has 216 monic inverses; the final translations affect respectively 78 and 71 coordinates. Normal and Python -O outputs agree byte-for-byte for all three signed endpoints.

Seven independent mutations are rejected: squared cap, pooled residue, odd auxiliary multiplier, sign identity, inverse restoration, translation and collected coefficient. The unchanged Horn factorization is deliberately not misrepresented as newly re-proved by this script; its exact identities and interface preservation are covered by the separately reviewed inherited algebra auditor and the complete-source checker. The new cap rows do not alter that factorization's internal source variables.

## Final orientation-first semantic verdict

The frozen `ORIENTATION_FIRST_PROOF.md` closes the remaining semantic boundary correctly. The squared anchor is first interpreted with signed nominal h, giving actual index |h| and excluding h=0 without raw syntax positivity. Both-coordinate pooling forces the exact Pell polynomials at the original signed center. Its small-residue estimate includes the abscissa contribution: E<4mW^2+4m<4W^3 for m=15 and W>=258.

A negative requested exponent at a base n>=2 would give m*n^j=1 modulo T. The strict frame bound forces literal equality, impossible for j>=1. Zero exponent remains valid and gives output one. Initial q>=2 and t>=16 therefore recover the t pair, V0, F and y. The q^(x+1) request gives x>=-1, and the first endpoint excludes a negative endpoint quotient, recovering x>=F+1 before interpreting the factorial. Actual encoded representatives are nonnegative exponents of q+1 requests. The stored coordinates one less than those representatives need not be natural, and the proof does not claim otherwise.

The zero-upper-argument binomial boundary is handled correctly. After the factorial product is identified, B|C0+F^2+1 and B>F^2+1 imply C0>=1. Hence the actual self-radix sum H0>=2. Using max(1,n) for ordinary coefficient bounds and max(1,a,b,c,d) in the derived-label majorant restores all estimates even when some representatives vanish. This is not circular: the factorial digit bound uses only the earlier raw ceiling and exact powers, not C0 positivity.

The exact signed ordinary proof is approved, conditional only on the stated inherited source/calculus calibration. Completeness uses the same positive, parity-controlled CRT witness choice as the conservative 315 proof. Separate and grouped residue rows satisfy the same bounded-error argument separately, provided every abscissa and ordinate error appears exactly once; the independent checker verifies that partition.

## Limits

All these finite checks establish exact emitted syntax and algebraic equivalences, not universal arithmetic semantics by testing. The unbounded arguments above and the explicitly identified inherited Pell, factorial, CRT, beta/Horn and calculus calibration arguments supply the meaning. No consistency assumption, global optimum or literature-wide priority claim has been used.
