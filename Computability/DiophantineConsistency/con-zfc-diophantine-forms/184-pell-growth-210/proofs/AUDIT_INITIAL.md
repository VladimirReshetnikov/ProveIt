# Independent review of the frozen CRT/index-anchor source

Source: `sources/incoming/ConZFC_CRT_Index_Anchor_215_2026-10-25/ConZFC_CRT_Index_Anchor_215_2026-10-25`, downloaded from ProveIt at commit `ef0c534c1ae1e312c61a2a9a5a3f18f5516fd42b`.

## Existing endpoint baseline

The archive name is not its minimum dimension. The frozen package already delivers P215 (215 unrestricted integers, 154 quadratic residuals, 5,660 monomials, height 91,679), P214 (214/153/5,486/1,099,511,627,852), and P213 (213/152/5,402/2,417,851,639,242,452,488,945,685). New dimension comparisons must include the P213 companion.

The inherited `python3 -B verify.py` completed with status PASS in this review. It authenticated 196 manifest files, checked the finite constructor AST, and freshly reconstructed 26 stages with byte-identical residual equations and expansions. This is a finite artifact check, not a test of the universal semantic theorem.

## Mathematical checks

The factor-count argument in the product-separation lemma handles unequal counts even when the premise side has up to 2t+1 factors: the smaller count is at most t. For equal positive count m, every elementary symmetric coefficient belongs to [1,F], so corresponding differences have absolute value at most F-1. This justifies the boundary F=L^t. Empty products and label-zero unit factors are separately handled.

The signed anchor argument does not presuppose the sign of the global CRT index C. The cap gives |Ycap|>|C|; squared ordinate divisibility and comparison congruences recover the classified index |C| and exclude C=0. Bounding all remaining classified indices then precedes orientation. At a negative Pell center the correct abscissa need not be positive; the retained orientation formula handles the parity signs.

The completeness order proof,t,K,F,y,x,B,N,other representatives,C,H,q,frame,Pell center is acyclic. Since B and hence N squared are odd, C's prescribed residue class contains arbitrarily large even representatives. Enlarging C occurs before H and q are constructed. No earlier modulus depends on C. The cap's odd auxiliary quotient is supplied by the even anchor index and the composition expansion modulo the anchor ordinate squared.

The beta endpoint case y=F is genuinely excluded: its starting residue is zero; a selected row with positive weights propagates zero; the last residue is one. Hence multiplying and cancelling positive states is valid. The single-conclusion Horn closure counting argument handles cyclic rule multisets.

No substantive gap was found in these new source arguments on this review.

## Scope

The unbounded signed Pell classification and comparison-index lemmas, generalized binomial CRT lemma, and C222/ZF/ZFC calibration remain inherited theorems. The exact identified logical endpoints are `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their copied files contain proof terms, but the package is not the complete Lean dependency closure. This review did not build such a closure or independently reprove the seed-to-model calibration.

## Possible new intermediate frontier

One may replace K=t^4, t=128+4z^2 by K=c*t^2, t=h+4z^2, with h divisible by four and c*h>=2^20. This satisfies the same sufficient bound K>=2^20*t and keeps the horizon cofinal. It needs one quadratic growth wire instead of two and can reduce the large coefficients of the affine-index 214-variable companion. For example c=h=1024 works. This is a proposed implementation tradeoff, not an achieved new endpoint until the complete compiler and certificates have run.

Naively deleting the C range-binomial is unsound: B divides C+F+1 pins C only modulo the selector p^e, whereas local decoding needs its lift modulo p^(ex). The range binomial provides that lift and cannot be omitted on the basis of the raw index row alone.
